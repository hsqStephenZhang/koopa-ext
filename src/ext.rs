use koopa::ir::builder::{LocalInstBuilder, ValueBuilder};
use koopa::ir::{BasicBlock, FunctionData, Type, Value, ValueKind};
use rustc_hash::{FxHashMap, FxHashSet};

use crate::dbg::{BasicBlockWrapper, ValueKindDisplay};
use crate::graph::DirectedGraph;
use crate::utils::replace_operands;

pub trait FunctionDataExt {
    fn get_value_by_name(&self, name: &str) -> Option<Value>;

    fn get_bb_by_name(&self, name: &str) -> Option<BasicBlock>;

    fn insts(&self, bb: BasicBlock) -> Vec<Value>;

    fn inst_count(&self) -> usize;

    fn bbs_owned(&self) -> Vec<BasicBlock>;

    fn try_eval_i32(&self, value: Value) -> Option<i32>;

    fn bb_of_arg(&self, arg: Value) -> Option<BasicBlock>;

    fn has(&self, value: Value) -> bool;

    fn bb_params_name_tys(&self, bb: BasicBlock) -> Vec<(Option<String>, Type)>;

    fn replace_all_uses_with(&mut self, old: Value, new: Value);

    /// remove basic block and all its params, instructions
    /// will replace all usages of the instructions with `undef`
    fn remove_bb_insts(&mut self, bb: BasicBlock);

    /// Debug for `koopa::ir::BasicBlock`
    fn dbg_bb(&self, bb: BasicBlock) -> impl std::fmt::Display;

    /// Debug for `koopa::ir::Value`
    fn dbg_value(&self, value: Value) -> impl std::fmt::Display;
}

impl FunctionDataExt for FunctionData {
    fn dbg_bb(&self, bb: BasicBlock) -> impl std::fmt::Display {
        BasicBlockWrapper::new(bb, self.dfg())
    }

    fn dbg_value(&self, value: Value) -> impl std::fmt::Display {
        ValueKindDisplay::new(self.dfg(), value)
    }

    fn get_value_by_name(&self, name: &str) -> Option<Value> {
        self.dfg().values().iter().find(|(_, v)| v.name().as_deref() == Some(name)).map(|(k, _)| *k)
    }

    fn get_bb_by_name(&self, name: &str) -> Option<BasicBlock> {
        self.dfg().bbs().iter().find(|(_, v)| v.name().as_deref() == Some(name)).map(|(k, _)| *k)
    }

    fn inst_count(&self) -> usize {
        let mut cnt = 0;

        for (bb, _) in self.layout().bbs() {
            cnt += self.layout().bbs().node(bb).unwrap().insts().len();
        }

        cnt
    }

    fn insts(&self, bb: BasicBlock) -> Vec<Value> {
        self.layout().bbs().node(&bb).unwrap().insts().keys().copied().collect::<Vec<_>>()
    }

    fn bbs_owned(&self) -> Vec<BasicBlock> {
        self.nodes_iter().collect()
    }

    fn try_eval_i32(&self, value: Value) -> Option<i32> {
        match self.dfg().values().get(&value)?.kind() {
            ValueKind::Integer(integer) => Some(integer.value()),
            ValueKind::ZeroInit(_) => Some(0),
            _ => None,
        }
    }

    fn bb_of_arg(&self, arg: Value) -> Option<BasicBlock> {
        for bb in self.layout().bbs().keys() {
            for param in self.dfg().bb(*bb).params() {
                if *param == arg {
                    return Some(*bb);
                }
            }
        }
        None
    }

    fn has(&self, value: Value) -> bool {
        self.dfg().values().get(&value).is_some()
    }

    fn bb_params_name_tys(&self, bb: BasicBlock) -> Vec<(Option<String>, Type)> {
        self.dfg()
            .bb(bb)
            .params()
            .into_iter()
            .map(|p| {
                let v = self.dfg().value(*p);
                (v.name().clone(), v.ty().clone())
            })
            .collect()
    }

    fn replace_all_uses_with(&mut self, old: Value, new: Value) {
        if !self.dfg().values().contains_key(&old) {
            return;
        }
        let usages = self.dfg().value(old).used_by().clone();

        let mut v_map = FxHashMap::default();
        v_map.insert(old, new);

        for usage in usages {
            let mut value_data = self.dfg().value(usage).clone();
            if crate::utils::replace_operands(&mut value_data, &v_map) {
                self.dfg_mut().replace_value_with(usage).raw(value_data);
            }
        }
    }

    fn remove_bb_insts(&mut self, bb: BasicBlock) {
        // instructions + bb params
        let mut removed_values: FxHashMap<Value, Value> = FxHashMap::default();

        let params = self.dfg().bb(bb).params().iter().copied().collect::<FxHashSet<_>>();
        if let Some((_, node)) = self.layout_mut().bbs_mut().remove(&bb) {
            for &inst in node.insts().keys() {
                let ty = self.dfg().value(inst).ty().clone();
                if !ty.is_unit() {
                    let undef = self.dfg_mut().new_value().undef(ty);
                    removed_values.insert(inst, undef);
                }
            }
        }

        for &param in &params {
            let ty = self.dfg().value(param).ty().clone();
            if !ty.is_unit() {
                let undef = self.dfg_mut().new_value().undef(ty);
                removed_values.insert(param, undef);
            }
        }

        for &value in removed_values.keys() {
            for usage in self.dfg().value(value).used_by().clone() {
                let mut value_kind = self.dfg().value(usage).clone();
                assert!(replace_operands(&mut value_kind, &removed_values));
                self.dfg_mut().replace_value_with(usage).raw(value_kind);
            }
            assert!(self.dfg().value(value).used_by().is_empty());
        }

        // for params, we need only replace them with undef
        // the removal will be done within `dfg_mut().remove_bb(bb)`
        for &inst in removed_values.keys().filter(|inst| !params.contains(inst)) {
            self.dfg_mut().remove_value(inst);
        }

        let usages = self.dfg().bb(bb).used_by().clone();

        for terminator in usages {
            match self.dfg().value(terminator).kind() {
                ValueKind::Branch(branch) => {
                    let (target, args) = if branch.true_bb() == bb {
                        (branch.false_bb(), branch.false_args().to_vec())
                    } else {
                        (branch.true_bb(), branch.true_args().to_vec())
                    };
                    self.dfg_mut().replace_value_with(terminator).jump_with_args(target, args);
                }
                ValueKind::Jump(_) => {
                    // if `bb` is unreachable, **then the user bbs are also unreachable**
                    // **so we could replace the terminator with any instruction we like**
                    // we chose to replace with an `ret %undef_value` or simpliy an empty `ret`
                    // because the usage/reference of current `bb` will hinder us from
                    // removing them because koopa will check the usage before actually
                    // deleting any Value
                    let ret_ty = self.ty().clone();
                    let value = if ret_ty.is_unit() {
                        None
                    } else {
                        Some(self.dfg_mut().new_value().undef(ret_ty))
                    };
                    self.dfg_mut().replace_value_with(terminator).ret(value);
                }
                _ => {}
            }
        }
        self.dfg_mut().remove_bb(bb);
    }
}
