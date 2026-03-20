use koopa::ir::builder::ValueBuilder;
use koopa::ir::{BasicBlock, FunctionData, Type, Value, ValueKind};
use rustc_hash::FxHashMap;

use crate::graph::DirectedGraph;

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
}

impl FunctionDataExt for FunctionData {
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
}
