use std::collections::HashMap;

use koopa::ir::builder::{LocalInstBuilder, ValueBuilder};
use koopa::ir::dfg::DataFlowGraph;
use koopa::ir::entities::ValueData;
use koopa::ir::{BasicBlock, Function, FunctionData, Program, Type, Value, ValueKind};
use rustc_hash::FxHashMap;

use crate::graph::loops::{Loop, LoopsAnalysis};

pub trait FunctionDataExt {
    fn get_value_by_name(&self, name: &str) -> Option<Value>;

    fn get_bb_by_name(&self, name: &str) -> Option<BasicBlock>;
}

impl FunctionDataExt for FunctionData {
    fn get_value_by_name(&self, name: &str) -> Option<Value> {
        self.dfg().values().iter().find(|(_, v)| v.name().as_deref() == Some(name)).map(|(k, _)| *k)
    }

    fn get_bb_by_name(&self, name: &str) -> Option<BasicBlock> {
        self.dfg().bbs().iter().find(|(_, v)| v.name().as_deref() == Some(name)).map(|(k, _)| *k)
    }
}

/// unlink the inst and safely remove it from the
pub fn safely_remove_inst_from_dfg(dfg: &mut DataFlowGraph, value: Value) {
    let ty = dfg.value(value).ty().clone();
    if !ty.is_unit() {
        dfg.replace_value_with(value).undef(ty);
    }
    dfg.remove_value(value);
}

pub trait ValuesVisit {
    type Output;

    fn visit(&mut self, visitor: impl FnMut(&mut Value) -> Self::Output);
}

impl ValuesVisit for Vec<Value> {
    type Output = ();

    fn visit(&mut self, visitor: impl FnMut(&mut Value) -> Self::Output) {
        self.iter_mut().for_each(visitor);
    }
}

impl ValuesVisit for ValueData {
    type Output = ();

    fn visit(&mut self, mut visitor: impl FnMut(&mut Value) -> Self::Output) {
        match self.kind_mut() {
            koopa::ir::ValueKind::Load(load) => visitor(load.src_mut()),
            koopa::ir::ValueKind::Store(store) => {
                visitor(store.dest_mut());
                visitor(store.value_mut());
            }
            koopa::ir::ValueKind::GetPtr(get_ptr) => {
                visitor(get_ptr.index_mut());
                visitor(get_ptr.src_mut());
            }
            koopa::ir::ValueKind::GetElemPtr(get_elem_ptr) => {
                visitor(get_elem_ptr.index_mut());
                visitor(get_elem_ptr.src_mut());
            }
            koopa::ir::ValueKind::Binary(binary) => {
                visitor(binary.lhs_mut());
                visitor(binary.rhs_mut());
            }
            koopa::ir::ValueKind::Branch(branch) => {
                visitor(branch.cond_mut());
                for arg in branch.true_args_mut() {
                    visitor(arg);
                }
                for arg in branch.false_args_mut() {
                    visitor(arg);
                }
            }
            koopa::ir::ValueKind::Jump(jump) => {
                for arg in jump.args_mut() {
                    visitor(arg);
                }
            }
            koopa::ir::ValueKind::Call(call) => {
                for arg in call.args_mut() {
                    visitor(arg);
                }
            }
            koopa::ir::ValueKind::Return(ret) => {
                if let Some(ret) = ret.value_mut() {
                    visitor(ret);
                }
            }
            _ => {}
        }
    }
}

/// replace operands in the `ValueData` by the provided `v_map`
/// returns if it's changed
pub fn replace_operands<V: ValuesVisit<Output = ()>>(
    data: &mut V,
    v_map: &HashMap<Value, Value>,
) -> bool {
    let mut changed = false;
    let replacer = |old: &mut Value| {
        if let Some(new) = v_map.get(old) {
            *old = *new;
            changed = true;
        }
    };
    data.visit(replacer);
    changed
}

/// returns if the `value` is a loop invariant
pub fn is_loop_invariant(
    data: &FunctionData,
    lp: Loop,
    loops: &LoopsAnalysis<BasicBlock>,
    value: Value,
) -> bool {
    match data.layout().parent_bb(value) {
        Some(bb) => !loops.contains(lp, bb),
        None => data
            .dfg()
            .values()
            .get(&value)
            .map(|data| matches!(data.kind(), ValueKind::FuncArgRef(_) | ValueKind::GlobalAlloc(_)))
            .unwrap_or_default(),
    }
}

/// clone a basic block, replace the operand used in the insts by the `vmap`
/// will update `vmap` with the old -> new instruction mapping
/// 
/// it will skip the instruction that is already contained in vmap,
/// so if you wish to handle some inst like `alloc` mannually,
/// you could insert the mapping before calling this function.
/// 
pub fn clone_bb(
    prog: &mut Program,
    from_func: Function,
    to_func: Function,
    vmap: &mut FxHashMap<Value, Value>,
    bb_map: &FxHashMap<BasicBlock, BasicBlock>,
    old_bb: BasicBlock,
    new_bb: BasicBlock,
    ret_target: Option<BasicBlock>,
) {
    let insts: Vec<_> = {
        let from_data = prog.func(from_func);
        let dfg = from_data.dfg();
        from_data
            .layout()
            .bbs()
            .node(&old_bb)
            .unwrap()
            .insts()
            .keys()
            .filter(|&i| !vmap.contains_key(i))
            .map(|&i| {
                let v = dfg.value(i);
                (i, v.ty().clone(), v.kind().clone())
            })
            .collect()
    };

    for (old_inst, ty, kind) in insts {
        let new_inst =
            clone_instruction(prog, from_func, to_func, vmap, bb_map, ret_target, &ty, &kind);
        prog.func_mut(to_func)
            .layout_mut()
            .bb_mut(new_bb)
            .insts_mut()
            .push_key_back(new_inst)
            .unwrap();
        vmap.insert(old_inst, new_inst);
    }
}

fn clone_operand(
    prog: &mut Program,
    from_func: Function,
    to_func: Function,
    vmap: &mut FxHashMap<Value, Value>,
    op: Value,
) -> Value {
    if let Some(&new_op) = vmap.get(&op) {
        return new_op;
    }

    let (ty, kind) = {
        let from_dfg = prog.func(from_func).dfg();
        if let Some(src_val) = from_dfg.values().get(&op) {
            if src_val.kind().is_const() {
                (src_val.ty().clone(), src_val.kind().clone())
            } else {
                return op;
            }
        } else {
            return op;
        }
    };

    let new_op = match kind {
        ValueKind::Integer(i) => prog.func_mut(to_func).dfg_mut().new_value().integer(i.value()),
        ValueKind::ZeroInit(_) => prog.func_mut(to_func).dfg_mut().new_value().zero_init(ty),
        ValueKind::Undef(_) => prog.func_mut(to_func).dfg_mut().new_value().undef(ty),
        ValueKind::Aggregate(agg) => {
            let elems = agg
                .elems()
                .iter()
                .map(|&e| clone_operand(prog, from_func, to_func, vmap, e))
                .collect();
            prog.func_mut(to_func).dfg_mut().new_value().aggregate(elems)
        }
        _ => unreachable!("Only constant values expected to be cloned here"),
    };
    vmap.insert(op, new_op);
    new_op
}

fn clone_instruction(
    prog: &mut Program,
    from_func: Function,
    to_func: Function,
    vmap: &mut FxHashMap<Value, Value>,
    bb_map: &FxHashMap<BasicBlock, BasicBlock>,
    ret_target: Option<BasicBlock>,
    ty: &Type,
    kind: &ValueKind,
) -> Value {
    match kind {
        ValueKind::Integer(i) => prog.func_mut(to_func).dfg_mut().new_value().integer(i.value()),
        ValueKind::ZeroInit(_) => {
            prog.func_mut(to_func).dfg_mut().new_value().zero_init(ty.clone())
        }
        ValueKind::Undef(_) => prog.func_mut(to_func).dfg_mut().new_value().undef(ty.clone()),
        ValueKind::Aggregate(agg) => {
            let elems = agg
                .elems()
                .iter()
                .map(|&v| clone_operand(prog, from_func, to_func, vmap, v))
                .collect::<Vec<_>>();
            prog.func_mut(to_func).dfg_mut().new_value().aggregate(elems)
        }
        ValueKind::Alloc(_) => prog.func_mut(to_func).dfg_mut().new_value().alloc(ty.clone()),
        ValueKind::Load(load) => {
            let src = clone_operand(prog, from_func, to_func, vmap, load.src());
            prog.func_mut(to_func).dfg_mut().new_value().load(src)
        }
        ValueKind::Store(store) => {
            let val = clone_operand(prog, from_func, to_func, vmap, store.value());
            let dest = clone_operand(prog, from_func, to_func, vmap, store.dest());
            dbg!(prog.func(to_func).dfg().value(val).ty());
            dbg!(prog.func(to_func).dfg().value(dest).ty());
            prog.func_mut(to_func).dfg_mut().new_value().store(val, dest)
        }
        ValueKind::GetPtr(get_ptr) => {
            let src = clone_operand(prog, from_func, to_func, vmap, get_ptr.src());
            let idx = clone_operand(prog, from_func, to_func, vmap, get_ptr.index());
            prog.func_mut(to_func).dfg_mut().new_value().get_ptr(src, idx)
        }
        ValueKind::GetElemPtr(get_elem_ptr) => {
            let src = clone_operand(prog, from_func, to_func, vmap, get_elem_ptr.src());
            let idx = clone_operand(prog, from_func, to_func, vmap, get_elem_ptr.index());
            prog.func_mut(to_func).dfg_mut().new_value().get_elem_ptr(src, idx)
        }
        ValueKind::Binary(bin) => {
            let lhs = clone_operand(prog, from_func, to_func, vmap, bin.lhs());
            let rhs = clone_operand(prog, from_func, to_func, vmap, bin.rhs());
            prog.func_mut(to_func).dfg_mut().new_value().binary(bin.op(), lhs, rhs)
        }
        ValueKind::Branch(br) => {
            let cond = clone_operand(prog, from_func, to_func, vmap, br.cond());
            let true_args = br
                .true_args()
                .iter()
                .map(|&v| clone_operand(prog, from_func, to_func, vmap, v))
                .collect::<Vec<_>>();
            let false_args = br
                .false_args()
                .iter()
                .map(|&v| clone_operand(prog, from_func, to_func, vmap, v))
                .collect::<Vec<_>>();
            let true_bb = *bb_map.get(&br.true_bb()).unwrap_or(&br.true_bb());
            let false_bb = *bb_map.get(&br.false_bb()).unwrap_or(&br.false_bb());

            prog.func_mut(to_func)
                .dfg_mut()
                .new_value()
                .branch_with_args(cond, true_bb, false_bb, true_args, false_args)
        }
        ValueKind::Jump(j) => {
            let args = j
                .args()
                .iter()
                .map(|&v| clone_operand(prog, from_func, to_func, vmap, v))
                .collect::<Vec<_>>();
            let tgt = *bb_map.get(&j.target()).unwrap_or(&j.target());
            prog.func_mut(to_func).dfg_mut().new_value().jump_with_args(tgt, args)
        }
        ValueKind::Call(call) => {
            let args = call
                .args()
                .iter()
                .map(|&v| clone_operand(prog, from_func, to_func, vmap, v))
                .collect::<Vec<_>>();
            prog.func_mut(to_func).dfg_mut().new_value().call(call.callee(), args)
        }
        ValueKind::Return(ret) => {
            if let Some(target) = ret_target {
                let mut jump_args = Vec::new();
                if let Some(rv) = ret.value() {
                    jump_args.push(clone_operand(prog, from_func, to_func, vmap, rv));
                }
                prog.func_mut(to_func).dfg_mut().new_value().jump_with_args(target, jump_args)
            } else {
                let rv = ret.value().map(|v| clone_operand(prog, from_func, to_func, vmap, v));
                prog.func_mut(to_func).dfg_mut().new_value().ret(rv)
            }
        }

        ValueKind::FuncArgRef(_) | ValueKind::BlockArgRef(_) | ValueKind::GlobalAlloc(_) => {
            unreachable!("unexpected non-local value in BB layout")
        }
    }
}

pub fn clone_instruction_in_same_func(
    data: &mut FunctionData,
    vmap: &mut FxHashMap<Value, Value>,
    value: Value,
) -> Value {
    if let Some(&new_val) = vmap.get(&value) {
        return new_val;
    }

    let (ty, kind) = {
        let v = data.dfg().value(value);
        (v.ty().clone(), v.kind().clone())
    };

    let mapped = |op: Value| -> Value { vmap.get(&op).copied().unwrap_or(op) };

    let new_val = match kind {
        ValueKind::Integer(i) => data.dfg_mut().new_value().integer(i.value()),
        ValueKind::ZeroInit(_) => data.dfg_mut().new_value().zero_init(ty),
        ValueKind::Undef(_) => data.dfg_mut().new_value().undef(ty),
        ValueKind::Aggregate(agg) => {
            let elems = agg.elems().iter().map(|&v| mapped(v)).collect();
            data.dfg_mut().new_value().aggregate(elems)
        }
        ValueKind::Alloc(_) => data.dfg_mut().new_value().alloc(ty),
        ValueKind::Load(load) => {
            let src = mapped(load.src());
            data.dfg_mut().new_value().load(src)
        }
        ValueKind::Store(store) => {
            let val = mapped(store.value());
            let dest = mapped(store.dest());
            data.dfg_mut().new_value().store(val, dest)
        }
        ValueKind::GetPtr(get_ptr) => {
            let src = mapped(get_ptr.src());
            let idx = mapped(get_ptr.index());
            data.dfg_mut().new_value().get_ptr(src, idx)
        }
        ValueKind::GetElemPtr(get_elem_ptr) => {
            let src = mapped(get_elem_ptr.src());
            let idx = mapped(get_elem_ptr.index());
            data.dfg_mut().new_value().get_elem_ptr(src, idx)
        }
        ValueKind::Binary(bin) => {
            let lhs = mapped(bin.lhs());
            let rhs = mapped(bin.rhs());
            data.dfg_mut().new_value().binary(bin.op(), lhs, rhs)
        }
        ValueKind::Branch(br) => {
            let cond = mapped(br.cond());
            let true_args = br.true_args().iter().map(|&v| mapped(v)).collect();
            let false_args = br.false_args().iter().map(|&v| mapped(v)).collect();
            data.dfg_mut().new_value().branch_with_args(
                cond,
                br.true_bb(), // Branch targets are kept as-is since there's no bb_map
                br.false_bb(),
                true_args,
                false_args,
            )
        }
        ValueKind::Jump(j) => {
            let args = j.args().iter().map(|&v| mapped(v)).collect();
            data.dfg_mut().new_value().jump_with_args(j.target(), args)
        }
        ValueKind::Call(call) => {
            let args = call.args().iter().map(|&v| mapped(v)).collect();
            data.dfg_mut().new_value().call(call.callee(), args)
        }
        ValueKind::Return(ret) => {
            let rv = ret.value().map(mapped);
            data.dfg_mut().new_value().ret(rv)
        }
        ValueKind::BlockArgRef(_) | ValueKind::FuncArgRef(_) | ValueKind::GlobalAlloc(_) => value,
    };

    vmap.insert(value, new_val);
    new_val
}
