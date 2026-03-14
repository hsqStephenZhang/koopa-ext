use std::collections::HashMap;

use koopa::ir::builder::ValueBuilder;
use koopa::ir::dfg::DataFlowGraph;
use koopa::ir::entities::ValueData;
use koopa::ir::{BasicBlock, FunctionData, Value, ValueKind};

use crate::graph::loops::{Loop, LoopsAnalysis};

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
