use std::collections::HashMap;

use koopa::ir::Value;
use koopa::ir::builder::ValueBuilder;
use koopa::ir::dfg::DataFlowGraph;
use koopa::ir::entities::ValueData;

/// unlink the inst and safely remove it from the
pub fn safely_remove_inst_from_dfg(dfg: &mut DataFlowGraph, value: Value) {
    let ty = dfg.value(value).ty().clone();
    dfg.replace_value_with(value).undef(ty);
    dfg.remove_value(value);
}

/// replace operands in the `ValueData` by the provided `v_map`
/// returns if it's changed
pub fn replace_operands(data: &mut ValueData, v_map: &HashMap<Value, Value>) -> bool {
    let mut changed = false;
    let mut replace = |old: &mut Value| {
        if let Some(new) = v_map.get(old) {
            *old = *new;
            changed = true;
        }
    };
    match data.kind_mut() {
        koopa::ir::ValueKind::Load(load) => replace(load.src_mut()),
        koopa::ir::ValueKind::Store(store) => {
            replace(store.dest_mut());
            replace(store.value_mut());
        }
        koopa::ir::ValueKind::GetPtr(get_ptr) => {
            replace(get_ptr.index_mut());
            replace(get_ptr.src_mut());
        }
        koopa::ir::ValueKind::GetElemPtr(get_elem_ptr) => {
            replace(get_elem_ptr.index_mut());
            replace(get_elem_ptr.src_mut());
        }
        koopa::ir::ValueKind::Binary(binary) => {
            replace(binary.lhs_mut());
            replace(binary.rhs_mut());
        }
        koopa::ir::ValueKind::Branch(branch) => {
            replace(branch.cond_mut());
            for arg in branch.true_args_mut() {
                replace(arg);
            }
            for arg in branch.false_args_mut() {
                replace(arg);
            }
        }
        koopa::ir::ValueKind::Jump(jump) => {
            for arg in jump.args_mut() {
                replace(arg);
            }
        }
        koopa::ir::ValueKind::Call(call) => {
            for arg in call.args_mut() {
                replace(arg);
            }
        }
        koopa::ir::ValueKind::Return(ret) => {
            if let Some(ret) = ret.value_mut() {
                replace(ret);
            }
        }
        _ => {}
    }

    changed
}
