use koopa::ir::{FunctionData, Type, Value};
fn test(data: &mut FunctionData) {
    let p = data.dfg_mut().new_value().integer(0);
}
