use std::collections::{HashMap, VecDeque};

use koopa::ir::builder_traits::*;
use koopa::ir::{BinaryOp, Function, FunctionData, Type, Value, ValueKind};
use koopa::opt::FunctionPass;

use crate::analysis::FlattenValue;

struct ConstantState {
    inner: HashMap<Value, FlattenValue<ValueKind>>,
}

impl ConstantState {
    pub fn get(&self, value: Value) -> &FlattenValue<ValueKind> {
        self.inner.get(&value).unwrap_or(&FlattenValue::Bottom)
    }
}

trait IRType {
    fn get_type() -> Type;
}

impl IRType for i32 {
    fn get_type() -> Type {
        Type::get_i32()
    }
}

pub trait EvalConst<O> {
    type Value;

    fn eval(&self, value: Self::Value) -> Option<O>;
}

impl EvalConst<i32> for HashMap<Value, FlattenValue<ValueKind>> {
    type Value = koopa::ir::Value;

    fn eval(&self, value: Self::Value) -> Option<i32> {
        let value_data = self.get(&value)?.get()?;
        let val = match value_data {
            ValueKind::Integer(val) => val.value(),
            ValueKind::ZeroInit(_) => 0,
            _ => return None,
        };
        Some(val)
    }
}

impl<T> EvalConst<Vec<T>> for HashMap<Value, FlattenValue<ValueKind>>
where
    Self: EvalConst<T, Value = koopa::ir::Value>,
{
    type Value = koopa::ir::Value;

    fn eval(&self, value: Self::Value) -> Option<Vec<T>> {
        let value_data = self.get(&value)?.get()?;

        let mut res = vec![];

        match value_data {
            ValueKind::Aggregate(agg) => {
                for val in agg.elems() {
                    let val = self.eval(*val)?;
                    res.push(val);
                }
            }
            _ => return None,
        };
        Some(res)
    }
}

/// Performs constant folding.
pub struct ConstantFolding;

impl FunctionPass for ConstantFolding {
    fn run_on(&mut self, _: Function, data: &mut FunctionData) {
        self.eval_const(data);
        // handle all basic block parameters
        self.eval_bb_params(data);
    }
}

impl Default for ConstantFolding {
    fn default() -> Self {
        Self::new()
    }
}

impl ConstantFolding {
    pub fn new() -> Self {
        Self
    }

    fn eval_const(&self, data: &mut FunctionData) {
        // find all evaluable binary instructions and evaluate
        let mut states: HashMap<Value, FlattenValue<ValueKind>> =
            HashMap::with_capacity(data.dfg().values().len());
        for &v in data.dfg().values().keys() {
            states.insert(v, FlattenValue::Bottom);
        }

        let mut worklist: VecDeque<Value> = VecDeque::new();
        while !worklist.is_empty() {
            let cur = worklist.pop_front().unwrap();
            let value_data = data.dfg().value(cur);
            // let old_state = states.get(&cur).unwrap();
            let old_value: Option<i32> = states.eval(cur);

            let new_value = match value_data.kind() {
                ValueKind::Binary(bin) => {
                    let v1: Option<i32> = states.eval(bin.lhs());
                    let v2: Option<i32> = states.eval(bin.rhs());
                    match (v1, v2) {
                        (Some(l), Some(r)) => match bin.op() {
                            BinaryOp::NotEq => Some((l != r) as i32),
                            BinaryOp::Eq => Some((l == r) as i32),
                            BinaryOp::Gt => Some((l > r) as i32),
                            BinaryOp::Lt => Some((l < r) as i32),
                            BinaryOp::Ge => Some((l >= r) as i32),
                            BinaryOp::Le => Some((l <= r) as i32),
                            BinaryOp::Add => Some(l + r),
                            BinaryOp::Sub => Some(l - r),
                            BinaryOp::Mul => Some(l * r),
                            BinaryOp::Div => (r != 0).then(|| l / r),
                            BinaryOp::Mod => (r != 0).then(|| l % r),
                            BinaryOp::And => Some(l & r),
                            BinaryOp::Or => Some(l | r),
                            BinaryOp::Xor => Some(l ^ r),
                            BinaryOp::Shl => Some(l << r),
                            BinaryOp::Shr => Some((l as u32 >> r) as i32),
                            BinaryOp::Sar => Some(l >> r),
                        },
                        _ => None,
                    }
                }
                _ => None,
            };

            if new_value.is_some() && old_value != new_value {
                let bb = data.layout().parent_bb(cur).unwrap();
                data.layout_mut().bb_mut(bb).insts_mut().remove(&cur);
                // TODO: distinguish different None value
                data.dfg_mut().replace_value_with(cur).integer(new_value.unwrap());
                for inst in data.dfg().value(cur).used_by() {
                    worklist.push_back(*inst);
                }
            }
        }
    }

    fn eval_bb_params(&self, data: &mut FunctionData) {
        let mut bb_params = Vec::new();
        for (b, bb) in data.dfg().bbs() {
            // collect parameters that can be evaluated in the current basic block
            let mut evaluated = Vec::new();
            'outer: for i in 0..bb.params().len() {
                let mut ans = None;
                // check if all corresponding arguments are constant
                for user in bb.used_by() {
                    // get the argument value handle
                    let value = match data.dfg().value(*user).kind() {
                        ValueKind::Branch(branch) => {
                            if branch.true_bb() == *b {
                                branch.true_args()[i]
                            } else {
                                branch.false_args()[i]
                            }
                        }
                        ValueKind::Jump(jump) => jump.args()[i],
                        _ => panic!("invalid branch/jump instruction"),
                    };
                    // check if is constant
                    let value = data.dfg().value(value);
                    if !value.kind().is_const()
                        || !ans.is_none_or(|v| data.dfg().data_eq(&v, value))
                    {
                        continue 'outer;
                    }
                    ans = Some(value.clone());
                }
                evaluated.push((i, ans.unwrap()));
            }
            if !evaluated.is_empty() {
                bb_params.push((*b, evaluated));
            }
        }
        // update basic block parameters
        for (bb, evals) in bb_params {
            // replace all parameters to constants
            for (i, value) in evals {
                let p = data.dfg().bb(bb).params()[i];
                let param = data.dfg().value(p).clone();
                data.dfg_mut().replace_value_with(p).raw(value);
                let p = data.dfg_mut().new_value().raw(param);
                data.dfg_mut().bb_mut(bb).params_mut()[i] = p;
            }
        }
    }
}
