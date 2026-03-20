use std::collections::{HashMap, VecDeque};

use koopa::ir::builder::{LocalInstBuilder, ValueBuilder};
use koopa::ir::{BasicBlock, BinaryOp, Value, ValueKind};
use koopa::opt::FunctionPass;
use rustc_hash::{FxHashMap, FxHashSet};
use smallvec::SmallVec;

use crate::analysis::{FlattenValue, MeetSemiLattice};
use crate::ext::FunctionDataExt;
use crate::utils::replace_operands;

/// Specifically, this:
///   * Assumes values are constant unless proven otherwise
///   * Assumes BasicBlocks are dead unless proven otherwise
///   * Proves values to be constant, and replaces them with constants
///   * Proves conditional branches to be unconditional
#[derive(Default)]
pub struct SCCP {
    /// domain1
    executable_bbs: FxHashSet<BasicBlock>,

    /// domain2
    /// all values in this map should belong to `koopa::ir::FunctionData`
    /// FlattenValue::Top : unknown const
    /// FlattenValue::Concrete : known const
    /// FlattenValue::Bottom : not a constant
    values: FxHashMap<Value, FlattenValue<i32>>,

    /// worklist1
    bb_worklist: VecDeque<BasicBlock>,

    /// worklist2
    value_worklist: VecDeque<Value>,
}

impl FunctionPass for SCCP {
    fn run_on(&mut self, _func: koopa::ir::Function, data: &mut koopa::ir::FunctionData) {
        let Some(entry) = data.layout().entry_bb() else {
            return;
        };

        // init the state and worklist
        for param in data.params() {
            self.values.insert(*param, FlattenValue::Bottom);
        }
        self.executable_bbs.insert(entry);
        self.bb_worklist.push_back(entry);

        self.mark(data);
        self.sweep(data);
    }
}

impl SCCP {
    pub fn new() -> Self {
        Self::default()
    }

    fn mark(&mut self, data: &koopa::ir::FunctionData) {
        while !(self.bb_worklist.is_empty() && self.value_worklist.is_empty()) {
            while let Some(value) = self.value_worklist.pop_front() {
                self.handle_value(value, data);
            }

            while let Some(bb) = self.bb_worklist.pop_front() {
                for inst in data.layout().bbs().node(&bb).unwrap().insts().keys() {
                    self.handle_value(*inst, data);
                }
            }
        }
    }

    fn handle_value(&mut self, value: Value, data: &koopa::ir::FunctionData) {
        if !data.has(value) {
            return;
        }
        let new_value = match data.dfg().value(value).kind() {
            ValueKind::Integer(integer) => FlattenValue::Concrete(integer.value()),
            ValueKind::ZeroInit(_) => FlattenValue::Concrete(0),
            ValueKind::Undef(_) => FlattenValue::Bottom,
            // should be handled before hand
            ValueKind::FuncArgRef(_) => unreachable!(),
            ValueKind::BlockArgRef(_) => self.lattice_value(value, data),
            ValueKind::Alloc(_)
            | ValueKind::GlobalAlloc(_)
            | ValueKind::Aggregate(_)
            | ValueKind::Load(_)
            | ValueKind::GetPtr(_)
            | ValueKind::GetElemPtr(_) => FlattenValue::Bottom,
            ValueKind::Binary(binary) => {
                let lhs = self.lattice_value(binary.lhs(), data);
                let rhs = self.lattice_value(binary.rhs(), data);

                match (lhs, rhs) {
                    (FlattenValue::Concrete(l), FlattenValue::Concrete(r)) => {
                        let res = match binary.op() {
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
                        };
                        // will panic on UB(div/mod by 0)
                        FlattenValue::Concrete(res.unwrap())
                    }
                    (FlattenValue::Bottom, _) | (_, FlattenValue::Bottom) => FlattenValue::Bottom,
                    _ => FlattenValue::Top,
                }
            }
            ValueKind::Branch(branch) => {
                let cond = self.lattice_value(branch.cond(), data);
                match cond {
                    FlattenValue::Top => return,
                    FlattenValue::Concrete(v) => {
                        if v == 0 {
                            self.set_edge_executable(branch.false_args(), branch.false_bb(), data);
                        } else {
                            self.set_edge_executable(branch.true_args(), branch.true_bb(), data);
                        }
                    }
                    FlattenValue::Bottom => {
                        self.set_edge_executable(branch.false_args(), branch.false_bb(), data);
                        self.set_edge_executable(branch.true_args(), branch.true_bb(), data);
                    }
                }
                return;
            }
            ValueKind::Jump(jump) => {
                self.set_edge_executable(jump.args(), jump.target(), data);
                return;
            }
            ValueKind::Call(_) => FlattenValue::Bottom,
            ValueKind::Store(_) | ValueKind::Return(_) => return, // not a value
        };

        if self.update(value, new_value) {
            self.update_value_worklist(value, data);
        }
    }

    // update the executable_bbs, bb_worklist
    // re-evalute the BB params for the target BB
    fn set_edge_executable(
        &mut self,
        args: &[Value],
        target: BasicBlock,
        data: &koopa::ir::FunctionData,
    ) {
        if self.executable_bbs.insert(target) {
            self.bb_worklist.push_back(target);
        }

        for (&param, &arg) in data.dfg().bb(target).params().iter().zip(args) {
            let mut old = self.lattice_value(param, data);
            let arg = self.lattice_value(arg, data);
            if old.meet(arg) {
                self.values.insert(param, old);
                self.update_value_worklist(param, data);
            }
        }
    }

    fn update_value_worklist(&mut self, value: Value, data: &koopa::ir::FunctionData) {
        for &usage in data.dfg().value(value).used_by() {
            if let Some(parent_bb) = data.layout().parent_bb(usage)
                && self.executable_bbs.contains(&parent_bb)
            {
                self.value_worklist.push_back(usage);
            }
        }
    }

    fn lattice_value(&self, value: Value, data: &koopa::ir::FunctionData) -> FlattenValue<i32> {
        self.values.get(&value).cloned().unwrap_or_else(|| {
            if let Some(value_data) = data.dfg().values().get(&value)
                && matches!(value_data.kind(), ValueKind::Integer(_) | ValueKind::ZeroInit(_))
            {
                FlattenValue::Concrete(data.try_eval_i32(value).unwrap())
            } else {
                FlattenValue::Top
            }
        })
    }

    /// returns if the original value is not the same as the old one
    fn update(&mut self, value: Value, lattice_value: FlattenValue<i32>) -> bool {
        // by default it's Top
        self.values.entry(value).or_insert(FlattenValue::Top);
        let origin = self.values.insert(value, lattice_value).unwrap();
        origin != lattice_value
    }

    fn sweep(&self, data: &mut koopa::ir::FunctionData) {
        let mut v_map = FxHashMap::default();
        let mut block_args: HashMap<BasicBlock, SmallVec<[usize; 4]>, _> = FxHashMap::default();

        // fill the vmap and repalce values that belong to the Function
        for (&value, lat) in &self.values {
            // only handle local values
            if !data.has(value) {
                continue;
            }
            if let FlattenValue::Concrete(c) = lat {
                let new_value = data.dfg_mut().new_value().integer(*c);
                let kind = data.dfg().value(value).kind();
                if kind.is_local_inst() {
                    v_map.insert(value, new_value);
                } else if let ValueKind::BlockArgRef(arg_ref) = kind {
                    let bb = data.bb_of_arg(value).unwrap();
                    block_args.entry(bb).or_default().push(arg_ref.index());
                }
            }
        }

        for value in v_map.keys().copied() {
            if !data.has(value) {
                continue;
            }
            for usage in data.dfg().value(value).used_by().clone() {
                // should replace branch with jump
                if let ValueKind::Branch(branch) = data.dfg().value(usage).kind() {
                    let value = self.values.get(&value).unwrap().get().unwrap();
                    let (target, args) = if *value != 0 {
                        (branch.true_bb(), branch.true_args().to_vec())
                    } else {
                        (branch.false_bb(), branch.false_args().to_vec())
                    };
                    data.dfg_mut().replace_value_with(usage).jump_with_args(target, args);
                } else {
                    let mut value_kind = data.dfg().value(usage).clone();
                    assert!(replace_operands(&mut value_kind, &v_map));
                    data.dfg_mut().replace_value_with(usage).raw(value_kind);
                }
            }

            if let Some(parent_bb) = data.layout().parent_bb(value) {
                data.layout_mut().bb_mut(parent_bb).insts_mut().remove(&value);
            }
            data.dfg_mut().remove_value(value);
        }

        // simplify each bb params(phi node)
        for (bb, mut to_remove_indexes) in block_args {
            to_remove_indexes.sort();
            to_remove_indexes.dedup();
            // Remove params from the basic block
            for &idx in to_remove_indexes.iter().rev() {
                let old = data.dfg_mut().bb_mut(bb).params_mut().remove(idx);
                let new = data
                    .dfg_mut()
                    .new_value()
                    .integer(*self.values.get(&old).unwrap().get().unwrap());

                let v_map = FxHashMap::from_iter([(old, new)]);

                for usage in data.dfg().value(old).used_by().clone() {
                    let mut value_kind = data.dfg().value(usage).clone();
                    assert!(replace_operands(&mut value_kind, &v_map));
                    data.dfg_mut().replace_value_with(usage).raw(value_kind);
                }
            }

            let terminators = data.dfg().bb(bb).used_by().clone();
            for terminator in terminators {
                let kind = data.dfg().value(terminator).kind().clone();
                match kind {
                    ValueKind::Branch(branch) => {
                        let mut t_args = branch.true_args().to_vec();
                        let mut f_args = branch.false_args().to_vec();

                        if branch.true_bb() == bb {
                            for &idx in to_remove_indexes.iter().rev() {
                                t_args.remove(idx);
                            }
                        }
                        if branch.false_bb() == bb {
                            for &idx in to_remove_indexes.iter().rev() {
                                f_args.remove(idx);
                            }
                        }
                        data.dfg_mut().replace_value_with(terminator).branch_with_args(
                            branch.cond(),
                            branch.true_bb(),
                            branch.false_bb(),
                            t_args,
                            f_args,
                        );
                    }
                    ValueKind::Jump(jump) => {
                        let mut args = jump.args().to_vec();
                        for &idx in to_remove_indexes.iter().rev() {
                            args.remove(idx);
                        }
                        data.dfg_mut()
                            .replace_value_with(terminator)
                            .jump_with_args(jump.target(), args);
                    }
                    _ => {}
                }
            }
        }

        // Remove unreachable BBs based on SCCP executable_edges analysis
        // should handle both BBs and Instructions
        let unreachable_bbs = data
            .layout_mut()
            .bbs()
            .keys()
            .filter(|bb| !self.executable_bbs.contains(bb))
            .copied()
            .collect::<Vec<_>>();

        for bb in unreachable_bbs {
            data.remove_bb_insts(bb);
        }
    }
}

#[cfg(test)]
mod tests {
    use koopa::back::koopa::Visitor as KoopaVisitor;
    use koopa::back::{NameManager, Visitor};
    use koopa::front::Driver;

    use super::*;

    fn apply_pass(ir_text: &str, debug_on: bool) {
        let driver = Driver::from(ir_text);
        let mut program = driver.generate_program().unwrap();
        let func_id = *program.funcs().keys().next().unwrap();
        let func_data = program.func_mut(func_id);
        let mut pass = SCCP::new();
        pass.run_on(func_id, func_data);

        if debug_on {
            let mut visitor = KoopaVisitor;
            let mut nm = NameManager::new();
            let mut w = std::io::stdout();
            visitor.visit(&mut w, &mut nm, &program).unwrap();
        }
    }

    #[test]
    fn test_sccp_simple() {
        let ir = r#"
fun @local(): i32 {
%entry:
    %0 = add 1, 1
    %1 = mul %0, 2
    %2 = mul %0, 8
    %3 = mul %1, %2
    %4 = shl %3, 5
    ret %4
}
        "#;

        apply_pass(ir, true);
    }

    #[test]
    fn test_sccp_branch() {
        let ir = r#"
fun @branch_test(): i32 {
%entry:
    %cond = eq 1, 1  // true
    br %cond, %then, %else

%then:
    jump %end(10)

%else:
    jump %end(20)

%end(%res: i32):
    ret %res
}
    "#;
        apply_pass(ir, true);
    }

    #[test]
    fn test_sccp_phi_merge() {
        let ir = r#"
fun @merge_test(%input: i32): i32 {
%entry:
    %cond = gt %input, 0
    br %cond, %path_a, %path_b

%path_a:
    jump %end(100)

%path_b:
    jump %end(100)

%end(%res: i32):
    %final = add %res, 1
    ret %final
}
    "#;
        apply_pass(ir, true);
    }

    #[test]
    fn test_sccp_complex_call() {
        let ir = r#"
fun @sccp_loop_test(): i32 {
%entry:
    jump %loop(0)

%loop(%i: i32):
    %cond = lt %i, 1
    br %cond, %body, %exit(1)

%body:
    jump %exit(123)

%exit(%res: i32):
    ret %res
}
        "#;
        apply_pass(ir, true);
    }
}
