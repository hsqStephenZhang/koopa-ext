use koopa::ir::{BasicBlock, FunctionData, Value, ValueKind, values};

/// The kind of a terminator instruction.
pub enum TerminatorKind {
    /// Conditional branch.
    Branch(values::Branch),
    /// Unconditional jump.
    Jump(values::Jump),
    /// Function call.
    Call(values::Call),
    /// Function return.
    Return(values::Return),
}

impl From<ValueKind> for TerminatorKind {
    fn from(value: ValueKind) -> Self {
        TerminatorKind::try_from(value).unwrap()
    }
}

pub trait TerminatorExt {
    fn terminator(&self, bb: BasicBlock) -> (Value, TerminatorKind);
}

impl TerminatorExt for FunctionData {
    fn terminator(&self, bb: BasicBlock) -> (Value, TerminatorKind) {
        let bb_node = self.layout().bbs().node(&bb).unwrap();
        let value = bb_node.insts().iter().last().unwrap().0.clone();
        let data = TerminatorKind::from(self.dfg().value(value).kind().clone());
        (value, data)
    }
}
