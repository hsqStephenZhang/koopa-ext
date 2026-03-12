use koopa::ir::{BasicBlock, FunctionData, Value, ValueKind, values};

/// The kind of a terminator instruction.
pub enum TerminatorKind {
    /// Conditional branch.
    Branch(values::Branch),
    /// Unconditional jump.
    Jump(values::Jump),
    /// Function return.
    Return(values::Return),
}

impl TryFrom<ValueKind> for TerminatorKind {
    type Error = ();

    fn try_from(value: ValueKind) -> Result<Self, Self::Error> {
        let res = match value {
            ValueKind::Branch(branch) => Self::Branch(branch),
            ValueKind::Jump(jump) => Self::Jump(jump),
            ValueKind::Return(ret) => Self::Return(ret),
            _ => return Err(()),
        };
        Ok(res)
    }
}

pub trait TerminatorExt {
    fn terminator(&self, bb: BasicBlock) -> (Value, TerminatorKind);
}

impl TerminatorExt for FunctionData {
    fn terminator(&self, bb: BasicBlock) -> (Value, TerminatorKind) {
        let bb_node = self.layout().bbs().node(&bb).unwrap();
        let value = *bb_node.insts().iter().last().unwrap().0;
        let data = TerminatorKind::try_from(self.dfg().value(value).kind().clone()).unwrap();
        (value, data)
    }
}
