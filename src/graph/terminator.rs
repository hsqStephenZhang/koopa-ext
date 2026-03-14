use koopa::ir::entities::ValueData;
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

impl TerminatorKind {
    pub fn params(&self, target: BasicBlock) -> Option<Vec<Value>> {
        let mut res = vec![];
        match self {
            TerminatorKind::Branch(branch) => {
                assert!(branch.true_bb() == target || branch.false_bb() == target);
                if branch.true_bb() == target {
                    res.extend(branch.true_args());
                } else {
                    res.extend(branch.false_args());
                }
            }
            TerminatorKind::Jump(jump) => {
                assert!(jump.target() == target);
                res.extend(jump.args());
            }
            TerminatorKind::Return(_) => return None,
        }
        Some(res)
    }
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

    fn terminator_raw(&self, bb: BasicBlock) -> (Value, ValueData);
}

impl TerminatorExt for FunctionData {
    fn terminator(&self, bb: BasicBlock) -> (Value, TerminatorKind) {
        let bb_node = self.layout().bbs().node(&bb).unwrap();
        let value = *bb_node.insts().iter().last().unwrap().0;
        let data = TerminatorKind::try_from(self.dfg().value(value).kind().clone()).unwrap();
        (value, data)
    }

    fn terminator_raw(&self, bb: BasicBlock) -> (Value, ValueData) {
        let bb_node = self.layout().bbs().node(&bb).unwrap();
        let value = *bb_node.insts().iter().last().unwrap().0;
        let data = self.dfg().value(value).clone();
        assert!(matches!(
            data.kind(),
            ValueKind::Branch(_) | ValueKind::Jump(_) | ValueKind::Return(_)
        ));
        (value, data)
    }
}
