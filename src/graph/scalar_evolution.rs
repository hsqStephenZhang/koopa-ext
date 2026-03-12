use koopa::ir::values::{Integer, ZeroInit};
use koopa::ir::{BinaryOp, Value, ValueKind};

use crate::graph::loops::Loop;

pub enum ConstantKind {
    Integer(Integer),
    ZeroInit(ZeroInit),
}

impl TryFrom<ValueKind> for ConstantKind {
    type Error = ();

    fn try_from(value: ValueKind) -> Result<Self, Self::Error> {
        match value {
            ValueKind::Integer(integer) => Ok(Self::Integer(integer)),
            ValueKind::ZeroInit(zero_init) => Ok(Self::ZeroInit(zero_init)),
            _ => Err(()),
        }
    }
}

pub enum SCEVBase {
    /// a constant
    Constant(ConstantKind),
    /// unknown value outside of the loop
    Unknown(Value),
}

pub enum SCEV {
    /// atomic value
    Base(SCEVBase),
    /// a start value add by and loop Invaraint
    AddRec(AddRec),
    /// n-ary expression
    NAry { vec: Vec<Box<SCEV>>, op: BinaryOp },
}

pub struct AddRec {
    /// base of the value
    base: Value,
    /// loop invariant
    step: Value,
    /// loop id
    lp: Loop,
}

impl AddRec {
    fn new(base: Value, step: Value, lp: Loop) -> Self {
        Self { base, step, lp }
    }
}

pub struct ScalarEvolutionAnalysis {}

impl ScalarEvolutionAnalysis {
    pub fn compute(&mut self) {
        todo!()
    }
}
