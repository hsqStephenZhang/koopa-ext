use koopa::ir::values::{Integer, ZeroInit};
use koopa::ir::{FunctionData, Value, ValueKind};

use crate::graph::dom_tree::DomTree;
use crate::graph::loops::LoopsAnalysis;

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

/// Errors produced when building SCEV expressions.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SCEVError {
    /// The expression combination is not supported.
    UnsupportedExpr,
}

pub enum SCEVExpr {
    /// a constant
    Constant(ConstantKind),
    /// loop invariant
    Invariant(Value),
    /// a start value add by and loop Invaraint
    AddRec(AffineAddRec),
}

impl SCEVExpr {
    pub fn add_expr(_lhs: SCEVExpr, _rhs: SCEVExpr) -> Result<Self, SCEVError> {
        Err(SCEVError::UnsupportedExpr)
    }

    pub fn mul_expr(_lhs: SCEVExpr, _rhs: SCEVExpr) -> Result<Self, SCEVError> {
        Err(SCEVError::UnsupportedExpr)
    }
}

pub struct AffineAddRec {
    /// base of the value
    pub base: Box<SCEVExpr>,
    /// must be constant or invariant
    pub step: Box<SCEVExpr>,
}

impl AffineAddRec {
    pub fn new(base: Box<SCEVExpr>, step: Box<SCEVExpr>) -> Self {
        Self { base, step }
    }
}

pub struct ScalarEvolutionAnalysis {}

impl ScalarEvolutionAnalysis {
    pub fn compute(&mut self, data: &FunctionData) {
        let entry = data.layout().entry_bb().unwrap();
        let dom_tree = DomTree::build(entry, data);
        let mut loops = LoopsAnalysis::new();
        loops.compute(data, entry, &dom_tree);

        for lp in loops.bottom_up() {
            let header = loops.loops()[&lp].header();
            let params = data.dfg().bb(header).params();
            // we wish to tell which BB param could be represented as an `AffineAddRec`
            for _param in params {}
        }
    }
}
