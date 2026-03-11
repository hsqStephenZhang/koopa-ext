/// ∨ operation to compute the least upper bound
/// of two elements in a partial order
pub trait JoinSemiLattice {
    /// returns if self is changed
    fn join(&mut self, other: Self) -> bool;
}

/// The lattice looks like:
///      Top
/// v1 v2 ... vn
///     Bottom
#[derive(Debug, Clone, PartialEq, PartialOrd)]
pub enum FlattenValue<V> {
    Top,
    Concrete(V),
    Bottom,
}

impl<V> FlattenValue<V> {
    pub fn get(&self) -> Option<&V> {
        if let Self::Concrete(v) = self { Some(v) } else { None }
    }
}

impl<V: PartialEq> JoinSemiLattice for FlattenValue<V> {
    fn join(&mut self, other: Self) -> bool {
        match self {
            FlattenValue::Top => false,
            FlattenValue::Concrete(v1) => {
                // if other is concert or top, the result of join must be Top
                match other {
                    FlattenValue::Top => {
                        *self = FlattenValue::Top;
                        true
                    }
                    FlattenValue::Concrete(v2) => {
                        if *v1 == v2 {
                            false
                        } else {
                            *v1 = v2;
                            true
                        }
                    }
                    FlattenValue::Bottom => false,
                }
            }
            FlattenValue::Bottom => {
                // if other is not bottom, then we must change
                let changed = !matches!(other, Self::Bottom);
                if changed {
                    *self = other;
                }
                changed
            }
        }
    }
}

pub trait Direction {}

pub struct Forward;

impl Direction for Forward {}

pub struct Backward;

pub trait DataFlowAnalysis {
    type Direction: Direction;

    type Domain: JoinSemiLattice;

    /// bottom value for worklist algorithm
    fn bottom_value(&self) -> Self::Domain;

    /// actual runner of worklist algorithm
    fn run_analysis(func: &koopa::ir::FunctionData);

    /// will be invoked after the analysis
    fn apply_effects(func: &mut koopa::ir::FunctionData);
}

pub struct DeadcodeElimination {}

// impl DataFlowAnalysis for DeadcodeElimination {
//     type Direction;

//     type Domain;

//     fn bottom_value(&self) -> Self::Domain {
//         todo!()
//     }

//     fn run_analysis(func: &koopa::ir::FunctionData) {
//         todo!()
//     }

//     fn apply_effects(func: &mut koopa::ir::FunctionData) {
//         todo!()
//     }
// }

pub mod constant_fold;
