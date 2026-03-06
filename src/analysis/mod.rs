/// ∨ oepration to compute the least upper bound
/// of two elements in a partial order
pub trait JoinSemiLattice {
    /// compute the
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

impl<V> JoinSemiLattice for FlattenValue<V> {
    fn join(&mut self, other: Self) -> bool {
        match self {
            FlattenValue::Top => false,
            FlattenValue::Concrete(_) => {
                // if other is concret or top, the result of join must be Top
                let changed = !matches!(other, Self::Bottom);
                if changed {
                    *self = Self::Top;
                }
                changed
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

pub trait DataFlowAnalaysis {
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

// impl DataFlowAnalaysis for DeadcodeElimination {
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
