pub mod memory_ssa;
pub trait JoinSemiLattice {
    /// returns if self is changed
    fn join(&mut self, other: Self) -> bool;
}

pub trait MeetSemiLattice {
    /// returns if self is changed
    fn meet(&mut self, other: Self) -> bool;
}

/// The lattice looks like:
///      Top
/// v1 v2 ... vn
///     Bottom
#[derive(Debug, Clone, Copy, PartialEq, PartialOrd)]
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
                            *self = FlattenValue::Top;
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

impl<V: PartialEq> MeetSemiLattice for FlattenValue<V> {
    fn meet(&mut self, other: Self) -> bool {
        match (&*self, other) {
            (FlattenValue::Bottom, _) | (_, FlattenValue::Top) => false,

            (FlattenValue::Top, other_val) => {
                *self = other_val;
                true
            }

            (FlattenValue::Concrete(v1), other_val) => match other_val {
                FlattenValue::Top => false,
                FlattenValue::Bottom => {
                    *self = FlattenValue::Bottom;
                    true
                }
                FlattenValue::Concrete(v2) => {
                    if *v1 == v2 {
                        false
                    } else {
                        *self = FlattenValue::Bottom;
                        true
                    }
                }
            },
        }
    }
}
