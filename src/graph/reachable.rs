use std::hash::Hash;

use rustc_hash::FxHashSet;

use crate::graph::{DirectedGraph, Graph};

pub fn reachable<N: Eq + Hash + Copy, G: Graph + DirectedGraph<Node = N>>(
    data: &G,
    entry: &[N],
) -> FxHashSet<N> {
    let mut reachable = FxHashSet::default();
    reachable.reserve(data.num_nodes());
    let mut worklist = Vec::with_capacity(data.num_nodes() / 2 + 1);
    worklist.extend(entry);
    while let Some(bb) = worklist.pop() {
        if !reachable.insert(bb) {
            continue;
        }

        worklist.extend(data.succs(bb));
    }

    reachable
}
