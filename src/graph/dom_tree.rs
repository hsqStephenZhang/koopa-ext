use std::collections::HashMap;
use std::hash::Hash;

use indexmap::IndexMap;

use crate::graph::graph::{DirectedGraph, Graph};
use crate::graph::traverse::reverse_post_order;

pub struct DomTree<N> {
    idoms: IndexMap<N, N>,
}

impl<N: PartialEq + Eq + Hash + Copy> DomTree<N> {
    /// Cooper-Harvey-Kennedy algorithm
    /// we need:
    ///     1. entry node
    ///     2. reverse post ordering of BBs
    pub fn build<G: DirectedGraph<Node = N> + Graph>(entry_node: N, graph: &G) -> Self {
        let rpo = reverse_post_order(graph, entry_node);
        let bb_to_rpo =
            rpo.iter().enumerate().map(|(num, bb)| (*bb, num)).collect::<HashMap<_, _>>();
        let mut idoms = IndexMap::with_capacity(graph.num_nodes());

        idoms.insert(entry_node, entry_node);

        let mut changed = true;

        while changed {
            changed = false;

            // dom(bb) is the intersection of doms(pred) forall pred ∈ preds(bb)
            // idom(bb) is the neartest common ancester of pred forall pred ∈ preds(bb)
            for bb in rpo.iter().filter(|&&bb| bb != entry_node) {
                let old_idom = idoms.get(bb).cloned();
                let mut new_idom = None;

                for pred in graph.preds(*bb) {
                    match (new_idom, idoms.get(&pred)) {
                        (Some(pred1), Some(_)) => {
                            new_idom =
                                Some(nearest_common_ancester(pred1, pred, &bb_to_rpo, &idoms));
                        }
                        (None, Some(_)) => {
                            new_idom = Some(pred);
                        }
                        _ => {}
                    }
                }

                if old_idom != new_idom {
                    // new idom must be Some if it has changed
                    idoms.insert(*bb, new_idom.unwrap());
                    changed = true;
                }
            }
        }

        Self { idoms }
    }

    pub fn dominates(&self, a: N, mut b: N) -> bool {
        if a == b {
            return true;
        }

        while let Some(idom) = self.idoms.get(&b) {
            if *idom == a {
                return true;
            }
            // we are at the root of the dom tree
            if b == *idom {
                break;
            }

            b = *idom;
        }

        false
    }

    pub fn idom(&self, node: N) -> Option<N> {
        self.idoms.get(&node).copied()
    }

    /// returns the strict dominators of the node
    /// if node has no strict dominator, it will return None
    pub fn strict_dominators(&self, node: N) -> Option<IdomIterator<'_, N>> {
        let idom = self.idom(node);
        if idom != Some(node) {
            Some(IdomIterator { next: self.idom(node), dom_tree: self })
        } else {
            None
        }
    }

    /// returns the iterator of dominators
    /// of the given node, including itself
    pub fn dominators(&self, node: N) -> IdomIterator<'_, N> {
        IdomIterator { next: Some(node), dom_tree: self }
    }
}

pub struct IdomIterator<'t, N> {
    next: Option<N>,
    dom_tree: &'t DomTree<N>,
}

impl<'t, N: PartialEq + Eq + Hash + Copy> Iterator for IdomIterator<'t, N> {
    type Item = N;

    fn next(&mut self) -> Option<Self::Item> {
        let cur = self.next?;
        let next_idom = self.dom_tree.idom(cur);

        if next_idom == self.next {
            self.next = None;
        } else {
            self.next = next_idom;
        }

        Some(cur)
    }
}

fn nearest_common_ancester<N: PartialEq + Eq + Hash + Copy>(
    mut pred1: N,
    mut pred2: N,
    bb_to_rpo: &HashMap<N, usize>,
    partial_idoms: &IndexMap<N, N>,
) -> N {
    assert!(partial_idoms.get(&pred1).is_some());
    assert!(partial_idoms.get(&pred2).is_some());
    while pred1 != pred2 {
        // whoever is at lower level of the tree should move upward
        while bb_to_rpo[&pred1] > bb_to_rpo[&pred2] {
            // # panic safety:
            // the dom tree is constructed downward
            // so when we iterate over preds1's idoms,
            // it's ancester's idoms has already been constructed
            pred1 = partial_idoms[&pred1];
        }
        while bb_to_rpo[&pred1] < bb_to_rpo[&pred2] {
            pred2 = partial_idoms[&pred2];
        }
    }

    // we are iterating over a tree, so the ancester of a and b must meet at some point,
    // which is the neartest commoon ancester for us.
    pred1
}

#[cfg(test)]
mod tests {

    use petgraph::Direction;
    use petgraph::algo::dominators::simple_fast;
    use petgraph::graph::{DiGraph, NodeIndex};

    use crate::graph::dom_tree::DomTree;
    use crate::graph::graph::*;

    impl<V, E> DirectedGraph for DiGraph<V, E> {
        type Node = NodeIndex;

        fn num_nodes(&self) -> usize {
            self.node_count()
        }
    }

    impl<V, E> Predecessors for DiGraph<V, E> {
        fn preds(&self, cur: Self::Node) -> impl Iterator<Item = Self::Node> {
            self.neighbors_directed(cur, Direction::Incoming)
        }
    }

    impl<V, E> Successors for DiGraph<V, E> {
        fn succs(&self, cur: Self::Node) -> impl Iterator<Item = Self::Node> {
            self.neighbors_directed(cur, Direction::Outgoing)
        }
    }

    fn assert_dom_tree_eq(g: &DiGraph<&str, ()>, entry: NodeIndex) {
        let petgraph_doms = simple_fast(g, entry);
        let my_dom_tree = DomTree::build(entry, g);

        for node in g.node_indices() {
            let expected_idom = petgraph_doms.immediate_dominator(node);

            // petgraph will ignore unreachable nodes
            if expected_idom.is_none() && node != entry {
                continue;
            }

            let actual_idom = my_dom_tree.idom(node);

            // 1. check idom
            if node == entry {
                assert_eq!(actual_idom, Some(entry), "Entry node must dominate itself");
            } else {
                assert_eq!(
                    actual_idom, expected_idom,
                    "Mismatch idom for node {:?} ({}): expected {:?}, got {:?}",
                    node, g[node], expected_idom, actual_idom
                );
            }

            // 2. check Dominators
            let mut expected_doms: Vec<_> = petgraph_doms.dominators(node).unwrap().collect();
            expected_doms.sort();

            let mut actual_doms: Vec<_> = my_dom_tree.dominators(node).collect();
            actual_doms.sort();

            assert_eq!(
                actual_doms, expected_doms,
                "Dominator chain mismatch for node {:?} ({})",
                node, g[node]
            );
        }
    }

    #[test]
    fn test_irreducible_cfg() {
        let mut g = DiGraph::<&str, ()>::new();
        let entry = g.add_node("Entry");
        let a = g.add_node("A");
        let b = g.add_node("B");

        g.add_edge(entry, a, ());
        g.add_edge(a, b, ());
        g.add_edge(b, a, ());

        assert_dom_tree_eq(&g, entry);
    }

    #[test]
    fn test_nested_loops_with_multiple_latches() {
        let mut g = DiGraph::<&str, ()>::new();
        let entry = g.add_node("Entry");
        let outer_head = g.add_node("OuterHead");
        let inner_head = g.add_node("InnerHead");
        let inner_body = g.add_node("InnerBody");
        let inner_latch = g.add_node("InnerLatch");
        let outer_latch = g.add_node("OuterLatch");
        let exit = g.add_node("Exit");

        g.add_edge(entry, outer_head, ());
        g.add_edge(outer_head, inner_head, ());
        g.add_edge(inner_head, inner_body, ());

        // Inner branches
        g.add_edge(inner_body, inner_latch, ()); // continue inner
        g.add_edge(inner_body, outer_latch, ()); // break inner

        g.add_edge(inner_latch, inner_head, ()); // Inner backedge
        g.add_edge(outer_latch, outer_head, ()); // Outer backedge

        g.add_edge(outer_head, exit, ());

        assert_dom_tree_eq(&g, entry);
    }

    use rand::rngs::StdRng;
    use rand::{RngExt, SeedableRng};

    #[test]
    fn fuzz_dom_tree() {
        let mut rng = StdRng::seed_from_u64(42);

        for _ in 0..1000 {
            let num_nodes = rng.random_range(5..50);
            let num_extra_edges = rng.random_range(5..100);

            let mut g = DiGraph::<&str, ()>::new();
            let mut nodes = Vec::new();

            for _ in 0..num_nodes {
                nodes.push(g.add_node("Node"));
            }

            let entry = nodes[0];

            for i in 1..num_nodes {
                let parent_idx = rng.random_range(0..i);
                g.add_edge(nodes[parent_idx], nodes[i], ());
            }

            for _ in 0..num_extra_edges {
                let from = nodes[rng.random_range(0..num_nodes)];
                let to = nodes[rng.random_range(0..num_nodes)];
                g.add_edge(from, to, ());
            }

            // 如果断言失败，这里会 panic，你可以通过循环变量 i 和当时随机生成的 g 来复现
            assert_dom_tree_eq(&g, entry);
        }
    }
}
