use std::collections::{BTreeMap, HashMap};
use std::fmt::Debug;
use std::hash::Hash;

use crate::graph::dom_tree::DomTree;
use crate::graph::traverse::reverse_post_order;
use crate::graph::{DirectedGraph, Graph};

#[derive(PartialEq, Eq, Clone, Copy, Debug)]
pub struct LoopData<N> {
    /// header of the loop
    header: N,
    /// it's parent loop
    parent: Option<usize>,
    /// level of the loop
    level: usize,
}

impl<N> LoopData<N> {
    pub fn new(header: N, parent: Option<usize>) -> Self {
        Self { header, parent, level: 1 }
    }
}

pub struct LoopsAnalysis<N> {
    /// from loop's id to it's actual data
    loops: BTreeMap<usize, LoopData<N>>,
    /// basic block to the inner most loop
    bb_to_loop: HashMap<N, usize>,

    next_loop_id: usize,
}

impl<N: PartialEq + Eq + Hash + Copy + Debug> LoopsAnalysis<N> {
    pub fn new() -> Self {
        Self { loops: Default::default(), bb_to_loop: Default::default(), next_loop_id: 0 }
    }

    fn next_id(&mut self) -> usize {
        let id = self.next_loop_id;
        self.next_loop_id += 1;
        id
    }

    pub fn loops(&self) -> &BTreeMap<usize, LoopData<N>> {
        &self.loops
    }

    pub fn bb_to_loop(&self) -> &HashMap<N, usize> {
        &self.bb_to_loop
    }

    pub fn compute<G: DirectedGraph<Node = N> + Graph>(
        &mut self,
        graph: &G,
        start_node: N,
        dom_tree: &DomTree<N>,
    ) {
        let rpo: Vec<N> = reverse_post_order(graph, start_node);
        let loops = rpo
            .iter()
            .filter(|b| Self::is_loop_header(graph, **b, dom_tree))
            .cloned()
            .collect::<Vec<_>>();

        for lp in &loops {
            let cur_loop_num = self.next_id();
            self.loops.insert(cur_loop_num, LoopData::new(*lp, None));
        }

        let keys = self.loops.keys().copied().collect::<Vec<_>>();

        // start from the inner loop
        for &cur_loop_num in keys.iter().rev() {
            let header = self.loops[&cur_loop_num].header;
            // each block belongs to a deepest loop or doesn't belong to any at all
            // we perform reverse-dfs(iterate the preds rather than succ)
            // to collect the body of current loop and tag the loop that it belongs to it

            // init with all the latches
            let mut stack = graph
                .preds(header)
                .filter(|pred| dom_tree.dominates(header, *pred))
                .collect::<Vec<_>>();

            while !stack.is_empty() {
                let mut next = None;
                let cur = stack.pop().unwrap();

                match self.bb_to_loop.get(&cur).copied() {
                    None => {
                        self.bb_to_loop.insert(cur, cur_loop_num);
                        next = Some(cur);
                    }
                    Some(mut subloop_num) => {
                        // cur node is already visited
                        // there are two situations
                        //  1. it's the current loop. we have already visited it and tag the loop num for it.
                        //  2. it's a subloop. we must skip the body of the subloop by jumping to it's header

                        // if we have three loops l1 <- l2 <- l3
                        // l2 and l3 has already been handled
                        // then l3's parent is set, but l2's parent is not
                        // when we are handling l1
                        // we might encounter a latch that belongs to l3
                        // but we must start from l2's header and set l2's parent index
                        // 
                        // so we must find the first subloop whose parent idnex is still unset
                        while let Some(p) = self.loops.get(&subloop_num).unwrap().parent {
                            if p == cur_loop_num {
                                break;
                            } else {
                                subloop_num = p;
                            }
                        }

                        if subloop_num != cur_loop_num {
                            let subloop = self.loops.get_mut(&subloop_num).unwrap();
                            // first visit of this subloop
                            if subloop.parent.is_none() {
                                subloop.parent = Some(cur_loop_num);
                                next = Some(subloop.header);
                            }
                        }
                    }
                }

                if let Some(next) = next
                    && next != header
                {
                    stack
                        .extend(graph.preds(next).filter(|pred| dom_tree.dominates(header, *pred)));
                }
            }
        }

        // thanks to RPO, when we calculate the deps of loop with larger id, it's parent's depth
        // has already been set
        for id in keys {
            if let Some(p) = self.loops[&id].parent {
                let parent_level = self.loops[&p].level;
                self.loops.get_mut(&id).unwrap().level = parent_level + 1;
            } else {
                self.loops.get_mut(&id).unwrap().level = 1; // root loop
            }
        }
    }

    /// definition of loop header(BB):
    ///     BB dominates one of its predecessors
    fn is_loop_header<G: DirectedGraph<Node = N> + Graph>(
        graph: &G,
        node: N,
        dom_tree: &DomTree<N>,
    ) -> bool {
        graph.preds(node).any(|pred| dom_tree.dominates(node, pred))
    }
}

#[cfg(test)]
mod tests {
    use petgraph::graph::DiGraph;

    use super::*;
    use crate::graph::dom_tree::DomTree;

    #[test]
    fn test_simple_loop() {
        let mut g = DiGraph::<&str, ()>::new();
        let entry = g.add_node("Entry");
        let header = g.add_node("Header");
        let body = g.add_node("Body");
        let exit = g.add_node("Exit");

        g.add_edge(entry, header, ());
        g.add_edge(header, body, ());
        g.add_edge(body, header, ()); // Backedge
        g.add_edge(header, exit, ());

        let dom_tree = DomTree::build(entry, &g);
        let mut analysis = LoopsAnalysis::new();
        analysis.compute(&g, entry, &dom_tree);
        let loops = analysis.loops();
        for (id, loopdata) in loops {
            println!("{id} -> {:?}, {}", loopdata.parent, loopdata.header.index());
        }
        dbg!(analysis.bb_to_loop());
    }

    #[test]
    fn test_nested_loops() {
        let mut g = DiGraph::<&str, ()>::new();
        let entry = g.add_node("Entry");
        let outer_header = g.add_node("OuterHeader");
        let inner_header = g.add_node("InnerHeader");
        let inner_latch = g.add_node("InnerLatch");
        let outer_latch = g.add_node("OuterLatch");

        g.add_edge(entry, outer_header, ());
        g.add_edge(outer_header, inner_header, ());

        // Inner loop
        g.add_edge(inner_header, inner_latch, ());
        g.add_edge(inner_latch, inner_header, ()); // Inner backedge

        // Return to outer loop
        g.add_edge(inner_latch, outer_latch, ());
        g.add_edge(outer_latch, outer_header, ()); // Outer backedge

        let dom_tree = DomTree::build(entry, &g);
        let mut analysis = LoopsAnalysis::new();
        analysis.compute(&g, entry, &dom_tree);
        let loops = analysis.loops();
        for (id, loopdata) in loops {
            println!("{id} -> {:?}, {}", loopdata.parent, loopdata.header.index());
        }
        dbg!(analysis.bb_to_loop());
    }

    #[test]
    fn test_sibling_loops() {
        let mut g = DiGraph::<&str, ()>::new();
        let entry = g.add_node("Entry");
        let header1 = g.add_node("Header1");
        let header2 = g.add_node("Header2");

        g.add_edge(entry, header1, ());
        g.add_edge(header1, header1, ()); // Loop 1

        g.add_edge(entry, header2, ());
        g.add_edge(header2, header2, ()); // Loop 2

        let dom_tree = DomTree::build(entry, &g);
        let mut analysis = LoopsAnalysis::new();
        analysis.compute(&g, entry, &dom_tree);
        let loops = analysis.loops();
        for (id, loopdata) in loops {
            println!("{id} -> {:?}, {}", loopdata.parent, loopdata.header.index());
        }
        dbg!(analysis.bb_to_loop());
    }
}
