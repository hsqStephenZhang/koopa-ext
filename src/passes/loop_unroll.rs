// use koopa::opt::FunctionPass;

// use crate::graph::{dom_tree::DomTree, loops::LoopsAnalysis};

// pub struct LoopUnRoll;

// impl FunctionPass for LoopUnRoll {
//     fn run_on(&mut self, _func: koopa::ir::Function, data: &mut koopa::ir::FunctionData) {
//         let Some(entry) = data.layout().entry_bb() else {
//             return;
//         };
//         let dom_tree = DomTree::build(entry, data);
//         let mut loops = LoopsAnalysis::new();
//         loops.compute(data, entry, &dom_tree);

//         // start from the inner loop
//         for lp in loops.bottom_up() {

//         }
//     }
// }
