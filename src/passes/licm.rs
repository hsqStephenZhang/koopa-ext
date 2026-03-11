///! Loop Invariatn Code Motion
use std::collections::HashMap;

use koopa::ir::{BasicBlock, BinaryOp, FunctionData, Value};
use koopa::opt::FunctionPass;

use crate::graph::dom_tree::DomTree;
use crate::graph::loops::LoopsAnalysis;
use crate::graph::traverse::reverse_post_order;

pub struct LICM;

impl FunctionPass for LICM {
    fn run_on(&mut self, _func: koopa::ir::Function, data: &mut koopa::ir::FunctionData) {
        let entry = data.layout().entry_bb().unwrap();
        let dom_tree = DomTree::build(entry, data);
        let mut loops = LoopsAnalysis::new();
        loops.compute(data, entry, &dom_tree);

        let rpo: Vec<BasicBlock> = reverse_post_order(data, entry);
        let bb_to_rpo_num =
            rpo.iter().enumerate().map(|(i, bb)| (*bb, i)).collect::<HashMap<_, _>>();

        let mut loop_to_bb = loops.loop_to_bb();
        for lp in loops.bottom_up() {
            // the basic block in the loop, we sort it by RPO
            let mut is_invariants: HashMap<Value, bool> = HashMap::new();
            let mut lp_basic_blocks = loop_to_bb.remove(&lp).unwrap();
            lp_basic_blocks.sort_by(|a, b| bb_to_rpo_num[a].cmp(&bb_to_rpo_num[b]));

            for bb in lp_basic_blocks {
                let lp = loops.bb_to_loop()[&bb];
                // the invariant instruction will be executed outside of the loop
                // we should only hoist instruction that has no side effect
                let bb_dominate_exits =
                    loops.exits(data, lp).all(|exit| dom_tree.dominates(bb, exit));

                // tells if the given val is an invariant for current lp
                let test_invar =
                    |data: &FunctionData, partial_map: &mut HashMap<Value, bool>, val: Value| {
                        // 1. const
                        let is_const = data.dfg().value(val).kind().is_const();
                        // 2. already set
                        let is_computed_inv = partial_map.get(&val).copied().unwrap_or_default();
                        // 3. a value defined outside the loop
                        let is_inv_inst = match data.layout().parent_bb(val) {
                            Some(bb) => !loops.contains(lp, bb),
                            None => false,
                        };
                        let res = is_const || is_inv_inst || is_computed_inv;
                        res
                    };

                // instruction to hoist to the preheader of the loop
                let mut to_hoist = vec![];

                let insts = data.layout().bbs().node(&bb).unwrap();
                for (&inst, _) in insts.insts() {
                    // an instruction is an invaraint, if all its operands are invariant
                    let value_data = data.dfg().value(inst);
                    let is_invariant = match value_data.kind() {
                        koopa::ir::ValueKind::Binary(binary) => {
                            let is_inv1 = test_invar(data, &mut is_invariants, binary.lhs());
                            let is_inv2 = test_invar(data, &mut is_invariants, binary.rhs());

                            (!has_side_effect(binary.op()) || bb_dominate_exits)
                                && is_inv1
                                && is_inv2
                        }
                        _ => false,
                    };
                    dbg!(is_invariant);
                    is_invariants.insert(inst, is_invariant);
                    if is_invariant {
                        to_hoist.push(inst);
                    }
                }

                // suppose prehead does exist and don't have to bother with creating new preheader
                // TODO: create new preheader if None
                let preheader = loops.preheader(data, lp).unwrap();

                for inst in to_hoist {
                    data.layout_mut().bb_mut(bb).insts_mut().remove(&inst);
                    let mut cursor =
                        data.layout_mut().bb_mut(preheader).insts_mut().cursor_back_mut();
                    cursor.insert_before(inst, ()).unwrap();
                }
            }
        }
    }
}

fn has_side_effect(op: BinaryOp) -> bool {
    matches!(op, BinaryOp::Div | BinaryOp::Mod)
}

#[cfg(test)]
mod tests {
    use koopa::back::koopa::Visitor as KoopaVisitor;
    use koopa::back::{NameManager, Visitor};
    use koopa::front::Driver;
    use koopa::opt::FunctionPass;

    use crate::passes::licm::LICM;

    #[test]
    fn test_simple() {
        let src = r#"
decl @getint(): i32

fun @test(): i32 {
%entry:
  %0 = call @getint()  // n
  %1 = call @getint()  // a
  %2 = call @getint()  // b
  jump %while_cond(0, 0) // (sum, i)

%while_cond(%3: i32, %4: i32):  // %3 是 sum, %4 是 i
  %5 = lt %4, %0
  br %5, %while_body, %while_end

%while_body:
  %6 = add %1, %2       // <-- this is an invariant deps on %1 and %2
  jump %while_body2

%while_body2:
  %7 = add %6, 2        // <-- this is an invariant deps on %6
  %8 = add %7, 3        // <-- this is an invariant deps on %7
  %9 = div %8, %6       // <-- has side effect, should not hoist
  %10 = add %9, 1       // should not 
  %90 = add %3, %10      // sum + inv
  %91 = add %4, 1       // i + 1
  jump %while_cond(%90, %91)

%while_end:
  ret %3
}
"#;
        let driver: Driver<_> = src.into();
        let mut prog = driver.generate_program().unwrap();
        let (func, data) = prog.funcs_mut().iter_mut().find(|bb| bb.1.name() == "@test").unwrap();
        let mut licm = LICM;
        licm.run_on(*func, data);

        let mut visitor = KoopaVisitor;
        let mut nm = NameManager::new();
        let mut w = std::io::stdout();
        visitor.visit(&mut w, &mut nm, &prog).unwrap();
    }
}
