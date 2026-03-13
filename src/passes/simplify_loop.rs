use koopa::ir::builder::{BasicBlockBuilder, LocalInstBuilder, ValueBuilder};
use koopa::ir::{BasicBlock, ValueKind};
use koopa::opt::FunctionPass;
use smallvec::SmallVec;

use crate::graph::Predecessors;
use crate::graph::dom_tree::DomTree;
use crate::graph::loops::LoopsAnalysis;
use crate::graph::terminator::TerminatorExt;

/// This pass Will transform loops into a simplier/canonical form
/// to make the life of other loop ralated passes easier
///
/// reference:
///     https://llvm.org/docs/LoopTerminology.html
///     https://llvm.org/doxygen/LoopSimplify_8cpp_source.html
///
/// When Success, each loop has:
///     1. A preheader.
///     2. A single backedge (which implies that there is a single latch).
///     3. Dedicated exits. That is, no exit block for the loop has a predecessor that is outside the loop.
///  This implies that all exit blocks are dominated by the loop header.
pub struct LoopSimpliy;

impl FunctionPass for LoopSimpliy {
    fn run_on(&mut self, _func: koopa::ir::Function, data: &mut koopa::ir::FunctionData) {
        let Some(entry) = data.layout().entry_bb() else {
            return;
        };
        let dom_tree = DomTree::build(entry, data);
        let mut loops = LoopsAnalysis::new();
        loops.compute(data, entry, &dom_tree);

        let lps = loops.loops().keys().cloned().collect::<Vec<_>>();

        for lp in lps {
            let header = loops.loops()[&lp].header();
            let header_name =
                data.dfg().bb(header).name().clone().unwrap_or("%unknown_header".into());

            // %pred1:
            //    ...
            //   jump %preheader(%arg1_val_pred1, %arg2_val_pred1)
            //
            // %pred2:
            //   ...
            //   jump %preheader(%arg1_val_pred2, %arg2_val_pred2)

            // %preheader(%arg1_clone, %arg2_clone):
            //   jump %preheader(%arg1_clone, %arg2_clone)

            // %header(%arg1, %arg2):
            //   ...
            if loops.preheader(data, lp).is_none() {
                // 1. create pre-header bb
                let preheader =
                    merge_preds(data, header, format!("{}_preheader", header_name), |pred| {
                        !loops.contains(lp, *pred)
                    });
                assert!(preheader.is_some());

                // the header has no predecessor
                // there are two possibilities:
                // 1. it's entry block. we need to simpliy create an new entry block and jump to header.
                //    **But that's forbidden in IR, since entry cannot have any preds**
                // 2. it's an unreachable loop's header. let's simply ignore the case.
                if let (Some(parent), Some(bb)) = (loops.loops()[&lp].parent(), preheader) {
                    // dedicate_exit is outside the loop
                    loops.add_bb_to_loop(parent, bb);
                }
            }

            // 2. latches
            //    it works similar with the merged pre-header, except that we aims at the preds of the header that are in the loop
            let latches = loops.latches(data, lp);
            if latches.len() > 1 {
                let merged_latch =
                    merge_preds(data, header, format!("{}_merged_latch", header_name), |pred| {
                        loops.contains(lp, *pred)
                    });
                loops.add_bb_to_loop(lp, merged_latch.unwrap());
            }

            // 3. exits
            // before:
            //      entry  -> exit
            //      entry  -> header
            //      header -> exit
            //      header -> latch
            //      latch  -> header

            // after:
            //      entry  -> exit
            //      entry  -> header
            //      header -> dedicate_exit
            //      dedicate_exit -> exit
            //      header -> latch
            //      latch  -> header

            let exits = loops.exits(data, lp).collect::<SmallVec<[BasicBlock; 3]>>();
            for exit in exits {
                // exit block that has a predecessor is outside the loop.
                if !data.preds(exit).any(|pred| !loops.contains(lp, pred)) {
                    continue;
                }

                let dedicate_exit = merge_preds(data, exit, "%dedicate_exit".into(), |pred| {
                    loops.contains(lp, *pred)
                });

                if let (Some(bb), Some(parent)) = (dedicate_exit, loops.loops()[&lp].parent()) {
                    // dedicate_exit is outside the loop
                    loops.add_bb_to_loop(parent, bb);
                }
            }
        }
    }
}

// merge some preds of `target` that satisfy the `filter`
// so all these preds go through the merged bb before entering `target`
fn merge_preds(
    data: &mut koopa::ir::FunctionData,
    target: BasicBlock,
    merge_bb_name: String,
    filter: impl FnMut(&BasicBlock) -> bool,
) -> Option<BasicBlock> {
    let preds = data.preds(target).filter(filter).collect::<SmallVec<[BasicBlock; 3]>>();
    if preds.is_empty() {
        return None;
    }

    let param_tys = data
        .dfg()
        .bb(target)
        .params()
        .iter()
        .map(|v| (None, data.dfg().value(*v).ty().clone()))
        .collect::<Vec<_>>();

    let builder = data.dfg_mut().new_bb();
    let merge_bb = builder.basic_block_with_param_names(Some(merge_bb_name), param_tys);
    data.layout_mut().bbs_mut().push_key_back(merge_bb).unwrap();
    let preheader_params = data.dfg().bb(merge_bb).params().to_vec();

    // 2. link preheader with original preds of the loop header
    for pred in preds {
        let (terminator, mut terminator_kind) = data.terminator_raw(pred);
        match terminator_kind.kind_mut() {
            ValueKind::Branch(branch) => {
                if branch.true_bb() == target {
                    *branch.true_bb_mut() = merge_bb;
                }
                if branch.false_bb() == target {
                    *branch.false_bb_mut() = merge_bb;
                }
                data.dfg_mut().replace_value_with(terminator).raw(terminator_kind);
            }
            ValueKind::Jump(jump) => {
                assert_eq!(jump.target(), target);
                *jump.target_mut() = merge_bb;
                data.dfg_mut().replace_value_with(terminator).raw(terminator_kind);
            }
            _ => unreachable!(),
        };
    }

    // 3. link preheader with header
    let inst_builder = data.dfg_mut().new_value();
    let jump = inst_builder.jump_with_args(target, preheader_params);
    let _ = data.layout_mut().bb_mut(merge_bb).insts_mut().push_key_back(jump);

    Some(merge_bb)
}

#[cfg(test)]
mod tests {
    use koopa::back::koopa::Visitor as KoopaVisitor;
    use koopa::back::{NameManager, Visitor};
    use koopa::front::Driver;
    use koopa::ir::{BasicBlock, FunctionData};
    use koopa::opt::FunctionPass;

    use crate::graph::Predecessors;
    use crate::passes::simplify_loop::LoopSimpliy;

    #[test]
    fn test_simple() {
        let src = r#"
fun @test(%cond1: i32, %cond2: i32): i32 {
%entry:
  br %cond1, %init_a, %init_b

%init_a:
  // 外部前驱 1
  jump %loop_header(0)

%init_b:
  // 外部前驱 2
  jump %loop_header(1)

%loop_header(%i: i32):
  %cmp = lt %i, 10
  br %cmp, %loop_body, %exit

%loop_body:
  br %cond2, %latch_a, %latch_b

%latch_a:
  %next_a = add %i, 1
  // 回边 1
  jump %loop_header(%next_a)

%latch_b:
  %next_b = add %i, 2
  // 回边 2
  jump %loop_header(%next_b)

%exit:
  ret %i
}
"#;
        let driver: Driver<_> = src.into();
        let mut prog = driver.generate_program().unwrap();
        let (func, data) = prog.funcs_mut().iter_mut().find(|bb| bb.1.name() == "@test").unwrap();
        let mut lp_simplify = LoopSimpliy;
        lp_simplify.run_on(*func, data);

        let mut visitor = KoopaVisitor;
        let mut nm = NameManager::new();
        let mut w = std::io::stdout();
        visitor.visit(&mut w, &mut nm, &prog).unwrap();
    }

    fn find_bb(data: &FunctionData, expect_name: &str) -> Option<BasicBlock> {
        data.dfg().bbs().iter().find_map(|(&bb, bb_data)| {
            if let Some(name) = bb_data.name() {
                if name.eq(expect_name) {
                    return Some(bb);
                }
            }
            None
        })
    }

    #[test]
    fn test_simple_preheader_and_latch() {
        let src = r#"
fun @test(%cond1: i32, %cond2: i32): i32 {
%entry:
  br %cond1, %init_a, %init_b

%init_a:
  jump %loop_header(0)

%init_b:
  jump %loop_header(1)

%loop_header(%i: i32):
  %cmp = lt %i, 10
  br %cmp, %loop_body, %exit

%loop_body:
  br %cond2, %latch_a, %latch_b

%latch_a:
  %next_a = add %i, 1
  jump %loop_header(%next_a)

%latch_b:
  %next_b = add %i, 2
  jump %loop_header(%next_b)

%exit:
  ret %i
}
"#;
        let driver: Driver<_> = src.into();
        let mut prog = driver.generate_program().unwrap();
        let (func, data) = prog.funcs_mut().iter_mut().find(|bb| bb.1.name() == "@test").unwrap();

        let mut lp_simplify = LoopSimpliy;
        lp_simplify.run_on(*func, data);

        let preheader = find_bb(data, "%loop_header_preheader").expect("Should generate preheader");
        let merged_latch =
            find_bb(data, "%loop_header_merged_latch").expect("Should generate merged latch");
        let header = find_bb(data, "%loop_header").unwrap();

        let header_preds: Vec<_> = data.preds(header).collect();
        assert_eq!(header_preds.len(), 2, "Canonical header must have exactly 2 predecessors");
        for pred in &header_preds {
            println!("pred: {:?}", data.dfg().bb(*pred).name());
        }
        assert!(header_preds.contains(&merged_latch));
        assert!(header_preds.contains(&preheader));

        let init_a = find_bb(data, "%init_a").unwrap();
        let init_b = find_bb(data, "%init_b").unwrap();
        let preheader_preds: Vec<_> = data.preds(preheader).collect();
        assert_eq!(preheader_preds.len(), 2);
        assert!(preheader_preds.contains(&init_a));
        assert!(preheader_preds.contains(&init_b));

        let latch_a = find_bb(data, "%latch_a").unwrap();
        let latch_b = find_bb(data, "%latch_b").unwrap();
        let latch_preds: Vec<_> = data.preds(merged_latch).collect();
        assert_eq!(latch_preds.len(), 2);
        assert!(latch_preds.contains(&latch_a));
        assert!(latch_preds.contains(&latch_b));
    }

    #[test]
    fn test_dedicate_exits() {
        let src = r#"
fun @test_exit(%cond1: i32, %cond2: i32): i32 {
%entry:
  br %cond1, %loop_preheader, %shared_exit(100)

%loop_preheader:
  jump %loop_header

%loop_header:
  br %cond2, %loop_body, %shared_exit(200)

%loop_body:
  jump %loop_header

%shared_exit(%res: i32):
  ret %res
}
"#;
        let driver: Driver<_> = src.into();
        let mut prog = driver.generate_program().unwrap();
        let (func, data) =
            prog.funcs_mut().iter_mut().find(|bb| bb.1.name() == "@test_exit").unwrap();

        let mut lp_simplify = LoopSimpliy;
        lp_simplify.run_on(*func, data);

        let dedicate_exit = find_bb(data, "%dedicate_exit").expect("Should generate dedicate exit");
        let shared_exit = find_bb(data, "%shared_exit").unwrap();
        let loop_header = find_bb(data, "%loop_header").unwrap();
        let entry = find_bb(data, "%entry").unwrap();

        let shared_preds: Vec<_> = data.preds(shared_exit).collect();
        assert_eq!(shared_preds.len(), 2, "Shared exit should have 2 preds now");
        assert!(shared_preds.contains(&entry));
        assert!(shared_preds.contains(&dedicate_exit));

        let dedicate_preds: Vec<_> = data.preds(dedicate_exit).collect();
        assert_eq!(dedicate_preds.len(), 1);
        assert!(dedicate_preds.contains(&loop_header));
    }

    #[test]
    fn test_nested_loops() {
        let src = r#"
fun @test_nested(%cond: i32): i32 {
%entry:
  jump %outer_header

%outer_header:
  // %outer_header 和 %outer_body 都跳向 %inner_header
  // 导致 %inner_header 有两个外部前驱，需要一个 preheader
  br %cond, %inner_header, %outer_body

%outer_body:
  jump %inner_header

%inner_header:
  br %cond, %inner_body, %exit

%inner_body:
  // 内层回边
  jump %inner_header

%exit:
  ret 0
}
"#;
        let driver: Driver<_> = src.into();
        let mut prog = driver.generate_program().unwrap();
        let (func, data) =
            prog.funcs_mut().iter_mut().find(|bb| bb.1.name() == "@test_nested").unwrap();

        let mut lp_simplify = LoopSimpliy;
        lp_simplify.run_on(*func, data);

        let inner_preheader =
            find_bb(data, "%inner_header_preheader").expect("Inner loop needs a preheader");
        let inner_header = find_bb(data, "%inner_header").unwrap();

        let inner_header_preds: Vec<_> = data.preds(inner_header).collect();
        assert_eq!(inner_header_preds.len(), 2);
        assert!(inner_header_preds.contains(&inner_preheader));

        let outer_header = find_bb(data, "%outer_header").unwrap();
        let outer_body = find_bb(data, "%outer_body").unwrap();
        let inner_pre_preds: Vec<_> = data.preds(inner_preheader).collect();
        assert_eq!(inner_pre_preds.len(), 2);
        assert!(inner_pre_preds.contains(&outer_header));
        assert!(inner_pre_preds.contains(&outer_body));
    }
}
