use std::collections::HashMap;

use koopa::ir::builder::{LocalInstBuilder, ValueBuilder};
use koopa::ir::{BasicBlock, Value, ValueKind};
use koopa::opt::FunctionPass;
use smallvec::SmallVec;

use crate::graph::reachable::reachable;
use crate::graph::{Predecessors, Successors};
use crate::utils::{replace_operands, safely_remove_inst_from_dfg};

/// simplify and canonicalize the CFG of a function
/// will:
///     1. remove unreachable BBs
///     2. merge a BB to its predecessor if it has only one predecessor
///         and its predecessor has only one successor
///     3. eliminate BBs that has no instruction other than an jump(unconditional)
///     
pub struct SimplifyCFG;

impl FunctionPass for SimplifyCFG {
    fn run_on(&mut self, _func: koopa::ir::Function, data: &mut koopa::ir::FunctionData) {
        // 1. remove unreachable BBs
        let reachable_bbs = match data.layout().entry_bb() {
            Some(entry) => reachable(data, &[entry]),
            None => Default::default(),
        };
        let unreachable_bbs = data
            .layout_mut()
            .bbs()
            .keys()
            .filter(|bb| !reachable_bbs.contains(bb))
            .copied()
            .collect::<Vec<_>>();

        // dead instructions for the unreachable blocks
        let mut removed_insts: Vec<Value> = vec![];
        for bb in &unreachable_bbs {
            if let Some((_, node)) = data.layout_mut().bbs_mut().remove(bb) {
                for (inst, _) in node.insts().iter() {
                    removed_insts.push(*inst);
                }
            }
        }

        for inst in &removed_insts {
            safely_remove_inst_from_dfg(data.dfg_mut(), *inst);
        }

        for bb in &unreachable_bbs {
            data.dfg_mut().remove_bb(*bb);
        }

        // 2. merge a BB to its predecessor if it has only one predecessor
        //    and its predecessor has only one successor
        loop {
            let mut changed = false;

            let target_pair = data.layout().bbs().keys().find_map(|&bb| {
                let preds: SmallVec<[BasicBlock; 4]> = data.preds(bb).collect();
                if preds.len() == 1 && data.succs(preds[0]).count() == 1 {
                    Some((bb, preds[0]))
                } else {
                    None
                }
            });

            if let Some((bb, pred)) = target_pair
                && merge_bb(data, pred, bb)
            {
                changed = true;
            }

            if !changed {
                break;
            }
        }

        // 3. eliminate BBs that has no instruction other than an jump(unconditional)
        loop {
            let mut changed = false;

            let empty_bb = data
                .layout()
                .bbs()
                .keys()
                .find(|&bb| {
                    let insts = data.layout().bbs().node(bb).unwrap().insts();
                    insts.len() == 1
                        && matches!(
                            data.dfg().value(*insts.back_key().unwrap()).kind(),
                            ValueKind::Jump(_)
                        )
                })
                .copied();

            if let Some(empty_bb) = empty_bb
                && eliminate_empty_bb(data, empty_bb)
            {
                changed = true;
            }

            if !changed {
                break;
            }
        }
    }
}

// merge all insts in `bb` into `pred` and remove `bb` from function's layout
// returns if its successfully merged
fn merge_bb(data: &mut koopa::ir::FunctionData, pred: BasicBlock, bb: BasicBlock) -> bool {
    let preds: SmallVec<[BasicBlock; 4]> = data.preds(bb).collect();
    let satisfy = preds.len() == 1 && preds[0] == pred && data.succs(pred).count() == 1;
    if !satisfy {
        return false;
    }

    // 1. remove from layout
    let node = match data.layout_mut().bbs_mut().remove(&bb) {
        Some((_, node)) => node,
        None => return false,
    };

    let pred_termin = data.layout_mut().bb_mut(pred).insts_mut().back_key().copied().unwrap();

    let params = data.dfg().bb(bb).params().iter().copied().collect::<SmallVec<[Value; 4]>>();
    let args = match data.dfg().value(pred_termin).kind() {
        ValueKind::Jump(jump) => jump.args().iter().copied().collect::<SmallVec<[Value; 4]>>(),
        _ => todo!(),
    };
    let v_map = params.into_iter().zip(args).collect::<HashMap<_, _>>();

    // 2. add all instructions in `bb` to `pred`
    //    fix the usage of BlockParams of `bb` in these insts
    //    before:
    //
    // %pred:
    //  ...
    //  jump %bb(%arg1, %arg2)
    //
    // %bb(%param1, %param2):
    //  ...
    //  %10 = add %param1, %param2
    //  %11 = mul %param1, %param2
    //  jump %next(%param2)
    //
    // after:
    // %pred:
    //  ...
    //  %10 = add %arg1, %arg2
    //  %11 = mul %arg1, %arg2
    //  jump %next(%arg2)
    for (inst, _) in node.insts().iter() {
        data.layout_mut()
            .bb_mut(pred)
            .insts_mut()
            .cursor_back_mut()
            .insert_key_before(*inst)
            .unwrap();

        let mut inst_data = data.dfg().value(*inst).clone();
        if replace_operands(&mut inst_data, &v_map) {
            data.dfg_mut().replace_value_with(*inst).raw(inst_data);
        }
    }
    data.layout_mut().bb_mut(pred).insts_mut().cursor_back_mut().remove_current().unwrap();

    true
}

// eliminate empty bb, update its predecessor's terminator
// returns if the structure is changed
fn eliminate_empty_bb(data: &mut koopa::ir::FunctionData, empty_bb: BasicBlock) -> bool {
    let (target_bb, jump_args) = {
        let node = data.layout().bbs().node(&empty_bb).unwrap();
        let jump_inst_val = node.insts().back_key().unwrap();
        let jump_inst = data.dfg().value(*jump_inst_val);

        match jump_inst.kind() {
            ValueKind::Jump(jump) => {
                let args = jump.args().to_vec();
                (jump.target(), args)
            }
            _ => unreachable!(),
        }
    };

    if target_bb == empty_bb {
        return false;
    }

    let preds: SmallVec<[BasicBlock; 4]> = data.preds(empty_bb).collect();
    if preds.is_empty() {
        return false;
    }

    let mut succ_cnt = 0;

    let params = data.dfg().bb(empty_bb).params().iter().copied().collect::<SmallVec<[Value; 4]>>();

    for pred in &preds {
        let pred_terminator_val =
            *data.layout().bbs().node(pred).unwrap().insts().back_key().unwrap();
        let mut new_terminator_data = data.dfg().value(pred_terminator_val).clone();

        match new_terminator_data.kind_mut() {
            ValueKind::Jump(jump) => {
                if jump.target() == empty_bb {
                    // before:
                    //
                    // %pred:
                    //    jump %empty_bb(%arg1, %arg2)
                    // %empty_bb(%param1, %param2):
                    //   jump %next(%v1, %v2, %param2)
                    //

                    // after:
                    //
                    // %pred:
                    //    jump %next(%v1, %v2, %arg2)

                    let prev_args = jump.args().iter().copied().collect::<SmallVec<[Value; 4]>>();
                    let v_map =
                        params.clone().into_iter().zip(prev_args).collect::<HashMap<_, _>>();
                    let mut final_args = jump_args.clone();
                    replace_operands(&mut final_args, &v_map);

                    data.dfg_mut()
                        .replace_value_with(pred_terminator_val)
                        .jump_with_args(target_bb, final_args);
                    succ_cnt += 1;
                }
            }
            ValueKind::Branch(branch) => {
                let (true_bb, true_args) = if branch.true_bb() == empty_bb {
                    let prev_args =
                        branch.true_args().iter().copied().collect::<SmallVec<[Value; 4]>>();
                    let v_map =
                        params.clone().into_iter().zip(prev_args).collect::<HashMap<_, _>>();
                    let mut final_args = jump_args.clone();
                    replace_operands(&mut final_args, &v_map);

                    (target_bb, final_args)
                } else {
                    (branch.true_bb(), branch.true_args().to_vec())
                };

                let (false_bb, false_args) = if branch.false_bb() == empty_bb {
                    let prev_args =
                        branch.false_args().iter().copied().collect::<SmallVec<[Value; 4]>>();
                    let v_map =
                        params.clone().into_iter().zip(prev_args).collect::<HashMap<_, _>>();
                    let mut final_args = jump_args.clone();
                    replace_operands(&mut final_args, &v_map);

                    (target_bb, final_args)
                } else {
                    (branch.false_bb(), branch.false_args().to_vec())
                };

                if true_bb == false_bb {
                    continue;
                }

                data.dfg_mut().replace_value_with(pred_terminator_val).branch_with_args(
                    branch.cond(),
                    true_bb,
                    false_bb,
                    true_args,
                    false_args,
                );
                succ_cnt += 1;
            }
            _ => unreachable!(),
        };
    }

    if succ_cnt == preds.len()
        && let Some((_, node)) = data.layout_mut().bbs_mut().remove(&empty_bb)
    {
        for (inst, _) in node.insts().iter() {
            safely_remove_inst_from_dfg(data.dfg_mut(), *inst);
        }
        data.dfg_mut().remove_bb(empty_bb);
    }

    succ_cnt != 0
}

#[cfg(test)]
mod tests {
    use koopa::back::koopa::Visitor as KoopaVisitor;
    use koopa::back::{NameManager, Visitor};
    use koopa::front::Driver;

    use super::*;

    fn apply_pass(ir_text: &str, debug_on: bool) {
        let driver = Driver::from(ir_text);
        let mut program = driver.generate_program().unwrap();
        let func_id = *program.funcs().keys().next().unwrap();
        let mut pass = SimplifyCFG;
        let func_data = program.func_mut(func_id);
        pass.run_on(func_id, func_data);

        if debug_on {
            let mut visitor = KoopaVisitor;
            let mut nm = NameManager::new();
            let mut w = std::io::stdout();
            visitor.visit(&mut w, &mut nm, &program).unwrap();
        }
    }

    fn apply_pass_and_count_bbs(ir_text: &str) -> usize {
        let driver = Driver::from(ir_text);
        let mut program = driver.generate_program().unwrap();
        let func_id = *program.funcs().keys().next().unwrap();
        let mut pass = SimplifyCFG;
        let func_data = program.func_mut(func_id);
        pass.run_on(func_id, func_data);
        func_data.layout().bbs().len()
    }

    #[test]
    fn test_all_bbs_reachable() {
        // 全部可达
        let ir = r#"
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

        // init_a was removed
        // but init_b could not be removed because branch inst cannot have two same block in koopa
        assert_eq!(apply_pass_and_count_bbs(ir), 7);
    }

    #[test]
    fn test_remove_unreachable_bbs() {
        // 一个不可达块 `%dead_block`
        let ir = r#"
        fun @test(%cond1: i32, %cond2: i32): i32 {
        %entry:
          br %cond1, %init_a, %init_b

        // ==== 这是一个不可达块 ====
        %dead_block:
          %dead_val = add 1, 2
          jump %init_a
        // ===========================
        
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

        assert_eq!(apply_pass_and_count_bbs(ir), 7);
    }

    #[test]
    fn test_remove_unreachable_loop() {
        // 构造一个包含完整循环结构（Header, Body, Exit）但入口被切断的 IR
        let ir = r#"
        fun @test_unreachable_loop(%cond: i32): i32 {
        %entry:
          br %cond, %true_path, %false_path

        %true_path:
          jump %exit(1)

        %false_path:
          jump %exit(0)

        // ==== 不可达的循环结构 (Dead Loop) ====
        // 没有任何可达的基本块跳转到 %dead_header
        %dead_header(%i: i32):
          %cmp = lt %i, 10
          br %cmp, %dead_body, %dead_end

        %dead_body:
          %next_i = add %i, 1
          // 这里有一条回边 (Backedge) 构成了环
          jump %dead_header(%next_i)

        %dead_end:
          // 虽然死循环的出口连接到了可达的 %exit，
          // 但因为 %dead_header 不可达，整条链路都是死代码
          jump %exit(2)
        // ======================================

        %exit(%ret_val: i32):
          ret %ret_val
        }
        "#;

        assert_eq!(apply_pass_and_count_bbs(ir), 3);
    }

    #[test]
    fn test_remove_multiple_unreachable_blocks() {
        // Multiple linked unreachable blocks
        let ir = r#"
        fun @test(%cond: i32): i32 {
        %entry:
          br %cond, %true_path, %false_path

        // ==== Unreachable cluster ====
        %dead1:
          %v1 = add 1, 2
          jump %dead2
          
        %dead2:
          %v2 = mul 3, 4
          jump %dead1
        // =============================
        
        %true_path:
          jump %exit(1)

        %false_path:
          jump %exit(0)
          
        %exit(%ret_val: i32):
          ret %ret_val
        }
        "#;
        assert_eq!(apply_pass_and_count_bbs(ir), 3);
    }

    #[test]
    fn test_merge_block_with_params_and_insts() {
        let ir = r#"
        fun @test(): i32 {
        %entry:
          jump %bb1(5)

        %bb1(%p1: i32):
          %v1 = add %p1, 2
          jump %bb2(%v1)

        %bb2(%p2: i32):
          %v2 = mul %p2, 3
          ret %v2
        }
        "#;
        // Entry -> bb1 -> bb2 (ret). All have single pred/succ.
        // Should merge down to 1 block.
        assert_eq!(apply_pass_and_count_bbs(ir), 1);
    }

    #[test]
    fn test_do_not_merge_multiple_successors() {
        let ir = r#"
        fun @test(%cond: i32): i32 {
        %entry:
          jump %bb1
          
        %bb1:
          br %cond, %bb2, %bb3
          
        %bb2:
          jump %exit
          
        %bb3:
          jump %exit
          
        %exit:
          ret 0
        }
        "#;
        // %entry merges with %bb1 (1 block).
        // %bb1 has multiple successors, so it cannot merge with %bb2 or %bb3.
        // %exit has multiple predecessors, so %bb2 and %bb3 cannot merge into %exit.
        // Total expected blocks: 4 (merged entry+bb1+bb2, bb3, exit)
        assert_eq!(apply_pass_and_count_bbs(ir), 3);
    }

    #[test]
    fn test_merge_bb() {
        let ir = r#"
        fun @test(): i32 {
        %entry:
          jump %exit(1, 2, 3)
        
        %exit(%p1: i32, %p2: i32, %p3: i32):
          %10 = add %p1, %p2
          %11 = add %10, %p3
          ret %11
        }
        "#;
        apply_pass(ir, true);
    }

    #[test]
    fn test_should_no_change() {
        let ir = r#"
        fun @test(%cond: i32): i32 {
        %entry:
          br %cond, %true_path, %false_path

        %true_path:
          jump %exit(1, 2, 3)

        %false_path:
          jump %exit(3, 2, 1)
        
        %exit(%p1: i32, %p2: i32, %p3: i32):
          %10 = add %p1, %p2
          %11 = add %10, %p3
          ret %11
        }
        "#;
        assert_eq!(apply_pass_and_count_bbs(ir), 3);
    }

    #[test]
    fn test_cascade() {
        let ir = r#"
        fun @test(%cond: i32): i32 {
        %entry:
          jump %bb1

        %bb1:
          jump %bb2

        %bb2:
          jump %exit(3, 2, 1)
        
        %exit(%p1: i32, %p2: i32, %p3: i32):
          %10 = add %p1, %p2
          %11 = add %10, %p3
          ret %11
        }
        "#;
        assert_eq!(apply_pass_and_count_bbs(ir), 1);
    }
}
