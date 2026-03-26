use std::hash::{Hash, Hasher};

use koopa::ir::builder::ValueBuilder;
use koopa::ir::{BasicBlock, BinaryOp, FunctionData, Value, ValueKind};
use koopa::opt::FunctionPass;
use rustc_hash::{FxHashMap, FxHasher};
use smallvec::SmallVec;

use crate::graph::dom_tree::DomTree;
use crate::utils::replace_operands;

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
enum ExprOp {
    Bin(BinaryOp),
}

impl ExprOp {
    fn is_commutative(&self) -> bool {
        match self {
            ExprOp::Bin(op) => matches!(
                op,
                BinaryOp::Add
                    | BinaryOp::Mul
                    | BinaryOp::Eq
                    | BinaryOp::NotEq
                    | BinaryOp::And
                    | BinaryOp::Or
                    | BinaryOp::Xor
            ),
        }
    }
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
struct ExprData {
    op: ExprOp,
    operands: SmallVec<[Value; 3]>,
}

impl ExprData {
    fn canonicalize(&mut self) {
        if self.op.is_commutative() {
            self.operands.sort_by_key(|v| {
                let mut hasher = FxHasher::default();
                v.hash(&mut hasher);
                hasher.finish()
            });
        }
    }
}

struct ScopedExprTable {
    table: FxHashMap<ExprData, Value>,
    scopes: Vec<Vec<(ExprData, Option<Value>)>>,
}

impl ScopedExprTable {
    fn new() -> Self {
        Self { table: FxHashMap::default(), scopes: Vec::new() }
    }

    fn enter_scope(&mut self) {
        self.scopes.push(Vec::new());
    }

    fn leave_scope(&mut self) {
        if let Some(scope_ops) = self.scopes.pop() {
            for (expr, old_val) in scope_ops.into_iter().rev() {
                if let Some(val) = old_val {
                    self.table.insert(expr, val);
                } else {
                    self.table.remove(&expr);
                }
            }
        }
    }

    fn lookup(&self, expr: &ExprData) -> Option<Value> {
        self.table.get(expr).copied()
    }

    fn insert(&mut self, expr: ExprData, val: Value) {
        let old_val = self.table.insert(expr.clone(), val);
        if let Some(current_scope) = self.scopes.last_mut() {
            current_scope.push((expr, old_val));
        }
    }
}

pub struct GVN;

impl FunctionPass for GVN {
    fn run_on(&mut self, _func: koopa::ir::Function, data: &mut FunctionData) {
        let Some(entry) = data.layout().entry_bb() else {
            return;
        };

        let dom_tree = DomTree::build(entry, data);

        let mut dom_children: FxHashMap<BasicBlock, Vec<BasicBlock>> = FxHashMap::default();
        for &bb in data.layout().bbs().keys() {
            if bb != entry {
                if let Some(idom) = dom_tree.idom(bb) {
                    dom_children.entry(idom).or_default().push(bb);
                }
            }
        }

        let mut scoped_table = ScopedExprTable::new();
        let mut leader_map: FxHashMap<Value, Value> = FxHashMap::default();
        let mut replacements: Vec<(Value, Value)> = Vec::new();

        visit_dom_tree(
            entry,
            data,
            &mut scoped_table,
            &mut leader_map,
            &mut replacements,
            &dom_children,
        );

        for (inst, leader) in replacements {
            let v_map = FxHashMap::from_iter([(inst, leader)]);
            for usage in data.dfg().value(inst).used_by().clone() {
                let mut value_kind = data.dfg().value(usage).clone();
                if replace_operands(&mut value_kind, &v_map) {
                    data.dfg_mut().replace_value_with(usage).raw(value_kind);
                }
            }
        }
    }
}

fn visit_dom_tree(
    bb: BasicBlock,
    data: &FunctionData,
    scoped_table: &mut ScopedExprTable,
    leader_map: &mut FxHashMap<Value, Value>,
    replacements: &mut Vec<(Value, Value)>,
    dom_children: &FxHashMap<BasicBlock, Vec<BasicBlock>>,
) {
    scoped_table.enter_scope();

    let insts: Vec<Value> =
        data.layout().bbs().node(&bb).unwrap().insts().keys().copied().collect();

    for inst in insts {
        let inst_data = data.dfg().value(inst);

        if let ValueKind::Binary(bin) = inst_data.kind() {
            let operands = inst_data
                .kind()
                .value_uses()
                .map(|use_val| leader_map.get(&use_val).copied().unwrap_or(use_val))
                .collect();

            let mut expr = ExprData { op: ExprOp::Bin(bin.op()), operands };
            expr.canonicalize();

            if let Some(leader) = scoped_table.lookup(&expr) {
                leader_map.insert(inst, leader);
                replacements.push((inst, leader));
            } else {
                leader_map.insert(inst, inst);
                scoped_table.insert(expr, inst);
            }
        } else {
            leader_map.insert(inst, inst);
        }
    }

    if let Some(children) = dom_children.get(&bb) {
        for &child in children {
            visit_dom_tree(child, data, scoped_table, leader_map, replacements, dom_children);
        }
    }

    scoped_table.leave_scope();
}

#[cfg(test)]
mod tests {
    use koopa::back::koopa::Visitor as KoopaVisitor;
    use koopa::back::{NameManager, Visitor};
    use koopa::front::Driver;
    use koopa::opt::FunctionPass;

    use super::*;
    use crate::passes::dce::DeadCodeElimination;

    fn apply_pass(ir_text: &str, simplify: bool, debug_on: bool) {
        let driver = Driver::from(ir_text);
        let mut program = driver.generate_program().unwrap();
        let func_id = *program.funcs().keys().next().unwrap();
        let func_data = program.func_mut(func_id);
        let mut pass = GVN;
        pass.run_on(func_id, func_data);

        if simplify {
            let mut pass = DeadCodeElimination::new();
            pass.run_on(func_id, func_data);
        }

        if debug_on {
            let mut visitor = KoopaVisitor;
            let mut nm = NameManager::new();
            let mut w = std::io::stdout();
            visitor.visit(&mut w, &mut nm, &program).unwrap();
        }
    }

    #[test]
    fn test_simple() {
        let ir = r#"
fun @test(): i32 {
%entry:
  %a = add 1, 1
  %a1 = add 1, 1
  %b = add %a, %a1 
  %c = add %a, %a1 // <-- %c is duplicated, should be removed after GVN + DCE

  %d = add %c, 1   // <-- %c is duplicated, should be replaced with %b

  ret %d
}
        "#;

        apply_pass(ir, true, true);
    }

    #[test]
    fn test_commutativity() {
        let ir = r#"
    fun @test(%a: i32, %b: i32): i32 {
    %entry:
      %0 = add %a, %b
      %1 = add %b, %a       // equival to %0
      %2 = mul %0, %1       // should be %0 * %0
      ret %2
    }
    "#;
        apply_pass(ir, true, true);
    }

    #[test]
    fn test_global_redundancy() {
        let ir = r#"
    fun @test(%cond: i32, %a: i32, %b: i32): i32 {
    %entry:
      %val1 = add %a, %b
      br %cond, %then, %else
    %then:
      %val2 = add %a, %b        // <-- equal to %val
      ret %val2                 // <-- should be replaced with %val
    %else:
      ret 0
    }
    "#;
        apply_pass(ir, true, true);
    }

    #[test]
    fn test_cascading_replacement() {
        let ir = r#"
    fun @test(%a: i32, %b: i32): i32 {
    %entry:
      %0 = add %a, %b
      %1 = add %a, %b       // dup
      %2 = add %0, 1        // 
      %3 = add %1, 1        // dup
      ret %3
    }
    "#;
        apply_pass(ir, true, true);
    }

    #[test]
    fn test_block_param_redundancy() {
        let ir = r#"
    fun @test(%cond: i32, %a: i32, %b: i32): i32 {
    %entry:
      %val = add %a, %b
      br %cond, %block_1(%val), %block_2(%val)

    %block_1(%p1: i32):
      jump %merge(%p1)

    %block_2(%p2: i32):
      jump %merge(%p2)

    %merge(%res: i32):
      %v_extra = add %a, %b // 应该替换为 %val
      ret %v_extra
    }
    "#;
        apply_pass(ir, true, true);
    }
}
