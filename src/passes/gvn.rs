use std::collections::HashMap;

use koopa::ir::builder::ValueBuilder;
use koopa::ir::{BasicBlock, BinaryOp, FunctionData, Value, ValueKind};
use koopa::opt::FunctionPass;
use rustc_hash::{FxHashMap, FxHashSet};
use smallvec::SmallVec;

use crate::graph::dom_tree::DomTree;
use crate::graph::traverse::reverse_post_order;
use crate::utils::replace_operands;

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
enum ExprOp {
    /// binary operation
    Bin(BinaryOp),
}

impl ExprOp {
    fn is_commutive(&self) -> bool {
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

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct EqClassId(u32);

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
struct ExprData {
    operands: SmallVec<[EqClassId; 3]>,
    op: ExprOp,
}

impl ExprData {
    fn canonicalize(&mut self) {
        if self.op.is_commutive() {
            self.operands.sort();
        }
    }
}

#[derive(Clone, Debug)]
struct EquivalentClass {
    /// leader of the the class,
    /// must dominates all other members
    leader: Value,
    /// member of the e-class, includes the leader itself
    members: FxHashSet<Value>,
}

impl EquivalentClass {
    /// init the equivalent class with only one member(itself)
    fn new(value: Value) -> Self {
        let values = FxHashSet::from_iter([value]);
        Self { members: values, leader: value }
    }

    /// add a new value to the dominance class, returns the new leader
    fn insert(&mut self, value: Value, data: &FunctionData, dom_tree: &DomTree<BasicBlock>) {
        if self.members.contains(&value) {
            return;
        }

        self.members.insert(value);
        let orig_leader_bb = data.layout().parent_bb(self.leader);
        let new_leader_bb = data.layout().parent_bb(value);

        if let (Some(old), Some(new)) = (orig_leader_bb, new_leader_bb) {
            // new value's BB must strictly old's
            // so we could keep the leader unchanged if the two BB is the same
            if dom_tree.strict_dominates(new, old) {
                self.leader = value;
            }
        }
    }
}

struct ExprTable {
    /// from expr to the equivalent class id
    exprs: FxHashMap<ExprData, EqClassId>,

    value_to_eclass: FxHashMap<Value, EqClassId>,

    /// from equivalent class id to its actual data
    equivalent_classes: FxHashMap<EqClassId, EquivalentClass>,

    /// next equivalent class id
    next_id: u32,
}

impl ExprTable {
    fn new() -> Self {
        Self {
            exprs: FxHashMap::default(),
            value_to_eclass: FxHashMap::default(),
            equivalent_classes: FxHashMap::default(),
            next_id: 0,
        }
    }

    fn next_id(&mut self) -> EqClassId {
        let id = self.next_id;
        self.next_id += 1;
        EqClassId(id)
    }

    fn get_or_create_id(&mut self, val: Value) -> EqClassId {
        if let Some(&id) = self.value_to_eclass.get(&val) {
            id
        } else {
            let id = self.next_id();
            self.value_to_eclass.insert(val, id);
            self.equivalent_classes.insert(id, EquivalentClass::new(val));
            id
        }
    }

    fn process_instruction(
        &mut self,
        inst: Value,
        data: &FunctionData,
        dom_tree: &DomTree<BasicBlock>,
    ) {
        let inst_data = data.dfg().value(inst);
        if !matches!(inst_data.kind(), ValueKind::Binary(_)) {
            return;
        }

        let operands: SmallVec<[EqClassId; 3]> =
            inst_data.kind().value_uses().map(|v| self.get_or_create_id(v)).collect();

        let op = match inst_data.kind() {
            ValueKind::Binary(b) => ExprOp::Bin(b.op()),
            _ => unreachable!(),
        };

        let mut expr = ExprData { operands, op };
        expr.canonicalize();

        let class_id = if let Some(&existing_id) = self.exprs.get(&expr) {
            let eclass = self.equivalent_classes.get_mut(&existing_id).unwrap();
            eclass.insert(inst, data, dom_tree);
            existing_id
        } else {
            let new_id = self.next_id();
            self.exprs.insert(expr, new_id);
            self.equivalent_classes.insert(new_id, EquivalentClass::new(inst));
            new_id
        };

        self.value_to_eclass.insert(inst, class_id);
    }

    fn leader(&self, value: Value) -> Option<Value> {
        let eclass_id = self.value_to_eclass.get(&value)?;
        let eclass = self.equivalent_classes.get(eclass_id)?;
        Some(eclass.leader)
    }
}

pub struct GVN;

/// TODO: fold block params
impl FunctionPass for GVN {
    fn run_on(&mut self, _func: koopa::ir::Function, data: &mut FunctionData) {
        let Some(entry) = data.layout().entry_bb() else {
            return;
        };

        let dom_tree = DomTree::build(entry, data);

        let mut expr_table = ExprTable::new();

        let rpo: Vec<BasicBlock> = reverse_post_order(data, entry);

        for bb in &rpo {
            let insts =
                data.layout().bbs().node(bb).unwrap().insts().keys().copied().collect::<Vec<_>>();

            for inst in insts {
                expr_table.process_instruction(inst, data, &dom_tree);

                if let Some(leader) = expr_table.leader(inst)
                    && inst != leader
                {
                    let v_map = HashMap::from([(inst, leader)]);
                    for usage in data.dfg().value(inst).used_by().clone() {
                        let mut value_kind = data.dfg().value(usage).clone();
                        assert!(replace_operands(&mut value_kind, &v_map));
                        data.dfg_mut().replace_value_with(usage).raw(value_kind);
                    }
                }
            }
        }
    }
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
