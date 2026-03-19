use koopa::ir::{BasicBlock, BinaryOp, FunctionData, Value, ValueKind};
use rustc_hash::FxHashMap;

use crate::graph::loops::{Loop, LoopsAnalysis};
use crate::graph::terminator::TerminatorExt;
use crate::utils::is_loop_invariant;

#[derive(Debug, Clone)]
pub enum SCEVExpr {
    /// an invariant for a loop
    Invariant(InVarExpr),
    /// an affine/linear expression like `value = base + i * step`
    /// where i is the loop count,
    AddRec(AffineAddRec),
}

impl SCEVExpr {
    pub fn add_expr(lhs: SCEVExpr, rhs: SCEVExpr) -> Option<Self> {
        match (lhs, rhs) {
            // Invariant + Invariant -> Invariant
            (SCEVExpr::Invariant(l), SCEVExpr::Invariant(r)) => {
                Some(SCEVExpr::Invariant(InVarExpr::bin(l, r, BinaryOp::Add)))
            }
            // AddRec + Invariant -> AddRec(base + inv, step)
            (SCEVExpr::AddRec(rec), SCEVExpr::Invariant(inv))
            | (SCEVExpr::Invariant(inv), SCEVExpr::AddRec(rec)) => {
                let new_base = InVarExpr::bin(rec.base, inv, BinaryOp::Add);
                Some(SCEVExpr::AddRec(AffineAddRec::new(new_base, rec.step)))
            }
            // AddRec + AddRec -> AddRec(base + base, step + step)
            (SCEVExpr::AddRec(rec1), SCEVExpr::AddRec(rec2)) => {
                Some(SCEVExpr::AddRec(AffineAddRec::add(rec1, rec2)))
            }
        }
    }

    pub fn sub_expr(lhs: SCEVExpr, rhs: SCEVExpr) -> Option<Self> {
        match (lhs, rhs) {
            // Invariant - Invariant -> Invariant
            (SCEVExpr::Invariant(l), SCEVExpr::Invariant(r)) => {
                Some(SCEVExpr::Invariant(InVarExpr::bin(l, r, BinaryOp::Sub)))
            }
            // AddRec - Invariant -> AddRec(base - inv, step)
            (SCEVExpr::AddRec(rec), SCEVExpr::Invariant(inv)) => {
                let new_base = InVarExpr::bin(rec.base, inv, BinaryOp::Sub);
                Some(SCEVExpr::AddRec(AffineAddRec::new(new_base, rec.step)))
            }
            // Invariant - AddRec -> AddRec(inv - base, -step)
            (SCEVExpr::Invariant(inv), SCEVExpr::AddRec(rec)) => {
                let new_base = InVarExpr::bin(inv, rec.base, BinaryOp::Sub);
                Some(SCEVExpr::AddRec(AffineAddRec::new(new_base, rec.step.neg())))
            }
            // AddRec - AddRec' -> AddRec(base - base', step - step')
            (SCEVExpr::AddRec(rec1), SCEVExpr::AddRec(rec2)) => {
                Some(SCEVExpr::AddRec(AffineAddRec::sub(rec1, rec2)))
            }
        }
    }

    pub fn mul_expr(lhs: SCEVExpr, rhs: SCEVExpr) -> Option<Self> {
        match (lhs, rhs) {
            // Invariant * Invariant -> Invariant
            (SCEVExpr::Invariant(l), SCEVExpr::Invariant(r)) => {
                Some(SCEVExpr::Invariant(InVarExpr::bin(l, r, BinaryOp::Mul)))
            }
            // AddRec * Invariant -> AddRec(base * inv, step * inv)
            (SCEVExpr::AddRec(rec), SCEVExpr::Invariant(inv))
            | (SCEVExpr::Invariant(inv), SCEVExpr::AddRec(rec)) => {
                Some(SCEVExpr::AddRec(AffineAddRec::bin(rec, inv, BinaryOp::Mul)))
            }
            (SCEVExpr::AddRec(_), SCEVExpr::AddRec(_)) => None,
        }
    }

    pub fn as_const(&self) -> Option<Constant> {
        if let SCEVExpr::Invariant(InVarExpr::Constant(c)) = self { Some(*c) } else { None }
    }

    pub fn as_addrec(&self) -> Option<&AffineAddRec> {
        if let Self::AddRec(v) = self { Some(v) } else { None }
    }
}

/// `val = base + i * step` or `next = next + step where init vlaue is base`
/// or it could be a deductive, like `V3 = V1 + V2` where V1 and V2 are both
/// addrec expression
#[derive(Debug, Clone)]
pub struct AffineAddRec {
    pub base: InVarExpr,
    pub step: InVarExpr,
}

#[allow(clippy::should_implement_trait)]
impl AffineAddRec {
    pub fn new(base: InVarExpr, step: InVarExpr) -> Self {
        Self { base, step }
    }

    /// val = base + i * step
    /// val' = base' + i * step'
    /// val'' = (base + base') + i * (step + step')
    pub fn add(lhs: Self, rhs: Self) -> Self {
        let base = InVarExpr::bin(lhs.base, rhs.base, BinaryOp::Add);
        let step = InVarExpr::bin(lhs.step, rhs.step, BinaryOp::Add);

        Self { base, step }
    }

    /// val = base + i * step
    /// val' = base' + i * step'
    /// val'' = (base - base') + i * (step - step')
    pub fn sub(lhs: Self, rhs: Self) -> Self {
        let base = InVarExpr::bin(lhs.base, rhs.base, BinaryOp::Sub);
        let step = InVarExpr::bin(lhs.step, rhs.step, BinaryOp::Sub);

        Self { base, step }
    }

    /// val = base + i * step
    /// val' = (base OP rhs) + i * (step OP rhs)
    pub fn bin(lhs: Self, rhs: InVarExpr, op: BinaryOp) -> Self {
        let base = InVarExpr::bin(lhs.base.clone(), rhs.clone(), op);
        let step = InVarExpr::bin(lhs.step.clone(), rhs.clone(), op);

        Self { base, step }
    }
}

#[derive(Clone, Debug)]
pub enum InVarExpr {
    Constant(Constant),
    Value(Value),
    Binary { lhs: Box<InVarExpr>, rhs: Box<InVarExpr>, op: BinaryOp },
    Neg(Box<InVarExpr>),
}

impl InVarExpr {
    pub fn const_inv(c: Constant) -> Self {
        Self::Constant(c)
    }

    pub fn invar(v: Value) -> Self {
        Self::Value(v)
    }

    pub fn bin(lhs: InVarExpr, rhs: InVarExpr, op: BinaryOp) -> Self {
        match (&lhs, &rhs) {
            (Self::Constant(v1), Self::Constant(v2)) => {
                Self::Constant(Constant::eval(v1, v2, op).unwrap())
            }
            _ => Self::Binary { lhs: Box::new(lhs), rhs: Box::new(rhs), op },
        }
    }

    #[allow(clippy::should_implement_trait)]
    pub fn neg(self) -> Self {
        Self::Neg(Box::new(self))
    }

    pub fn as_const(&self) -> Option<Constant> {
        if let Self::Constant(c) = self { Some(*c) } else { None }
    }
}

#[derive(Clone, Copy, Debug)]
pub struct Constant {
    val: i32,
}

impl Constant {
    pub fn value(&self) -> i32 {
        self.val
    }

    fn eval(l: &Self, r: &Self, op: BinaryOp) -> Option<Self> {
        match op {
            BinaryOp::NotEq => Some((l.value() != r.value()) as i32),
            BinaryOp::Eq => Some((l.value() == r.value()) as i32),
            BinaryOp::Gt => Some((l.value() > r.value()) as i32),
            BinaryOp::Lt => Some((l.value() < r.value()) as i32),
            BinaryOp::Ge => Some((l.value() >= r.value()) as i32),
            BinaryOp::Le => Some((l.value() <= r.value()) as i32),
            BinaryOp::Add => Some(l.value() + r.value()),
            BinaryOp::Sub => Some(l.value() - r.value()),
            BinaryOp::Mul => Some(l.value() * r.value()),
            BinaryOp::Div => (r.value() != 0).then(|| l.value() / r.value()),
            BinaryOp::Mod => (r.value() != 0).then(|| l.value() % r.value()),
            BinaryOp::And => Some(l.value() & r.value()),
            BinaryOp::Or => Some(l.value() | r.value()),
            BinaryOp::Xor => Some(l.value() ^ r.value()),
            BinaryOp::Shl => Some(l.value() << r.value()),
            BinaryOp::Shr => Some((l.value() as u32 >> r.value()) as i32),
            BinaryOp::Sar => Some(l.value() >> r.value()),
        }
        .map(|val| Self { val })
    }
}

impl TryFrom<&ValueKind> for Constant {
    type Error = ();

    fn try_from(value: &ValueKind) -> Result<Self, Self::Error> {
        match value {
            ValueKind::Integer(integer) => Ok(Self { val: integer.value() }),
            ValueKind::ZeroInit(_) => Ok(Self { val: 0 }),
            _ => Err(()),
        }
    }
}

pub struct ScalarEvolutionAnalysis {
    info: FxHashMap<Loop, FxHashMap<Value, AffineAddRec>>,
}

impl Default for ScalarEvolutionAnalysis {
    fn default() -> Self {
        Self::new()
    }
}

impl ScalarEvolutionAnalysis {
    pub fn new() -> Self {
        Self { info: Default::default() }
    }

    pub fn compute(&mut self, data: &FunctionData, loops: &LoopsAnalysis<BasicBlock>) {
        for lp in loops.bottom_up() {
            let header = loops.loops()[&lp].header();
            let Some(preheader) = loops.preheader(data, lp) else {
                continue;
            };
            let latches = loops.latches(data, lp);
            if latches.len() != 1 {
                continue;
            }

            let latch = latches[0];

            let (_, term1_val) = data.terminator(preheader);
            let (_, term2_val) = data.terminator(latch);

            let Some(base_args) = term1_val.params(header) else {
                continue;
            };

            let Some(latch_args) = term2_val.params(header) else {
                continue;
            };

            let params = data.dfg().bb(header).params();
            // we wish to tell which BB param could be represented as an `AffineAddRec`
            for ((base, &param), next) in base_args.into_iter().zip(params).zip(latch_args) {
                let Some(base) = Self::get_loop_invariant(data, lp, loops, base) else {
                    continue;
                };
                let step: Option<InVarExpr> = match data.dfg().value(next).kind() {
                    ValueKind::Integer(_) | ValueKind::ZeroInit(_) => Some(InVarExpr::Constant(
                        Constant::try_from(data.dfg().value(next).kind()).unwrap(),
                    )),
                    ValueKind::Binary(binary) => {
                        if matches!(binary.op(), koopa::ir::BinaryOp::Add)
                            && (binary.lhs() == param || binary.rhs() == param)
                        {
                            let step =
                                if binary.lhs() == param { binary.rhs() } else { binary.lhs() };
                            Self::get_loop_invariant(data, lp, loops, step)
                        } else {
                            None
                        }
                    }
                    _ => None,
                };

                let Some(step) = step else {
                    continue;
                };

                let add_rec = AffineAddRec::new(base, step);
                self.info.entry(lp).or_default().insert(param, add_rec);
            }
        }
    }

    pub fn get_or_insert(
        &mut self,
        data: &FunctionData,
        loops: &LoopsAnalysis<BasicBlock>,
        lp: Loop,
        value: Value,
    ) -> Option<SCEVExpr> {
        // 1. cached
        if let Some(loop_info) = self.info.get(&lp)
            && let Some(add_rec) = loop_info.get(&value)
        {
            return Some(SCEVExpr::AddRec(add_rec.clone()));
        }

        // 2. invaraint
        if let Some(invar) = Self::get_loop_invariant(data, lp, loops, value) {
            return Some(SCEVExpr::Invariant(invar));
        }

        // 3. recursively compute
        let kind = data.dfg().value(value).kind();
        if let ValueKind::Binary(binary) = kind {
            let lhs_scev = self.get_or_insert(data, loops, lp, binary.lhs())?;
            let rhs_scev = self.get_or_insert(data, loops, lp, binary.rhs())?;

            match binary.op() {
                BinaryOp::Add => {
                    return SCEVExpr::add_expr(lhs_scev, rhs_scev);
                }
                BinaryOp::Sub => {
                    return SCEVExpr::sub_expr(lhs_scev, rhs_scev);
                }
                BinaryOp::Mul => {
                    return SCEVExpr::mul_expr(lhs_scev, rhs_scev);
                }
                _ => return None, // none linear expression
            }
        }

        None
    }

    fn get_loop_invariant(
        data: &FunctionData,
        lp: Loop,
        loops: &LoopsAnalysis<BasicBlock>,
        value: Value,
    ) -> Option<InVarExpr> {
        let value_kind = data
            .dfg()
            .values() // it might be a global value
            .get(&value)
            .map(|v| v.kind());
        if value_kind.map(|v| v.is_const()).unwrap_or_default() {
            Some(InVarExpr::Constant(Constant::try_from(value_kind.unwrap()).unwrap()))
        } else if is_loop_invariant(data, lp, loops, value) {
            Some(InVarExpr::Value(value))
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use koopa::front::Driver;
    use koopa::ir::{BasicBlock, Function, FunctionData};
    use koopa::opt::FunctionPass;

    use crate::ext::FunctionDataExt;
    use crate::graph::dom_tree::DomTree;
    use crate::graph::loops::LoopsAnalysis;
    use crate::graph::scalar_evolution::ScalarEvolutionAnalysis;
    use crate::passes::LoopSimplify;

    fn prepare(
        func: Function,
        data: &mut FunctionData,
    ) -> (DomTree<BasicBlock>, LoopsAnalysis<BasicBlock>) {
        let mut lp_simplify = LoopSimplify;
        lp_simplify.run_on(func, data);
        let entry = data.layout().entry_bb().unwrap();
        let dom_tree = DomTree::build(entry, data);
        let mut loops = LoopsAnalysis::new();
        loops.compute(data, entry, &dom_tree);

        (dom_tree, loops)
    }

    #[test]
    fn test_scev_i_and_sum() {
        // ```c
        // int sum = 0;
        // int i = 0;
        // while (i<10) {
        //     sum = sum + i++;
        // }
        // ```
        let src = r#"
        fun @test_scev(): i32 {
        %entry:
          jump %preheader

        %preheader:
          // %i 的 base 是 0, %sum 的 base 是 0
          jump %loop_header(0, 0)

        %loop_header(%i: i32, %sum: i32):
          %cmp = lt %i, 10
          br %cmp, %loop_body, %exit

        %loop_body:
          %next_i = add %i, 1        // <-- loop invaraint
          %next_sum = add %sum, %i   // <-- not a loop invariant
          jump %latch

        %latch:
          jump %loop_header(%next_i, %next_sum)

        %exit:
          ret %sum
        }
        "#;

        let driver: Driver<_> = src.into();
        let mut prog = driver.generate_program().unwrap();

        let (func, data) =
            prog.funcs_mut().iter_mut().find(|bb| bb.1.name() == "@test_scev").unwrap();

        let (_, loops) = prepare(*func, data);

        let mut scev_pass = ScalarEvolutionAnalysis::new();
        scev_pass.compute(data, &loops);
        let v = data.get_value_by_name("%next_i").unwrap();
        let header = data.get_bb_by_name("%loop_header").unwrap();
        let lp = loops.bb_to_loop()[&header];
        let expr_i = scev_pass.get_or_insert(data, &loops, lp, v);
        println!("{:?}", expr_i);
    }

    #[test]
    fn test_scev_div() {
        let src = r#"
        fun @test_scev(): i32 {
        %entry:
          jump %preheader

        %preheader:
          jump %loop_header(0)

        %loop_header(%i: i32):
          %cmp = lt %i, 10
          br %cmp, %loop_body, %exit

        %loop_body:
          %i_times_4 = mul %i, 4
          %offset = add %i_times_4, 1
          
          %next_i = add %i, 1
          jump %latch

        %latch:
          jump %loop_header(%next_i)

        %exit:
          ret %i
        }
        "#;

        let driver: Driver<_> = src.into();
        let mut prog = driver.generate_program().unwrap();

        let (func, data) =
            prog.funcs_mut().iter_mut().find(|bb| bb.1.name() == "@test_scev").unwrap();

        let (_, loops) = prepare(*func, data);
        let mut scev_pass = ScalarEvolutionAnalysis::new();
        scev_pass.compute(data, &loops);

        let lp = loops.loop_of(data.get_bb_by_name("%loop_header").unwrap()).unwrap();
        let offset_val = data.get_value_by_name("%offset").unwrap();
        let result = scev_pass.get_or_insert(data, &loops, lp, offset_val);
        println!("{:?}", result);
    }

    #[test]
    fn test_scev_addrec_plus_addrec() {
        // i = {0, +, 1}
        // j = {10, +, 2}
        // next_j = {12, +, 2}
        // l: {11, +, 2}
        // k: {10, +, 3}
        let src = r#"
        fun @test_addrec_add(): i32 {
        %entry:
          jump %preheader
        %preheader:
          jump %loop_header(0, 10)

        %loop_header(%i: i32, %j: i32):
          %cmp = lt %i, 10
          br %cmp, %loop_body, %exit

        %loop_body:
          %k = add %i, %j
          
          %next_i = add %i, 1
          %next_j = add %j, 2
          %l = sub %next_j, 1
          jump %latch

        %latch:
          jump %loop_header(%next_i, %next_j)

        %exit:
          ret %k
        }
        "#;

        let driver: Driver<_> = src.into();
        let mut prog = driver.generate_program().unwrap();

        let (func, data) =
            prog.funcs_mut().iter_mut().find(|bb| bb.1.name() == "@test_addrec_add").unwrap();

        let (_, loops) = prepare(*func, data);
        let mut scev_pass = ScalarEvolutionAnalysis::new();
        scev_pass.compute(data, &loops);

        let lp = loops.loop_of(data.get_bb_by_name("%loop_header").unwrap()).unwrap();

        let val = data.get_value_by_name("%k").unwrap();
        let result = scev_pass.get_or_insert(data, &loops, lp, val);
        println!("{:?}", result);

        let val = data.get_value_by_name("%l").unwrap();
        let result = scev_pass.get_or_insert(data, &loops, lp, val);
        println!("{:?}", result);
    }
}
