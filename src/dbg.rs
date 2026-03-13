use core::fmt;

use koopa::ir::dfg::DataFlowGraph;
use koopa::ir::{BasicBlock, Value, ValueKind};

/// A displayable helper for [`ValueKind`].
pub struct ValueKindDisplay<'a> {
    pub kind: &'a ValueKind,
    pub dfg: &'a DataFlowGraph,
}

impl<'a> ValueKindDisplay<'a> {
    pub fn new(dfg: &'a DataFlowGraph, value: Value) -> Self {
        let kind = dfg.value(value).kind();
        Self { kind, dfg }
    }
}

pub trait ValueKindExt {
    fn display<'a>(&'a self, dfg: &'a DataFlowGraph) -> ValueKindDisplay<'a>;
}

impl ValueKindExt for ValueKind {
    fn display<'a>(&'a self, dfg: &'a DataFlowGraph) -> ValueKindDisplay<'a> {
        ValueKindDisplay { kind: self, dfg }
    }
}

impl fmt::Display for ValueKindDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.kind {
            ValueKind::Integer(v) => write!(f, "{}", v.value()),
            ValueKind::ZeroInit(_) => f.write_str("zeroinit"),
            ValueKind::Undef(_) => f.write_str("undef"),
            ValueKind::Aggregate(v) => {
                f.write_str("{")?;
                for (i, elem) in v.elems().iter().enumerate() {
                    if i != 0 {
                        f.write_str(", ")?;
                    }
                    write!(f, "{}", self.dfg.value(*elem).kind().display(self.dfg))?;
                }
                f.write_str("}")
            }
            ValueKind::FuncArgRef(v) => write!(f, "arg {}", v.index()),
            ValueKind::BlockArgRef(v) => write!(f, "block arg {}", v.index()),
            ValueKind::Alloc(_) => f.write_str("alloc"),
            ValueKind::GlobalAlloc(v) => {
                let init = self.dfg.value(v.init());
                write!(f, "alloc {}, ", init.ty())?;
                write!(f, "{}", init.kind().display(self.dfg))
            }
            ValueKind::Load(v) => {
                f.write_str("load ")?;
                self.fmt_value(v.src(), f)
            }
            ValueKind::Store(v) => {
                f.write_str("store ")?;
                self.fmt_value(v.value(), f)?;
                f.write_str(", ")?;
                self.fmt_value(v.dest(), f)
            }
            ValueKind::GetPtr(v) => {
                f.write_str("getptr ")?;
                self.fmt_value(v.src(), f)?;
                f.write_str(", ")?;
                self.fmt_value(v.index(), f)
            }
            ValueKind::GetElemPtr(v) => {
                f.write_str("getelemptr ")?;
                self.fmt_value(v.src(), f)?;
                f.write_str(", ")?;
                self.fmt_value(v.index(), f)
            }
            ValueKind::Binary(v) => {
                write!(f, "{} ", v.op())?;
                self.fmt_value(v.lhs(), f)?;
                f.write_str(", ")?;
                self.fmt_value(v.rhs(), f)
            }
            ValueKind::Branch(v) => {
                f.write_str("br ")?;
                self.fmt_value(v.cond(), f)?;
                f.write_str(", ")?;
                self.fmt_bb_target(v.true_bb(), v.true_args(), f)?;
                f.write_str(", ")?;
                self.fmt_bb_target(v.false_bb(), v.false_args(), f)
            }
            ValueKind::Jump(v) => {
                f.write_str("jump ")?;
                self.fmt_bb_target(v.target(), v.args(), f)
            }
            ValueKind::Call(v) => {
                // we cannot access the actual function name here
                // unless we have the callgraph
                write!(f, "call ...(")?;
                for (i, arg) in v.args().iter().enumerate() {
                    if i != 0 {
                        f.write_str(", ")?;
                    }
                    self.fmt_value(*arg, f)?;
                }
                f.write_str(")")
            }
            ValueKind::Return(v) => {
                f.write_str("ret")?;
                if let Some(val) = v.value() {
                    f.write_str(" ")?;
                    self.fmt_value(val, f)?;
                }
                Ok(())
            }
        }
    }
}

impl ValueKindDisplay<'_> {
    fn fmt_value(&self, value: Value, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let data = self.dfg.value(value);
        if data.kind().is_const() {
            write!(f, "{}", data.kind().display(self.dfg))
        } else {
            match data.name() {
                Some(name) => f.write_str(name),
                None => write!(f, "%{:x?}", value),
            }
        }
    }

    fn fmt_bb_target(
        &self,
        bb: BasicBlock,
        args: &[Value],
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result {
        let data = self.dfg.bb(bb);
        match data.name() {
            Some(name) => f.write_str(name),
            None => write!(f, "%{:?}", bb),
        }?;
        if !args.is_empty() {
            f.write_str("(")?;
            for (i, arg) in args.iter().enumerate() {
                if i != 0 {
                    f.write_str(", ")?;
                }
                self.fmt_value(*arg, f)?;
            }
            f.write_str(")")?;
        }
        Ok(())
    }
}
