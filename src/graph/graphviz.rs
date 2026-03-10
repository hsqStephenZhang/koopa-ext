use std::fmt;

use koopa::ir::dfg::DataFlowGraph;
use koopa::ir::{BasicBlock, FunctionData, Value, ValueKind};

use crate::graph::graph::Successors;

/// The `graphviz` function in Rust generates a Graphviz representation of a function's control flow
/// graph with optional instruction details.
///
/// Arguments:
///
/// * `func_data`: The `func_data` parameter is a reference to `FunctionData`, which is used to gather
/// information about a function such as basic block layout, data flow graph, and successors. This
/// function `graphviz` generates a Graphviz representation of the function control flow graph based on
/// the provided `func_data
/// * `no_body`: The `no_body` parameter is a boolean flag that determines whether to include the body
/// of each basic block in the graph visualization. If `no_body` is set to `true`, the graph will only
/// display the basic block names and parameters without showing the instructions inside each block. If
/// set to `
///
/// Returns:
///
/// The function `graphviz` returns a `String` containing the DOT representation of a graph for the
/// given `FunctionData`. The graph represents the control flow of the function, including basic blocks,
/// instructions, and their connections.
pub fn graphviz(func_data: &FunctionData, no_body: bool) -> String {
    let mut dot = String::from("digraph G {\n");
    dot.push_str("  node [shape=record];\n");

    for (bb, _) in func_data.layout().bbs() {
        let bb_data = func_data.dfg().bb(*bb);
        let name = bb_data.name().as_deref().unwrap_or("unnamed");

        let mut params = String::new();
        if !bb_data.params().is_empty() {
            params.push('(');
            for (i, &p) in bb_data.params().iter().enumerate() {
                if i > 0 {
                    params.push_str(", ");
                }
                let p_data = func_data.dfg().value(p);
                if let Some(p_name) = p_data.name() {
                    params.push_str(p_name);
                } else {
                    params.push_str(&format!("%{:x?}", p));
                }
            }
            params.push(')');
        }

        let mut label = format!("{{ {}{} | ", name, params);

        if !no_body {
            for inst in func_data.layout().bbs().node(bb).unwrap().insts() {
                let data = func_data.dfg().value(*inst.0);
                if !data.ty().is_unit() {
                    if let Some(name) = data.name() {
                        label.push_str(&format!("{} = ", name));
                    } else {
                        label.push_str(&format!("%{:x?} = ", inst.0));
                    }
                }
                let display = ValueKindDisplay { kind: data.kind(), dfg: func_data.dfg() };
                label.push_str(&format!("{} \\l", display));
            }
        }

        label.push_str(" }");

        dot.push_str(&format!("  \"bb_{:?}\" [label=\"{}\"];\n", bb, label));

        for succ in func_data.succs(*bb) {
            dot.push_str(&format!("  \"bb_{:?}\" -> \"bb_{:?}\";\n", bb, succ));
        }
    }

    dot.push_str("}\n");
    dot
}

/// The function `graphviz_cfg` generates a Graphviz representation of the control flow graph for a
/// given function.
///
/// Arguments:
///
/// * `func_data`: It looks like you are trying to create a Control Flow Graph using Graphviz for a
/// given function. To complete the function `graphviz_cfg`, you can use the `FunctionData` parameter to
/// generate the necessary graph representation.
///
/// Returns:
///
/// The `graphviz_cfg` function is returning a `String` value, which is the result of calling the
/// `graphviz` function with the `func_data` parameter and `true` as the second argument.
pub fn graphviz_cfg(func_data: &FunctionData) -> String {
    graphviz(func_data, true)
}

/// A displayable helper for [`ValueKind`].
pub struct ValueKindDisplay<'a> {
    pub kind: &'a ValueKind,
    pub dfg: &'a DataFlowGraph,
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
                write!(f, "call {}(", "...")?;
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

#[cfg(test)]
mod test_viz {
    use koopa::front::Driver;

    use super::*;

    #[test]
    fn test_simple() {
        let src = r#"
fun @test(): i32 {
%entry:
  %0 = add 1, 2
  br %0, %then, %end

%then:
  jump %end

%end:
  ret %0
}
"#;
        let driver: Driver<_> = src.into();
        let prog = driver.generate_program().unwrap();
        let func = prog.funcs().values().next().unwrap();
        let dot = graphviz(func, true);
        println!("{}", dot);
        assert!(dot.contains("digraph G"));
        assert!(dot.contains("bb_"));
    }

    #[test]
    fn test_preds_succs() {
        let src = r#"
decl @getint(): i32

fun @test(): i32 {
%entry:
  %0 = call @getint()
  %1 = call @getint()
  jump %while_cond_2(0, 0)

%while_cond_2(%2: i32, %3: i32):
  %4 = lt %3, %1
  br %4, %while_body_3, %while_end_1

%while_body_3:
  jump %while_cond_4(%2, 0)

%while_end_1:
  ret %2

%while_cond_4(%5: i32, %6: i32):
  %7 = lt %6, %0
  br %7, %while_body_6, %while_end_5

%while_body_6:
  %8 = add %5, %3
  %9 = add %8, %6
  %10 = add %6, 1
  jump %while_cond_4(%9, %10)

%while_end_5:
  %11 = add %3, 1
  jump %while_cond_2(%5, %11)
}
"#;
        let driver: Driver<_> = src.into();
        let prog = driver.generate_program().unwrap();
        let func = prog.funcs().values().find(|bb| bb.name() == "@test").unwrap();

        let viz = graphviz(func, false);

        println!("{}", viz);
    }
}
