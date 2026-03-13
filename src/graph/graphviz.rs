use koopa::ir::FunctionData;

use crate::dbg::ValueKindDisplay;
use crate::graph::Successors;

/// The `graphviz` function in Rust generates a Graphviz representation of a function's control flow
/// graph with optional instruction details.
///
/// Arguments:
///
/// * `func_data`: The `func_data` parameter is a reference to `FunctionData`, which is used to gather
///   information about a function such as basic block layout, data flow graph, and successors. This
///   function `graphviz` generates a Graphviz representation of the function control flow graph based on
///   the provided `func_data
/// * `no_body`: The `no_body` parameter is a boolean flag that determines whether to include the body
///   of each basic block in the graph visualization. If `no_body` is set to `true`, the graph will only
///   display the basic block names and parameters without showing the instructions inside each block.
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
///   given function. To complete the function `graphviz_cfg`, you can use the `FunctionData` parameter to
///   generate the necessary graph representation.
///
/// Returns:
///
/// The `graphviz_cfg` function is returning a `String` value, which is the result of calling the
/// `graphviz` function with the `func_data` parameter and `true` as the second argument.
pub fn graphviz_cfg(func_data: &FunctionData) -> String {
    graphviz(func_data, true)
}

/// Generates a Graphviz representation of a function-level graph.
///
/// Parameters:
/// - `func_data`: Function information, including basic blocks, data-flow graph,
///   and successor relationships.
/// - `no_body`: If `true`, render only block names and parameters, without
///   instruction bodies.
///
/// Returns:
/// A `String` containing Graphviz DOT text.
//
pub fn graphviz_bb(func_data: &FunctionData, no_body: bool) -> String {
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

/// Generates a CFG-only Graphviz representation for the given function.
///
/// This uses `FunctionData` to build control-flow edges and block nodes,
/// and then renders the graph using the `graphviz` function.
pub fn graphviz_cfg_only(func_data: &FunctionData) -> String {
    graphviz(func_data, true)
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
