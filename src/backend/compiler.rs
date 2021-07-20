//! Contains a simple entry point function for starting the abstraction of global definitions as well as the main expression.

use super::abstractor::Abstractor;
use crate::error::SaslError;
use crate::frontend::ast::Ast;

/// Abstract all global definitions as well as the main body expression. The given
/// AST while be altered in-place.
pub fn compile(ast: &mut Ast) -> Result<(), SaslError> {
    for (_, (p, body)) in ast.global_defs.iter_mut() {
        // Abstract global functions as well as global constants since global
        // constants can contain a where which needs to be abstracted.
        Abstractor::new(p).abstract_ids(body)?;
    }
    // Handle main expression
    Abstractor::new(&None).abstract_ids(&mut ast.body)?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use std::ops::Deref;

    use super::*;
    use crate::frontend::{lexer::*, parser::*, visualize::Visualizer};

    fn parse_to_ast(code: &str) -> Ast {
        Parser::new(Lexer::new(code).tokenize().unwrap())
            .parse()
            .unwrap()
    }

    #[test]
    fn test_free_occurences_global_def() {
        let mut ast = parse_to_ast(
            "def incr x = 1 + x \
            def plus x y = x + y \
            def null xs = xs = nil \
            def const = 5*3 \
            def rec x = if x = 0 then 0 else rec (x-1)
            def g x = f x where f x = y where y = x + 1
            . a + 2 where a = 3",
        );
        compile(&mut ast).unwrap();
        println!("{:?}", &ast.global_defs.keys());

        assert_eq!(
            ast.global_defs
                .get("incr")
                .unwrap()
                .1
                .deref()
                .borrow()
                .to_string(),
            "((S @ ((S @ (K @ +)) @ (K @ 1))) @ I)"
        );
        assert_eq!(
            ast.global_defs
                .get("null")
                .unwrap()
                .1
                .deref()
                .borrow()
                .to_string(),
            "((S @ ((S @ (K @ =)) @ I)) @ (K @ nil))"
        );
        assert_eq!(
            ast.global_defs
                .get("const")
                .unwrap()
                .1
                .deref()
                .borrow()
                .to_string(),
            "((* @ 5) @ 3)"
        );
        assert_eq!(
            ast.global_defs.get("plus").unwrap().1.deref().borrow().to_string(),
            "((S @ ((S @ (K @ S)) @ ((S @ ((S @ (K @ S)) @ ((S @ (K @ K)) @ (K @ +)))) @ ((S @ (K @ K)) @ I)))) @ (K @ I))"
        );

        let mut viz = Visualizer::new("g", false);
        viz.visualize_ast(&ast);
        viz.write_to_pdf("test.pdf");
        assert_eq!(
            ast.global_defs
                .get("rec")
                .unwrap()
                .1
                .deref()
                .borrow()
                .to_string(),
            "((S @ ((S @ ((S @ (K @ cond)) @ ((S @ ((S @ (K @ =)) @ I)) @ (K @ 0)))) @ (K @ 0))) @ ((S @ (K @ Id:rec)) @ ((S @ ((S @ (K @ -)) @ I)) @ (K @ 1))))"
        );
    }
}
