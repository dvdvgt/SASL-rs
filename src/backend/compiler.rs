use crate::error::SaslError;
use crate::frontend::ast::Ast;
use super::abstractor::Abstractor;

pub fn compile(ast: &Ast) -> Result<Ast, SaslError> {
    let mut rg = Ast::new();
    for (name, (p, body)) in ast.global_defs.iter() {
        // Only functions need to be freeded of parameter names
        if let Some(_) = p {
            let new_body = Abstractor::new(p).abstract_ids(body.clone())?;
            rg.global_defs.insert(name.clone(), (p.clone(), new_body));
        } else {
            rg.global_defs.insert(name.clone(), (p.clone(), body.clone()));
        }
    }
    // Handle main expression
    let new_main_body = Abstractor::new(&None).abstract_ids(ast.body.clone())?;
    rg.body = new_main_body;
    Ok(rg)
}


#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend::{lexer::*, parser::*, visualize::Visualizer};

    fn parse_to_ast(code: &str) -> Ast {
        Parser::new(Lexer::new(code).tokenize().unwrap())
            .parse()
            .unwrap()
    }

    #[test]
    fn test_free_occurences_global_def() {
        let ast = parse_to_ast(
            "def incr x = 1 + x \
            def plus x y = x + y \
            def null xs = xs = nil \
            def const = 5*3 \
            def rec x = if x = 0 then 0 else rec (x-1)
            def g x = f x where f x = y where y = x + 1
            . a + 2 where a = 3"
        );
        let ast = compile(&ast).unwrap();
        println!("{:?}", &ast.global_defs.keys());

        assert_eq!(
            ast.global_defs.get("incr").unwrap().1.to_string(),
            "((S @ ((S @ (K @ +)) @ (K @ Number:1))) @ I)"
        );
        assert_eq!(
            ast.global_defs.get("null").unwrap().1.to_string(),
            "((S @ ((S @ (K @ =)) @ I)) @ (K @ nil))"
        );
        assert_eq!(ast.global_defs.get("const").unwrap().1.to_string(), "((* @ Number:5) @ Number:3)");
        assert_eq!(
            ast.global_defs.get("plus").unwrap().1.to_string(),
            "((S @ ((S @ (K @ S)) @ ((S @ ((S @ (K @ S)) @ ((S @ (K @ K)) @ (K @ +)))) @ ((S @ (K @ K)) @ I)))) @ (K @ I))"
        );

        let mut viz = Visualizer::new("g", false);
        viz.visualize_ast(
            &ast
        );
        viz.write_to_pdf("test.pdf");
        assert_eq!(
            ast.global_defs.get("rec").unwrap().1.to_string(),
            "((S @ ((S @ ((S @ (K @ cond)) @ ((S @ ((S @ (K @ =)) @ I)) @ (K @ Number:0)))) @ (K @ Number:0))) @ ((S @ (K @ Id:rec)) @ ((S @ ((S @ (K @ -)) @ I)) @ (K @ Number:1))))"
        );
    }
}