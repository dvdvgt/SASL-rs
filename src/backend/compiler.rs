use crate::error::SaslError;
use crate::frontend::ast::Ast;

use super::abstractor::Abstractor;

pub struct Compiler {
    ast: Ast,
    /// Reduction graph created while compiling
    rg: Ast
}

impl Compiler {
    pub fn new(ast: Ast) -> Self {
        Self { ast, rg: Ast::default() }
    }

    fn throw_compiler_error(msg: &str) -> SaslError {
        SaslError::CompilerError {
            msg: msg.to_string(),
        }
    }

    /// Free all occurences of all parameters of a given definition.
    fn free_occurences_global_def(&mut self) -> Result<(), SaslError> {
        for (name, (p, body)) in self.ast.global_defs.iter() {
            // Only functions need to be freeded of parameter names
            if let Some(params) = p {
                let new_body = Abstractor::new(
                p,
                ).abstract_ids(body.clone())?;

                self.rg.global_defs.insert(
                name.to_string(),
                (p.clone(), new_body)
                );
            } else {
                self.rg.global_defs.insert(name.to_string(), (p.clone(), body.clone()));
            }
        }
        Ok(())
    }

    pub fn compile(&mut self) -> Result<&mut Ast, SaslError> {
        self.free_occurences_global_def()?;
        // TODO handle where in body
        self.rg.body = Abstractor::new(&None).abstract_ids(self.ast.body.clone())?;
        Ok(&mut self.rg)
    }
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
            "def incr x = 1 + y where y = 2 * x \
            def plus x y = x + y \
            def const = 5*3 \
            def rec x = if x = 0 then 0 else rec (x-1)
            def g x = f x where f x = f y
            . 1 where f x = g x; g x = f x"
        );
        let mut compiler = Compiler::new(ast);
        let rg = compiler.compile().unwrap();
        //println!("{:?}", &rg);

        assert_eq!(
            rg.global_defs.get("incr").unwrap().1.to_string(),
            "((S @ ((S @ (K @ +)) @ (K @ Number:1))) @ I)"
        );
        assert_eq!(
            rg.global_defs.get("null").unwrap().1.to_string(),
            "((S @ ((S @ (K @ =)) @ I)) @ (K @ nil))"
        );
        assert_eq!(rg.global_defs.get("const").unwrap().1.to_string(), "((* @ Number:5) @ Number:3)");
        assert_eq!(
            rg.global_defs.get("plus").unwrap().1.to_string(),
            "((S @ ((S @ (K @ S)) @ ((S @ ((S @ (K @ S)) @ ((S @ (K @ K)) @ (K @ +)))) @ ((S @ (K @ K)) @ I)))) @ (K @ I))"
        );

        let mut viz = Visualizer::new("g", false);
        viz.visualize_ast(
            &rg
        );
        viz.write_to_pdf("test.pdf");
        assert_eq!(
            rg.global_defs.get("rec").unwrap().1.to_string(),
            ""
        )
    }
}