use crate::error::SaslError;
use crate::frontend::ast::{self, Ast, AstNode, Identifier, Params};

pub struct Compiler<'a> {
    ast: &'a mut Ast,
}

impl<'a> Compiler<'a> {
    pub fn new(ast: &'a mut Ast) -> Self {
        Self { ast }
    }

    fn throw_compiler_error(msg: &str) -> SaslError {
        SaslError::CompilerError {
            msg: msg.to_string(),
        }
    }

    /// Free all occurences of all parameters of a given definition.
    fn free_occurences(&mut self, id: &str) {
        /// Free all occurences of one parameter from a given AST subtree.
        fn free_occurence(param_name: &str, subtree: AstNode) -> Result<AstNode, SaslError> {
            match subtree {
                AstNode::Constant(_)
                | AstNode::S
                | AstNode::K
                | AstNode::I
                | AstNode::Builtin(_) => Ok(ast::apply2(AstNode::K, subtree)),
                AstNode::Ident(ref n) => {
                    if n == param_name {
                        Ok(AstNode::I)
                    } else {
                        Ok(ast::apply2(AstNode::K, subtree))
                    }
                }
                AstNode::App(f, a) => Ok(ast::apply3(
                    AstNode::S,
                    free_occurence(param_name, *f)?,
                    free_occurence(param_name, *a)?,
                )),
                _ => Err(Compiler::throw_compiler_error("Erroneous AST.")),
            }
        }
        // Remove AST of the definition, modify it and reinsert it.
        let (params, mut body) = self.ast.global_defs.remove(id).unwrap();
        // Only free variable occurences if the definition has parameters.
        if let Some(ref params_vec) = params {
            for param_name in params_vec.iter().rev() {
                body = free_occurence(param_name, body).unwrap();
            }
            self.ast.global_defs.insert(id.to_string(), (params, body));
        }
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
    fn test_free_occurences() {
        let mut ast = parse_to_ast("def incr x = 1 + x . 1");
        let mut compiler = Compiler::new(&mut ast);
        compiler.free_occurences("incr");
        assert_eq!(
            ast.global_defs.get("incr").unwrap().1.to_string(),
            "((S @ ((S @ (K @ +)) @ (K @ Number:1))) @ I)"
        );

        let mut ast = parse_to_ast("def null xs = xs = nil . 1");
        let mut compiler = Compiler::new(&mut ast);
        compiler.free_occurences("null");
        assert_eq!(
            ast.global_defs.get("null").unwrap().1.to_string(),
            "((S @ ((S @ (K @ =)) @ I)) @ (K @ nil))"
        );

        let mut ast = parse_to_ast("def plus x y = x + y . 1");
        let mut compiler = Compiler::new(&mut ast);
        compiler.free_occurences("plus");
        let mut viz = Visualizer::new("g", false);
        viz.visualize_ast_nodes(&ast.global_defs.get("plus").unwrap().1);
        viz.write_to_pdf("incr.pdf");
        viz.write_to_dot("incr.dot");
        assert_eq!(ast.global_defs.get("plus").unwrap().1.to_string(), "");
    }
}
