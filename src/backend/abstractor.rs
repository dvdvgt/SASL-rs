//! This file contains the implementation of the compiler called `Abstractor'. It replaces all identifiers in
//! a expression with `S,K,I` combinators based on the rules defined by the SASL language.

use crate::ptr;
use crate::{
    error::SaslError,
    frontend::ast::{self, AstNode, AstNodePtr, Identifier, Op},
    T,
};
use std::collections::VecDeque;
use std::{cell::RefCell, rc::Rc};

type AbstractorResult = Result<AstNodePtr, SaslError>;

pub struct Abstractor<'a> {
    ids: &'a Option<Vec<Identifier>>,
}

impl<'a> Abstractor<'a> {
    pub fn new(ids: &'a Option<Vec<Identifier>>) -> Self {
        Self { ids }
    }

    /// Check if a given identifiert occurs in a given AST.
    fn check_for_recursion(&self, id: &Vec<Identifier>, subtree: &AstNodePtr) -> bool {
        match &*subtree.borrow() {
            AstNode::App(lhs, rhs) => {
                self.check_for_recursion(id, lhs) || self.check_for_recursion(id, rhs)
            }
            AstNode::Ident(s) => id.contains(&s),
            _ => false,
        }
    }

    /// Check if multiple where definitions contain recursion.
    fn check_for_mutual_recursion(&self, defs: &Vec<(Identifier, AstNodePtr)>) -> bool {
        let def_ids = defs.iter().map(|x| x.0.clone()).collect();
        let mut found_recursion = false;
        for (_, body) in defs {
            found_recursion = found_recursion || self.check_for_recursion(&def_ids, body);
        }
        found_recursion
    }

    /// Abstracts away all identifiers in a expressions.
    pub fn abstract_ids(&mut self, body: &mut AstNodePtr) -> Result<(), SaslError> {
        // If it's a function definition it has to have parameters which need to abstracted.
        // Otherwise it's just a const which may or may not contain a where.
        // If it contains a where it has to be handled.
        if let Some(id_vec) = self.ids {
            for id in id_vec.iter().rev() {
                *body = self.abstract_id(body.clone(), &id)?;
            }
        } else if let AstNode::Where(ref mut lhs, ref mut defs) = *body.clone().borrow_mut() {
            if defs.len() == 1 {
                let (def_name, (params, where_body)) = defs.iter_mut().next().unwrap();
                self.abstract_single_where(def_name, params, where_body)?;
                let free_def_name = self.abstract_id(Rc::clone(&lhs), def_name)?;
                *body = ast::apply2(free_def_name, where_body.clone());
            } else {
                *body = self.abstract_multiple_where(lhs, defs)?;
            }
        }
        Ok(())
    }

    fn abstract_id(&mut self, body: AstNodePtr, id: &Identifier) -> AbstractorResult {
        match *body.borrow_mut() {
            AstNode::Constant(_)
            | AstNode::S
            | AstNode::K
            | AstNode::I
            | AstNode::Y
            | AstNode::U
            | AstNode::Builtin(_) => Ok(ast::apply2(ptr!(AstNode::K), Rc::clone(&body))),
            // [x]var(v) = I if x = v | K @ var(v) otherwise
            AstNode::Ident(ref n) => {
                if id == n {
                    Ok(ptr!(AstNode::I))
                } else {
                    Ok(ast::apply2(ptr!(AstNode::K), Rc::clone(&body)))
                }
            }
            // [x](f @ a) = S @ [x]f @ [x]a
            AstNode::App(ref f, ref a) => Ok(ast::apply3(
                ptr!(AstNode::S),
                self.abstract_id(Rc::clone(f), id)?,
                self.abstract_id(Rc::clone(a), id)?,
            )),
            AstNode::Where(ref mut lhs, ref mut defs) => {
                if defs.len() == 1 {
                    let (def_name, (params, body)) = defs.iter_mut().next().unwrap();
                    self.abstract_single_where(def_name, params, body)?;
                    let free_def_name_body = self.abstract_id(Rc::clone(&lhs), def_name)?;
                    self.abstract_id(ast::apply2(free_def_name_body, Rc::clone(body)), id)
                } else {
                    let freed_where = self.abstract_multiple_where(lhs, defs)?;
                    self.abstract_id(freed_where, id)
                }
            }
            _ => Err(SaslError::CompilerError {
                msg: "Erroneous AST.".to_string(),
            }),
        }
    }

    fn abstract_single_where(
        &mut self,
        name: &Identifier,
        params: &Option<Vec<Identifier>>,
        body: &mut AstNodePtr,
    ) -> Result<(), SaslError> {
        // where f x y z = E -> ([x]([y]([z] E)))
        if let Some(_) = params {
            let mut abst = Abstractor::new(params);
            abst.abstract_ids(body)?;
        }
        // If the definition is recursive: Y @ ([x]([y]([z] E)))
        if self.check_for_recursion(&vec![name.clone()], body) {
            *body = ast::apply2(ptr!(AstNode::Y), self.abstract_id(Rc::clone(body), name)?);
        }
        Ok(())
    }

    fn abstract_multiple_where(
        &mut self,
        lhs: &mut AstNodePtr,
        defs: &mut Vec<(String, (Option<Vec<Identifier>>, AstNodePtr))>,
    ) -> Result<AstNodePtr, SaslError> {
        // Abstract all where definitions
        let mut abstracted_defs = vec![];
        let mut abst;
        for (name, (params, body)) in defs.iter_mut() {
            abst = Abstractor::new(params);
            abst.abstract_ids(body)?;
            abstracted_defs.push((name.clone(), Rc::clone(body)));
        }
        let def_names: VecDeque<Identifier> = abstracted_defs
            .iter()
            .rev()
            .map(|(name, _)| name.clone())
            .collect();
        let is_recursive = self.check_for_mutual_recursion(&abstracted_defs);
        // Build [[x1] E1, [x2]E2, ...] = [x1]E1 : ([x2]E2 : nil)
        let mut defs_list = ast::apply3(
            ptr!(AstNode::Builtin(Op::InfixOp(T![:]))),
            abstracted_defs.pop().unwrap().1,
            ptr!(AstNode::Constant(T![nil])),
        );
        while !abstracted_defs.is_empty() {
            defs_list = ast::apply3(
                ptr!(AstNode::Builtin(Op::InfixOp(T![:]))),
                abstracted_defs.pop().unwrap().1,
                defs_list,
            );
        }
        // Abstract where definition calls from main body
        // E1 where f x = E2; g y = E3 ~> U @ ([f]( U @ [g]( K @ E1)))
        let mut new_main_body = ast::apply2(ptr!(AstNode::K), Rc::clone(lhs));
        for name in def_names.iter() {
            new_main_body = ast::apply2(ptr!(AstNode::U), self.abstract_id(new_main_body, &name)?);
        }
        // Abstract local function names if definitions are mutual recursive
        // E1 where f1 x1 = E2:... g ...; f2 x2 = E3:... f ...; ... ~> Y @ (U @ [f1](U @ [f2](U @ ...(U @ f[n](K @ [[x1]E2], [x2]E3, ..., [xn]En]))
        if is_recursive {
            let mut rec_defs = ast::apply2(ptr!(AstNode::K), defs_list);
            for def_name in def_names.iter() {
                rec_defs = ast::apply2(ptr!(AstNode::U), self.abstract_id(rec_defs, def_name)?);
            }
            rec_defs = ast::apply2(ptr!(AstNode::Y), rec_defs);
            // U @ ([f]( U @ [g]( K @ E1))) @ (Y @ (U @ [f1](U @ [f2](U @ ...(U @ f[n](K @ [[x1]E2], [x2]E3, ..., [xn]En])))
            return Ok(ast::apply2(new_main_body, rec_defs));
        }
        // No (mutual) recursion found
        // U @ ([f]( U @ [g]( K @ E1))) @ [[x1]E1, ..., [xn]En]
        Ok(ast::apply2(new_main_body, defs_list))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{backend::compiler::compile, frontend::{ast::Ast, lexer::Lexer, parser::Parser, visualize::Visualizer}};

    fn parse_to_ast(code: &str) -> Ast {
        Parser::new(Lexer::new(code).tokenize().unwrap())
            .parse()
            .unwrap()
    }

    fn check_recursion(wh: AstNodePtr) -> bool {
        let abst = Abstractor::new(&None);
        if let AstNode::Where(_, ref defs) = &*wh.borrow() {
            let mut d = Vec::new();
            for (name, (_, body)) in defs {
                d.push((name.clone(), Rc::clone(body)))
            }
            return abst.check_for_mutual_recursion(&d);
        }
        false
    }

    fn compile_(code: &str) -> Ast {
        let mut ast = parse_to_ast(code);
        compile(&mut ast).unwrap();
        ast
    }

    #[test]
    fn test_check_recursion() {
        let mut ast = parse_to_ast("x where f x = g x; g y = f y");
        assert!(check_recursion(ast.body));
        ast = parse_to_ast("x where f x = f x; g y = g y");
        assert!(check_recursion(ast.body));
        ast = parse_to_ast("x where f x = x; g = 5");
        assert!(!check_recursion(ast.body));
        ast = parse_to_ast("1 where f x = 5 * x; g x = x; h x = g x");
        assert!(check_recursion(ast.body));
    }

    #[test]
    fn test_multiple_where() {
        let mut vis = Visualizer::new("g", false);
        let ast = compile_("f where f = g; g = 1");
        vis.visualize_ast(&ast);
        println!("After compilation: {:?}", &ast);
        vis.write_to_pdf("test.pdf");
        //println!("{}", ast.body.borrow());
    }
}
