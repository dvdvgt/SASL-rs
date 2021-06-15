use std::collections::HashMap;

use crate::{T, error::SaslError, frontend::ast::{self, AstNode, Identifier, Op}};

pub struct Abstractor<'a> {
    ids: &'a Option<Vec<Identifier>>
}

impl<'a> Abstractor<'a> {
    pub fn new(ids: &'a Option<Vec<Identifier>>) -> Self {
        Self {
            ids
        }
    }

    fn check_for_recursion(&self, id: &Vec<Identifier>, subtree: &AstNode) -> bool {
        match subtree {
            AstNode::App(lhs, rhs) => {
                self.check_for_recursion(id, lhs) || self.check_for_recursion(id, rhs)
            }
            AstNode::Ident(s) => id.contains(&s),
            _ => false
        }
    }

    fn check_for_mutual_recursion(&self, defs: &Vec<(Identifier, AstNode)>) -> bool {
        let def_ids = defs.iter().map(|x| x.0.clone()).collect();
        let mut found_recursion = false;
        for (_, body) in defs {
            found_recursion = found_recursion || self.check_for_recursion(&def_ids, body);
        }
        found_recursion
    }

    pub fn abstract_ids(&mut self, body: AstNode) -> Result<AstNode, SaslError> {
        let mut new_body = body;
        if let Some(id_vec) = self.ids {
            for id in id_vec.iter().rev() {
                new_body = self.abstract_id(new_body, &id)?;
            }
        }
        if let AstNode::Where(ref lhs, ref defs) = new_body {
            if defs.len() == 1 {
                let (def_name, (params, body)) = defs.iter().next().unwrap();
                let where_def_body = self.abstract_single_where(def_name, params, body)?;println!("{:?}", where_def_body);
                let free_def_name = self.abstract_id(*lhs.clone(), def_name)?;
                new_body = ast::apply2(free_def_name, where_def_body);
            } else {
                new_body = self.abstract_multiple_where(*lhs.clone(), defs)?;
            }
        }
        Ok(new_body)
    }

    fn abstract_id(&mut self, body: AstNode, id: &Identifier) -> Result<AstNode, SaslError> {
        match body {
            AstNode::Constant(_)
            | AstNode::S
            | AstNode::K
            | AstNode::I
            | AstNode::Y
            | AstNode::U
            | AstNode::Builtin(_) => Ok(ast::apply2(AstNode::K, body)),
            // [x]var(v) = I if x = v | K @ var(v) otherwise
            AstNode::Ident(ref n) => {
                if id == n {
                    Ok(AstNode::I)
                } else {
                    Ok(ast::apply2(AstNode::K, body))
                }
            }
            // [x](f @ a) = S @ [x]f @ [x]a
            AstNode::App(f, a) => Ok(
                ast::apply3(
                    AstNode::S,
                    self.abstract_id(*f, id)?,
                    self.abstract_id(*a, id)?
                )
            ),
            AstNode::Where(lhs, ref defs) => {
                if defs.len() == 1 {
                    let (def_name, (params, body)) = defs.iter().next().unwrap();
                    let where_def_body = self.abstract_single_where(def_name, params, body)?;
                    let free_def_name_body = self.abstract_id(*lhs, def_name)?;
                    self.abstract_id(
                        ast::apply2(free_def_name_body, where_def_body),
                        id
                    )
                } else {
                    let freed_where = self.abstract_multiple_where(*lhs, defs)?;
                    println!("{:?}", freed_where);
                    self.abstract_id(freed_where, id)
                }
            }
            _ => Err(SaslError::CompilerError {msg: "Erroneous AST.".to_string()})
        }
    }

    fn abstract_single_where(&mut self, name: &Identifier, params: &Option<Vec<Identifier>>, body: &AstNode) -> Result<AstNode, SaslError> {
        let mut new_body = body.clone();
        // where f x y z = E -> ([x]([y]([z] E)))
        if let Some(p) = params {
            let mut abst = Abstractor::new(params);
            new_body = abst.abstract_ids(new_body)?;
        }

        if self.check_for_recursion(&vec![name.clone()], &new_body) {
            Ok(ast::apply2(AstNode::Y, self.abstract_id(new_body, name)?))
        } else {
            Ok(new_body)
        }
    }

    fn abstract_multiple_where(&mut self, lhs: AstNode, defs: &HashMap<String, (Option<Vec<Identifier>>, AstNode)>) -> Result<AstNode, SaslError> {
        // Abstract all where definitions
        let mut abstracted_defs = vec![];
        for (name, (params, body)) in defs {
            let new_body = self.abstract_single_where(name, params, body)?;
            abstracted_defs.push((name.clone(), new_body));
        }
        let def_names: Vec<Identifier> = abstracted_defs.iter().map(|(name, _)| name.clone()).collect();
        let is_recursive = self.check_for_mutual_recursion(&abstracted_defs);
        // Build [[x1] E1, [x2]E2, ...] = [x1]E1 : ([x2]E2 : nil)
        let mut defs_list = ast::apply3( 
            AstNode::Builtin(Op::InfixOp(T![:])),
            abstracted_defs.pop().unwrap().1,
            AstNode::Constant(T![nil])
        );
        while !abstracted_defs.is_empty() {
            defs_list = ast::apply3(
                AstNode::Builtin(Op::InfixOp(T![:])), 
                abstracted_defs.pop().unwrap().1,
                defs_list
            );
        }
        // Abstract where definition calls from main body
        // E1 where f x = E2; g y = E3 ~> U @ ([f]( U @ [g]( K @ E1)))
        let mut new_main_body = ast::apply2(AstNode::K, lhs);
        for name in def_names.iter() {
            new_main_body = ast::apply2(AstNode::U, self.abstract_id(new_main_body, &name)?);
        }
        // Abstract local function names if definitions are mutual recursive
        // E1 where f1 x1 = E2:... g ...; f2 x2 = E3:... f ...; ... ~> Y @ (U @ [f1](U @ [f2](U @ ...(U @ f[n](K @ [[x1]E2], [x2]E3, ..., [xn]En]))
        if is_recursive {
            let mut rec_defs = ast::apply2(AstNode::K, defs_list);
            for def_name in def_names.iter() {
                println!("{}", def_name);
                rec_defs = ast::apply2(AstNode::U, self.abstract_id(rec_defs, def_name)?);
            }
            rec_defs = ast::apply2(AstNode::Y, rec_defs);
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
    use crate::frontend::{ast::Ast, parser::Parser, lexer::Lexer};
    use super::*;

    fn parse_to_ast(code: &str) -> Ast {
        Parser::new(Lexer::new(code).tokenize().unwrap())
            .parse()
            .unwrap()
    }

    fn check_recursion(wh: AstNode) -> bool {
        let abst = Abstractor::new(&None);
        if let AstNode::Where(_, defs) = wh {
            let mut d = Vec::new();
            for (name, (_, body)) in defs {
                d.push((name, body))
            }
            return abst.check_for_mutual_recursion(&d);
        }   
        false
    }

    #[test]
    fn test_check_recursion() {
        let mut ast = parse_to_ast(
            "x where f x = g x; g y = f y"
        );
        assert!(check_recursion(ast.body));
        ast = parse_to_ast(
            "x where f x = f x; g y = g y"
        );
        assert!(check_recursion(ast.body));
        ast = parse_to_ast(
            "x where f x = x; g = 5"
        );
        assert!(!check_recursion(ast.body));
        ast = parse_to_ast(
            "1 where f x = 5 * x; g x = x; h x = g x"
        );
        assert!(check_recursion(ast.body));
        ast = parse_to_ast(
            "1 where f x = f x"
        );
    }
}