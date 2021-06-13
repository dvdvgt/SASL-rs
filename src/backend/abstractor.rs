use std::collections::HashMap;

use crate::{error::SaslError, frontend::ast::{AstNode, Def, Identifier, self}};

pub struct Abstractor<'a> {
    ids: &'a Option<Vec<Identifier>>
}

impl<'a> Abstractor<'a> {
    pub fn new(ids: &'a Option<Vec<Identifier>>) -> Self {
        Self {
            ids
        }
    }

    fn check_for_recursion(&self, id: &str, subtree: &AstNode) -> bool {
        match subtree {
            AstNode::App(lhs, rhs) => {
                self.check_for_recursion(id, lhs) || self.check_for_recursion(id, rhs)
            }
            AstNode::Ident(s) => s == id,
            _ => false
        }
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
                let where_def_body = self.abstract_single_where(def_name, params, body)?;
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

        if self.check_for_recursion(name, &new_body) {
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
            abstracted_defs.push((name, new_body));
        }
        // Abstract where definition calls from main body
        let mut new_main_body = lhs;
        for (name, _) in abstracted_defs.clone().into_iter().rev() {
            new_main_body = self.abstract_id(new_main_body, name)?;
        }
        for (_, where_def_body) in abstracted_defs.into_iter().rev() {
            new_main_body = ast::apply2(new_main_body, where_def_body);
        }
        Ok(new_main_body)

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
}