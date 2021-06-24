use std::collections::HashMap;
use std::rc::Rc;
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

    pub fn abstract_ids(&self, body: Rc<AstNode>) -> Result<Rc<AstNode>, SaslError> {
        let mut new_body = body.clone();
        if let Some(id_vec) = self.ids {
            for id in id_vec.iter().rev() {
                new_body = self.abstract_id(new_body, id)?;
            }
        } else if let AstNode::Where(lhs, defs) = &*body {
            if defs.len() == 1 {
                let (def_name, (params, body)) = defs.iter().next().unwrap();
                let new_def_body = self.abstract_single_where(def_name, params, body.clone())?;
                let free_def_name = self.abstract_id(lhs.clone(), def_name)?;
                new_body = ast::apply2(free_def_name, new_def_body);
            } else {
                new_body = self.abstract_multiple_where(lhs.clone(), defs)?;
            }
        }
        Ok(new_body)
    }

    fn check_for_recursion(&self, tree: &Rc<AstNode>, id: &Vec<Identifier>) -> bool {
        match &**tree {
            AstNode::App(lhs, rhs) => {
                self.check_for_recursion(lhs, id) || self.check_for_recursion(rhs, id)
            }
            AstNode::Ident(s) => id.contains(&s),
            _ => false
        }
    }

    fn check_for_mutual_recursion(&self, defs: &Vec<(Identifier, Rc<AstNode>)>) -> bool {
        let def_ids = defs.iter().map(|x| x.0.clone()).collect();
        let mut found_recursion = false;
        for (_, body) in defs {
            found_recursion = found_recursion || self.check_for_recursion(body, &def_ids);
        }
        found_recursion
    }

    fn abstract_id(&self, body: Rc<AstNode>, id: &Identifier) -> Result<Rc<AstNode>, SaslError> {
        match &*body {
            AstNode::Constant(_)
            | AstNode::S
            | AstNode::K
            | AstNode::I
            | AstNode::Y
            | AstNode::U
            | AstNode::Builtin(_) => Ok(ast::apply2(Rc::new(AstNode::K), body)),
            // [x]var(v) = I if x = v | K @ var(v) otherwise
            AstNode::Ident(ref n) => {
                if id == n {
                    Ok(Rc::new(AstNode::I))
                } else {
                    Ok(ast::apply2(Rc::new(AstNode::K), body))
                }
            }
            // [x](f @ a) = S @ [x]f @ [x]a
            AstNode::App(ref f, ref a) => Ok(
                ast::apply3(
                    Rc::new(AstNode::S),
                    self.abstract_id(f.clone(), id)?,
                    self.abstract_id(a.clone(), id)?
                )
            ),
            AstNode::Where(lhs, defs) => {
                if defs.len() == 1 {
                    let (def_name, (params, body)) = defs.iter().next().unwrap();
                    let new_def_body = self.abstract_single_where(def_name, params, body.clone())?;
                    let free_def_name = self.abstract_id(lhs.clone(), def_name)?;
                    self.abstract_id(
                        ast::apply2(free_def_name, new_def_body),
                        id
                    )
                } else {
                    todo!()
                }
            }
            _ => Err(SaslError::CompilerError {msg: "Erroneous AST.".to_string()})
        }
    }

    fn abstract_single_where(&self, name: &Identifier, params: &Option<Vec<Identifier>>, body: Rc<AstNode>) -> Result<Rc<AstNode>, SaslError> {
        let mut new_body = body.clone();
        // where f x y z = E -> ([x]([y]([z] E)))
        if let Some(_) = params {
            let abst = Abstractor::new(params);
            new_body = abst.abstract_ids(new_body)?;
        }
        // If the definition is recursive: Y @ ([x]([y]([z] E)))
        if self.check_for_recursion(&body, &vec![name.clone()]) {
            new_body = ast::apply2(Rc::new(AstNode::Y), self.abstract_id(new_body.clone(), name)?.clone())
        }
        Ok(new_body)
    }

    fn abstract_multiple_where(&self, lhs: Rc<AstNode>, defs: &HashMap<String, (Option<Vec<Identifier>>, Rc<AstNode>)>) -> Result<Rc<AstNode>, SaslError> {
        // Abstract all where definitions
        let mut abstracted_defs = vec![];
        for (name, (params, body)) in defs.iter() {
            let new_def_body = self.abstract_single_where(name, params, body.clone())?;
            abstracted_defs.push((name.clone(), new_def_body));
        }
        let def_names: Vec<Identifier> = abstracted_defs.iter()
            .map(|(name, _)| name.clone())
            .collect();
        let is_mutual_recursive = self.check_for_mutual_recursion(&abstracted_defs);
        // Build [[x1] E1, [x2]E2, ...] = [x1]E1 : ([x2]E2 : nil)
        let mut defs_list = ast::apply3(
            Rc::new(
                AstNode::Builtin(Op::InfixOp(T![:]))
            ),
            abstracted_defs.pop().unwrap().1,
            Rc::new(
                AstNode::Constant(T![nil])
            )
        );
        while !abstracted_defs.is_empty() {
            defs_list = ast::apply3(
                Rc::new(
                    AstNode::Builtin(Op::InfixOp(T![:]))
                ),
                abstracted_defs.pop().unwrap().1,
                defs_list
            )
        }
        // Abstract where definition calls from main body
        // E1 where f x = E2; g y = E3 ~> U @ ([f]( U @ [g]( K @ E1)))
        let mut new_main_body = ast::apply2(Rc::new(AstNode::K), lhs);
        for name in def_names.iter() {
            new_main_body = ast::apply2(
                Rc::new(AstNode::U), 
                self.abstract_id(new_main_body, &name)?
            );
        }
        // Abstract local function names if definitions are mutual recursive
        // E1 where f1 x1 = E2:... g ...; f2 x2 = E3:... f ...; ... ~> Y @ (U @ [f1](U @ [f2](U @ ...(U @ f[n](K @ [[x1]E2], [x2]E3, ..., [xn]En]))
        if is_mutual_recursive {
            let mut rec_defs = ast::apply2(
                Rc::new(AstNode::K),
                defs_list
            );
            for def_name in def_names.iter() {
                rec_defs = ast::apply2(
                    Rc::new(AstNode::U), 
                    self.abstract_id(rec_defs, def_name)?
                );
            }
            rec_defs = ast::apply2(
                Rc::new(AstNode::Y),
                rec_defs
            );
            return Ok(ast::apply2(new_main_body, rec_defs));
        }
        Ok(ast::apply2(new_main_body, defs_list))
    }
}