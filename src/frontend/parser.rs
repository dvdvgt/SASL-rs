//! Recursive descent parser implementation

use std::collections::{hash_map::HashMap, VecDeque};
use std::error::Error;

use super::{ast::{AstNode, Op, Def, Ast}, utils::Position};
use super::token::{Token, Type};
use crate::{error::SaslError::{ParseError, self}};
use crate::T;

pub struct Parser<'a> {
    tokens: VecDeque<Token<'a>>,
}

type ParserResult = Result<AstNode, Box<dyn Error>>;
type Defs = HashMap<Def, AstNode>;

impl<'a> Parser<'a> {
    pub fn new(tokens: VecDeque<Token<'a>>) -> Self {
        Self { tokens }
    }

    //-------
    // HELPER
    //-------

    /// True if next token is of expected type.
    fn expect_type(&self, t: Type) -> bool {
        self.peek() == &t
    }

    /// Peeks at the type of the token at front of the queue.
    fn peek(&self) -> &Type {
        self.tokens.front()
            .map(|token| &token.typ)
            .unwrap_or(&T![eof])
    }

    /// Pops the first token of the queue.
    fn next(&mut self) -> Option<Token<'a>> {
        self.tokens.pop_front()
    }

    /// Tries consuming the next token. If the type matches the expected type the token
    /// is returned otherwise an error is thrown.
    // TODO
    fn consume(&mut self, expected: &Type) -> Token<'a> {
        let token = self.next()
            .expect(
                &format!("Expected '{}', but there was none.", expected)
            );
        assert_eq!(&token.typ, expected, "Expected '{}', but found '{}'", expected, &token.typ);
        token
    }

    /// Apply an operation to one argument.
    fn apply2(&self, op: AstNode, arg: AstNode) -> AstNode {
        AstNode::App(
            Box::new(op), Box::new(arg)
        )
    }

    /// Apply an operation to two arguments.
    fn apply3(&self, op: AstNode, inner_arg: AstNode, outer_arg: AstNode) -> AstNode {
        AstNode::App(
            Box::new(self.apply2(op, inner_arg)),
            Box::new(outer_arg)
        )
    }

    /// Create a parse error with a custom error message.
    fn throw_parse_err(&self, token: Token<'a>, err: &str) -> Box<dyn Error> {
        Box::new(
            ParseError {
                    pos: token.pos,
                    msg: format!("{} Found {}:{} instead.", err, token.typ, token.lexeme)
            }
        )
    }

    //--------
    // PARSING
    //--------

    /// Parse the given tokens into a AST.
    /// Corresponds to the <system> non-terminal in the grammar rules.
    pub fn parse(&mut self) -> Result<Ast, Box<dyn Error>> {
        let mut ast = Ast::new();
        if self.expect_type(T![def]) {
            self.parse_funcdefs(&mut ast.global_defs);
            if self.expect_type(T![.]) {
                self.consume(&T![.]);
                let expr = self.parse_expr()?;
                ast.body = expr;
                Ok(ast)
            } else {
                let tok = self.next().unwrap();
                Err(self.throw_parse_err(tok, "Expected '.'."))
            }
        } else {
            ast.body = self.parse_expr()?;
            Ok(ast)
        }
    }

    fn parse_funcdefs(&mut self, global_defs: &mut Defs) {
        self.consume(&T![def]);
        let def = self.parse_def();
        global_defs.insert(def.0, def.1);
        self.parse_funcdefs1(global_defs);
    }

    fn parse_funcdefs1(&mut self, global_defs: &mut Defs) {
        if self.expect_type(T![def]) {
            self.next();
            let def = self.parse_def();
            global_defs.insert(def.0, def.1);
            self.parse_funcdefs1(global_defs);
        }
    }

    fn parse_defs(&mut self) -> Defs {
        let mut defs = HashMap::new();
        let def = self.parse_def();
        defs.insert(def.0, def.1);
        self.parse_defs1(&mut defs);
        defs
    }

    fn parse_defs1(&mut self, defs: &mut Defs) {
        if self.expect_type(T![;]) {
            self.consume(&T![;]);
            let def = self.parse_def();
            defs.insert(def.0, def.1);
            self.parse_defs1(defs);
        } else {
            return
        }
    }

    fn parse_def(&mut self) -> (Def, AstNode) {
        let name = self.parse_name().unwrap();
        match name {
            AstNode::Ident(n) => {
                self.parse_abstraction(
                    Def::new(n, None)
                )
            }
            _ => panic!()
        }
    }

    fn parse_abstraction(&mut self, mut def: Def) -> (Def, AstNode) {
        if self.expect_type(T![=]) {
            self.consume(&T![=]);
            let expr = self.parse_expr().unwrap();
            (def, expr)
        } else {
            match self.parse_name().unwrap() {
                AstNode::Ident(name) => def.add_new_parameter(&name),
                _ => panic!()
            }
            self.parse_abstraction(def)
        }
    }

    pub fn parse_expr(&mut self) -> ParserResult {
        let cond_expr = self.parse_condexpr()?;
        let expr1 = self.parse_expr1()?;
        match expr1 {
            AstNode::Empty => Ok(cond_expr),
            AstNode::Where(None, defs, rhs) => {
                Ok(AstNode::Where(Some(Box::new(cond_expr)), defs, rhs))
            }
            _ => Ok(AstNode::Empty)
        }
    }

    fn parse_expr1(&mut self) -> ParserResult {
        if self.expect_type(T![where]) {
            let pos = self.consume(&T![where]).pos;
            let defs = self.parse_defs();
            let where_expr = self.parse_expr1()?;
            match where_expr {
                AstNode::Empty => Ok(AstNode::Where(None, defs, None)),
                nested_where @ AstNode::Where(None, _, None) => {
                    Ok(AstNode::Where(None, defs, Some(Box::new(nested_where))))
                }
                _ => Err(Box::new(ParseError {pos, msg: "Unexpected error.".to_string()}))
            }
        } else {
            Ok(AstNode::Empty)
        }
    }

    fn parse_condexpr(&mut self) -> ParserResult {
        if self.expect_type(T![if]) {
            self.consume(&T![if]);
            let predicate = self.parse_expr()?;
            self.consume(&T![then]);
            let then_expr = self.parse_condexpr()?;
            self.consume(&T![else]);
            let else_expr = self.parse_condexpr()?;
            Ok(
                self.apply2(
                    self.apply3(AstNode::Builtin(Op::Cond), predicate, then_expr), 
                    else_expr
                )
            )
        } else {
            self.parse_listexpr()
        }
    }

    fn parse_listexpr(&mut self) -> ParserResult {
        let op_expr = self.parse_opexpr()?;
        let list_expr = self.parse_listexpr1()?;
        match list_expr {
            AstNode::Empty => Ok(op_expr),
            _ => {
                Ok(self.apply3(AstNode::Builtin(Op::InfixOp(T![:])), op_expr, list_expr))
            }
        }
    }

    fn parse_listexpr1(&mut self) -> ParserResult {
        if self.expect_type(T![:]) {
            self.consume(&T![:]);
            self.parse_listexpr()
        } else {
            Ok(AstNode::Empty)
        }
    }

    fn parse_opexpr(&mut self) -> ParserResult {
        let lhs = self.parse_conjunct()?;
        self.parse_opexpr1(lhs)
    }

    fn parse_opexpr1(&mut self, lhs: AstNode) -> ParserResult {
        if self.expect_type(T![or]) {
            self.consume(&T![or]);
            let conjunct = self.parse_conjunct()?;
            let lhs1 = self.apply3(AstNode::Builtin(Op::InfixOp(T![or])), lhs, conjunct);
            self.parse_opexpr1(lhs1)
        } else {
            Ok(lhs)
        }
    }

    fn parse_conjunct(&mut self) -> ParserResult {
        let lhs = self.parse_compar()?;
        self.parse_conjunct1(lhs)
    }
    fn parse_conjunct1(&mut self, lhs: AstNode) -> ParserResult {
        if self.expect_type(T![and]) {
            self.consume(&T![and]);
            let compar = self.parse_compar()?;
            let lhs1 = self.apply3(AstNode::Builtin(Op::InfixOp(T![and])), lhs, compar);
            self.parse_conjunct1(lhs1)
        } else {
            Ok(lhs)
        }
    }

    fn parse_compar(&mut self) -> ParserResult {
        let lhs = self.parse_add()?;
        self.parse_compar1(lhs)
    }

    fn parse_compar1(&mut self, lhs: AstNode) -> ParserResult {
        match self.peek() {
            T![=] | T![~=] | T![<] | T![>] | T![<=] | T![>=] => {
                let op = self.parse_relop()?;
                let add = self.parse_add()?;
                let lhs1 = self.apply3(op, lhs, add);
                self.parse_compar1(lhs1)
            },
            _ => Ok(lhs)
        }
    }

    fn parse_add(&mut self) -> ParserResult {
        let rhs = self.parse_mul()?;
        self.parse_add1(rhs)
    }

    fn parse_add1(&mut self, rhs: AstNode) -> ParserResult {
        match self.peek() {
            T![+] | T![-] => {
                let op = self.next().unwrap().typ;
                let mul = self.parse_mul()?;
                let rhs1 = AstNode::App(
                    Box::new(AstNode::App(
                        Box::new(AstNode::Builtin(Op::InfixOp(op))),
                        Box::new(rhs)
                    )),
                    Box::new(mul)
                );
                self.parse_add1(rhs1)
            }
            _ => {
                Ok(rhs)
            }
        }
    }

    fn parse_mul(&mut self) -> ParserResult {
        let rhs = self.parse_factor()?;
        self.parse_mul1(rhs)   
    }

    fn parse_mul1(&mut self, rhs: AstNode) -> ParserResult {
        match self.peek() {
            T![*] | T![/] => {
                let op = self.next().unwrap().typ;
                let factor = self.parse_factor()?;
                let rhs1 = AstNode::App(
                    Box::new(AstNode::App(
                        Box::new(AstNode::Builtin(Op::InfixOp(op))), 
                        Box::new(rhs)
                    )),
                    Box::new(factor)
                );
                self.parse_mul1(rhs1)
            }
            _ => Ok(rhs)
        }
    }

    fn parse_factor(&mut self) -> ParserResult {
        match self.peek() {
            T![+] | T![-] | T![not] => {
                let prefix = self.next().unwrap().typ;
                let comb = self.parse_comb()?;
                Ok(self.apply2(AstNode::Builtin(Op::PrefixOp(prefix)), comb))
            }
            _ => {
                self.parse_comb()
            }
        }
    }

    fn parse_comb(&mut self) -> ParserResult {
        let simple = self.parse_simple()?;
        self.parse_comb1(simple)
    }

    fn parse_comb1(&mut self, lhs: AstNode) -> ParserResult {
        match self.peek() {
            T![head] | T![tail] | Type::String(_) | Type::Number(_) | Type::Boolean(_) |
            T!['['] | T!['('] | T![ident] => {
                let lhs1 = AstNode::App(Box::new(lhs), Box::new(self.parse_simple()?));
                self.parse_comb1(lhs1)
            }
            _ => Ok(lhs)
        }
    }

    fn parse_simple(&mut self) -> ParserResult {
        match self.peek() {
            T![ident] => self.parse_name(),
            T![head] | T![tail] => self.parse_builtin(),
            Type::String(_) | Type::Number(_) | Type::Boolean(_) | T![nil] | T!['['] => self.parse_constant(),
            T!['('] => {
                self.consume(&T!['(']);
                let expr = self.parse_expr()?;
                match self.peek() {
                    T![')'] => {
                        self.consume(&T![')']);
                        Ok(expr)
                    }
                    _ => {
                        let token = self.next().unwrap();
                    Err(Box::new(ParseError {pos: token.pos, msg: format!("Expected ')' but found {}.", token.typ)}))
                    }   
                }
            }
            _ => {
                let token = self.next().unwrap();
                Err(self.throw_parse_err(token, "Expected identifier, hd, tl, constand or grouped expression."))
            }
        }
    }

    fn parse_name(&mut self) -> ParserResult {
        if self.peek() == &T![ident] {
            let id_name = self.next()
                .unwrap()
                .lexeme.to_string();
            Ok(AstNode::Ident(id_name))
        } else {
            let token = self.next().unwrap();
            Err(self.throw_parse_err(token, "Expected identifier."))
        }
    }

    fn parse_builtin(&mut self) -> ParserResult {
        match self.peek() {
            T![head] | T![tail] => {
                let op = self.next().unwrap().typ;
                Ok(AstNode::Builtin(Op::PrefixOp(op)))
            }
            _ => {
                let token = self.next().unwrap();
                Err(self.throw_parse_err(token, "Expected hd (head) or tl (tail) call."))
            }
        }
    }

    fn parse_constant(&mut self) -> ParserResult {
        match self.peek() {
            Type::Number(_) | Type::String(_) | Type::Boolean(_) => Ok(AstNode::Constant(self.next().unwrap().typ)),
            T![nil] => Ok(AstNode::Constant(self.consume(&T![nil]).typ)),
            T!['['] => {
                self.consume(&T!['[']);
                self.parse_list1()
            }
            _ => {
                let token = self.next().unwrap();
                Err(self.throw_parse_err(token, "Expected constant/literal."))
            }
        }
    }

    fn parse_list1(&mut self) -> ParserResult {
        match self.peek() {
            T![']'] => {
                self.consume(&T![']']);
                Ok(AstNode::Constant(T![nil]))
            }
            _ => {
                let list_elems = self.parse_listelems()?;
                match self.peek() {
                    T![']'] => {
                        self.consume(&T![']']);
                        Ok(list_elems)
                    }
                    _ => {
                        let token = self.next().unwrap();
                        Err(self.throw_parse_err(token, "Expected ']'."))
                    }
                }
            }
        }
    }

    fn parse_listelems(&mut self) -> ParserResult {
        let expr = self.parse_expr()?;
        let list_app = AstNode::App(
            Box::new(AstNode::Builtin(Op::InfixOp(T![:]))),
            Box::new(expr)
        );
        Ok(AstNode::App(Box::new(list_app), Box::new(self.parse_listelems1()?)))
    }

    fn parse_listelems1(&mut self) -> ParserResult {
        match self.peek() {
            T![,] => {
                self.consume(&T![,]);
                let expr = self.parse_expr()?;
                let list_app = AstNode::App(
                    Box::new(AstNode::Builtin(Op::InfixOp(T![:]))),
                    Box::new(expr)
                );
                Ok(AstNode::App(Box::new(list_app), Box::new(self.parse_listelems1()?)))
            }
            _ => {
                Ok(AstNode::Constant(T![nil]))
            }
        }
    }

    fn parse_prefix(&mut self) -> ParserResult {
        match self.peek() {
            T![-] | T![+] | T![not] => {
                let token = self.next().unwrap();
                Ok(AstNode::Builtin(Op::PrefixOp(token.typ)))
            }
            _ => {
                let token = self.next().unwrap();
                Err(Box::new(ParseError {pos: token.pos, msg: format!("Expected prefix operator (+, -, not) but found {}.", token.typ)}))
            }
        }
    }

    fn parse_addop(&mut self) -> ParserResult {
        match self.peek() {
            T![+] | T![-] => {
                let token = self.next().unwrap();
                Ok(AstNode::Builtin(Op::InfixOp(token.typ)))
            }
            _ => {
                let token = self.next().unwrap();
                Err(Box::new(ParseError {pos: token.pos, msg: format!("Expected infix operator (+, -) but found {}.", token.typ)}))
            }
        }
    }

    fn parse_mulop(&mut self) -> ParserResult {
        match self.peek() {
            T![*] | T![/] => {
                let op = self.next().unwrap().typ;
                Ok(AstNode::Builtin(Op::InfixOp(op)))
            }
            _ => {
                let token = self.next().unwrap();
                Err(Box::new(ParseError {pos: token.pos, msg: format!("Expected infix operator (*, /) but found {}.", token.typ)}))
            }
        }
    }

    fn parse_relop(&mut self) -> ParserResult {
        match self.peek() {
            T![=] | T![~=] | T![<] | T![>] | T![<=] | T![>=] => {
                let op = self.next().unwrap().typ;
                Ok(AstNode::Builtin(Op::InfixOp(op)))
            }
            _ => {
                let token = self.next().unwrap();
                Err(Box::new(ParseError {pos: token.pos, msg: format!("Expected relational infix operator (=, ~=, <, >, <=, >=) but found {}.", token.typ)}))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend::lexer::Lexer;

    fn parse_expr(input: &str) -> AstNode {
        let mut lx = Lexer::new(input);
        let tokens = lx.tokenize().unwrap().clone();
        let mut parser = Parser::new(tokens);
        parser.parse_expr().unwrap()
    }

    fn parse_def(input: &str, defs: &mut Defs) {
        let mut lx = Lexer::new(input);
        let tokens = lx.tokenize().unwrap().clone();
        let mut parser = Parser::new(tokens);
        parser.parse_funcdefs(defs)
    }

    #[test]
    fn test_parse_basic_epxr() {
        let expr = parse_expr("[1,2,\"ab\", true, 5.6, id]");
        assert_eq!(
            expr.to_string(), 
            "((: @ Number:1) @ ((: @ Number:2) @ ((: @ String:ab) @ ((: @ Boolean:true) @ ((: @ Number:5.6) @ ((: @ Id:id) @ nil))))))"
        );
        let expr = parse_expr("1.2 + 2 * 3 - 4 / 5");
        assert_eq!(
            expr.to_string(),
            "((- @ ((+ @ Number:1.2) @ ((* @ Number:2) @ Number:3))) @ ((/ @ Number:4) @ Number:5))"
        );
        let expr = parse_expr("if [1,true,\"a\"] = nil then 1.5 else -2.5");
        assert_eq!(
            expr.to_string(),
            "(((cond @ ((= @ ((: @ Number:1) @ ((: @ Boolean:true) @ ((: @ String:a) @ nil)))) @ nil)) @ Number:1.5) @ (- @ Number:2.5))"
        )
    }

    #[test]
    fn test_parse_def() {
        let mut defs = HashMap::new();
        parse_def("def a = 5 + 2\ndef b x = -2.3 * x\ndef plus x y z = x + y + z", &mut defs);

        assert_eq!(defs.len(), 3);

        let def = &Def { name: "a".to_string(), params: None };
        let astnode = defs.get(def).unwrap();
        assert_eq!(
            astnode.to_string(),
            "((+ @ Number:5) @ Number:2)"
        );
        
        let def = &Def { name: "b".to_string(), params: Some(vec!["x".to_string()]) };
        let astnode = defs.get(def).unwrap();
        assert_eq!(
            astnode.to_string(),
            "((* @ (- @ Number:2.3)) @ Id:x)"
        );

        let def = &Def { name: "plus".to_string(), params: Some(vec!["x".to_string(), "y".to_string(), "z".to_string()])};
        let astnode = defs.get(def).unwrap();
        assert_eq!(
            astnode.to_string(),
            "((+ @ ((+ @ Id:x) @ Id:y)) @ Id:z)"
        );
    }
}