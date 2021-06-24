use crate::{error::SaslError, frontend::ast::{Ast, AstNode, AstNodePtr, Op}};
use crate::frontend::token::{Type};
use std::{cell::RefCell, ops::Deref, rc::Rc};
use crate::{T, ptr};

macro_rules! get_app_child {
    (rhs($node:expr)) => {
        match &*$node.borrow() {
            AstNode::App(_, rhs) => Rc::clone(rhs),
            _ => panic!()
        }
    };
    (lhs($node:expr)) => {
        match &*$node.borrow() {
            AstNode::App(lhs, _) => Rc::clone(lhs),
            _ => panic!()
        }
    }
}

macro_rules! set_app_child_value {
    ( rhs($app_node:expr) = $node:expr ) => {
        if let AstNode::App(_, rhs) = &*$app_node.borrow() {
            *rhs.borrow_mut() = $node;
        };
    };
    ( lhs($app_node:expr) = $node:expr ) => {
        if let AstNode::App(lhs, _) = &*$app_node.borrow() {
            *lhs.borrow_mut() = $node;
        };
    }
}

macro_rules! set_app_child_ptr {
    ( rhs($app_node:expr) = $node:expr ) => {
        if let AstNode::App(_, rhs) = &mut *$app_node.borrow_mut() {
            *rhs = $node;
        };
    };
    ( lhs($app_node:expr) = $node:expr ) => {
        if let AstNode::App(mut lhs, _) = &*$app_node.borrow_mut() {
            *lhs = $node;
        };
    }
}

macro_rules! check_type {
    ($nodeptr:expr; number) => {
        if let AstNode::Constant(Type::Number(_)) = &*$nodeptr.borrow() {
            true
        } else {
            false
        }
    };
    ($nodeptr:expr; boolean) => {
        if let AstNode::Constant(Type::Boolean(_)) = &*$nodeptr.borrow() {
            true
        } else {
            false
        }
    };
    ($nodeptr:expr; nil) => {
        if let AstNode::Constant(Type::Nil(_)) = &*$nodeptr.borrow() {
            true
        } else {
            false
        }
    }
}

macro_rules! get_const_val {
    ($node:expr; number) => {
        if let AstNode::Constant(Type::Number(x)) = &*$node.borrow() {
            x.clone()
        } else {
            panic!("Expected number.")
        }
    };
    ($node:expr; boolean) => {
        if let AstNode::Constant(Type::Boolean(x)) = &*$node.borrow() {
            x.clone()
        } else {
            panic!("Expected boolean.")
        }
    }
}

type Stack<T> = Vec<T>;
pub struct ReductionMachine {
    ast: Ast,
    left_ancestor_stack: Stack<AstNodePtr>
}

impl ReductionMachine {
    pub fn new(ast: Ast) -> Self {
        let stack = vec![Rc::clone(&ast.body)];
        Self {
            ast,
            left_ancestor_stack: stack,
        }
    }

    pub fn reduce(&mut self) -> Result<AstNode, SaslError> {
        loop {
            println!("{}", &self.ast);
            let top = self.left_ancestor_stack.last().unwrap().borrow().clone();
            match top {
                AstNode::App(lhs, _) => self.left_ancestor_stack.push(Rc::clone(&lhs)),
                AstNode::S
                | AstNode::K
                | AstNode::I
                | AstNode::Builtin(_) => {
                    self.reduce_builtin()?;
                    ()
                }
                _ => break
            };
        }
        Ok(self.left_ancestor_stack.last().unwrap().clone().borrow().clone())
    }

    pub fn get_result(&mut self) -> AstNode {
        self.left_ancestor_stack.pop().unwrap().deref().borrow().clone()
    }

    fn throw_compile_err(&self, msg: &str) -> Result<(), SaslError> {
        Err(
            SaslError::CompilerError { msg: msg.to_string() }
        )
    }

    fn reduce_builtin(&mut self) -> Result<(), SaslError> {
        let builtin = self.left_ancestor_stack.pop().unwrap().borrow().clone();
        match builtin {
            AstNode::Builtin(Op::InfixOp(op @ T![+]))
            | AstNode::Builtin(Op::InfixOp(op @ T![-]))
            | AstNode::Builtin(Op::InfixOp(op @ T![*]))
            | AstNode::Builtin(Op::InfixOp(op @ T![/]))
            | AstNode::Builtin(Op::InfixOp(op @ T![=]))
            | AstNode::Builtin(Op::InfixOp(op @ T![~=]))
            | AstNode::Builtin(Op::InfixOp(op @ T![<]))
            | AstNode::Builtin(Op::InfixOp(op @ T![<=]))
            | AstNode::Builtin(Op::InfixOp(op @ T![>]))
            | AstNode::Builtin(Op::InfixOp(op @ T![>=])) 
            | AstNode::Builtin(Op::InfixOp(op @ T![and]))
            | AstNode::Builtin(Op::InfixOp(op @ T![or])) => self.eval_binary(&op),
            AstNode::Builtin(Op::Cond) => todo!("eval cond"),
            AstNode::Builtin(Op::PrefixOp(T![not])) => self.eval_unary(),
            AstNode::Builtin(Op::InfixOp(T![:])) => todo!(),
            AstNode::Builtin(Op::PrefixOp(T![head])) => todo!(),
            AstNode::Builtin(Op::PrefixOp(T![tail])) => todo!(),
            AstNode::S => {
                // S @ f @ g @ x ~> (f @ x) @ (g @ x)
                let f = get_app_child!(rhs(self.left_ancestor_stack.pop().unwrap()));
                let g = get_app_child!(rhs(self.left_ancestor_stack.pop().unwrap()));
                let top = self.left_ancestor_stack.last().unwrap().clone();
                let x = get_app_child!(rhs(top));
                // Build (f @ x) @ (g @ x)
                let f_at_x = AstNode::App(ptr!(f.borrow().clone()), ptr!(x.borrow().clone()));
                let g_at_x = AstNode::App(ptr!(g.borrow().clone()), ptr!(x.borrow().clone()));
                set_app_child_value!(lhs(top) = f_at_x);
                set_app_child_value!(rhs(top) = g_at_x);
                Ok(())
            }
            AstNode::K => {
                // (K @ x) @ y ~> I @ x
                let x = get_app_child!(rhs(self.left_ancestor_stack.pop().unwrap()));
                let mut top = self.left_ancestor_stack.last().unwrap().clone();
                // Build I @ x
                set_app_child_value!(rhs(&mut top) = x.borrow().clone());
                set_app_child_value!(lhs(top) = AstNode::I);
                Ok(())
            }
            AstNode::I => {
                // I @ x ~> x
                let x = get_app_child!(rhs(self.left_ancestor_stack.pop().unwrap()));
                self.left_ancestor_stack.push(x);
                Ok(())
            }
            _ => todo!()
        }
    }

    fn eval_binary(&mut self, op: &Type) -> Result<(), SaslError> {
        let lhs = get_app_child!(rhs(self.left_ancestor_stack.pop().unwrap()));
        let top = self.left_ancestor_stack.last().unwrap().clone();
        let rhs = get_app_child!(rhs(top));

        self.left_ancestor_stack.push(lhs);
        self.reduce()?;
        let lhs = self.left_ancestor_stack.pop().unwrap();

        self.left_ancestor_stack.push(rhs);
        self.reduce()?;
        let rhs = self.left_ancestor_stack.pop().unwrap();

        set_app_child_value!(lhs(top) = AstNode::I);
        // Eval binary arithmetic operators
        if check_type!(&lhs; number) && check_type!(&rhs; number) {
            let num_lhs = get_const_val!(lhs; number);
            let num_rhs = get_const_val!(rhs; number);
            match op {
                T![+] => set_app_child_value!(rhs(top) = AstNode::Constant(Type::Number(num_lhs + num_rhs))),
                T![-] => set_app_child_value!(rhs(top) = AstNode::Constant(Type::Number(num_lhs - num_rhs))),
                T![*] => set_app_child_value!(rhs(top) = AstNode::Constant(Type::Number(num_lhs * num_rhs))),
                T![/] => set_app_child_value!(rhs(top) = AstNode::Constant(Type::Number(num_lhs / num_rhs))),
                T![=] => set_app_child_value!(rhs(top) = AstNode::Constant(Type::Boolean(num_lhs == num_rhs))),
                T![~=] => set_app_child_value!(rhs(top) = AstNode::Constant(Type::Boolean(num_lhs != num_rhs))),
                T![<] => set_app_child_value!(rhs(top) = AstNode::Constant(Type::Boolean(num_lhs < num_rhs))),
                T![<=] => set_app_child_value!(rhs(top) = AstNode::Constant(Type::Boolean(num_lhs <= num_rhs))),
                T![>] => set_app_child_value!(rhs(top) = AstNode::Constant(Type::Boolean(num_lhs > num_rhs))),
                T![>=] => set_app_child_value!(rhs(top) = AstNode::Constant(Type::Boolean(num_lhs >= num_rhs))),
                _ => todo!()
            }
        // Eval binary logic operators
        } else if check_type!(&lhs; boolean) && check_type!(&rhs; boolean) {
            let bool_lhs = get_const_val!(lhs; boolean);
            let bool_rhs = get_const_val!(rhs; boolean);
            match op {
                T![=] => set_app_child_value!(rhs(top) = AstNode::Constant(Type::Boolean(bool_lhs == bool_rhs))),
                T![~=] => set_app_child_value!(rhs(top) = AstNode::Constant(Type::Boolean(bool_lhs != bool_rhs))),
                T![and] => set_app_child_value!(rhs(top) = AstNode::Constant(Type::Boolean(bool_lhs && bool_rhs))),
                T![or] => set_app_child_value!(rhs(top) = AstNode::Constant(Type::Boolean(bool_lhs || bool_rhs))),
                _ => todo!()
            }
        }
        // Eval comparions with Nil!
        
        Ok(())
    } 

    fn eval_unary(&mut self) -> Result<(), SaslError> {
        // (not @ bool) ? not already borrowed !!
        let top = self.left_ancestor_stack.last().unwrap().clone();
        let rhs = get_app_child!(rhs(top));

        self.left_ancestor_stack.push(rhs);
        self.reduce()?;
        let rhs = self.left_ancestor_stack.pop().unwrap();

        set_app_child_value!(lhs(top) = AstNode::I);
        if check_type!(&rhs; boolean) {
            let rhs_val = get_const_val!(rhs; boolean);
            set_app_child_value!(rhs(top) = AstNode::Constant(Type::Boolean(!rhs_val)));
            Ok(())
        } else {
            self.throw_compile_err("Semantic Error: Expected boolean expression after not")
        }
    }


}

