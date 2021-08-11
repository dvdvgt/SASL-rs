//! This module contains the implementation of a virtual machine used for evaluating a SASL program.

use crate::frontend::token::Type;
use crate::{
    error::SaslError,
    frontend::ast::{Ast, AstNode, AstNodePtr, Op},
};
use crate::{ptr, T, set_app_child_value, get_app_child, get_const_val, get_pair_child, match_astnode, check_type};
use std::{cell::RefCell, ops::Deref, rc::Rc};

/// Specifies where a global definition occured - as the left or right child
/// of a application node.
enum DefPosition {
    Lhs,
    Rhs,
}

/// The vector datastructure is used as simple stack by the virtual machine hence the type alias.
type Stack<T> = Vec<T>;

/// The reduction machine is a virtual machine used for evaluating a SASL program until a
/// single, printable atomic value is reached i.e. Number, Boolean, String, List.
pub struct ReductionMachine {
    ast: Ast,
    left_ancestor_stack: Stack<AstNodePtr>,
    /// Activate optimizations or evaluate without any
    optimize: bool
}

impl ReductionMachine {
    pub fn new(ast: Ast, optimize: bool) -> Self {
        let stack = vec![Rc::clone(&ast.body)];
        Self {
            ast,
            left_ancestor_stack: stack,
            optimize
        }
    }

    /// Helper functions for peeking at the last element of the `left_ancestor_stack`.
    pub fn peek_stack(&self) -> AstNode {
        self.left_ancestor_stack.last().unwrap().borrow().clone()
    }

    /// Helper function for conveniently throwing a compiler error.
    fn throw_compile_err(&self, msg: &str) -> Result<(), SaslError> {
        Err(SaslError::CompilerError {
            msg: msg.to_string(),
        })
    }

    /// Returns the result as a string after the reduction has finished.
    pub fn print_result(&mut self) -> Result<String, SaslError> {
        let mut top = self.peek_stack();
        // If the top of the stack contains a pair it still needs to be reduced in order to
        // be printable due to lazy evaluation.
        if let AstNode::Pair(_, _) = top {
            let mut out_str = "[".to_string();
            while let AstNode::Pair(lhs, rhs) = top {
                self.left_ancestor_stack.pop();
                // Reduce the list head and recursivly create the corresponding string
                // in case the list head is a list itself.
                self.left_ancestor_stack.push(lhs.clone());
                self.reduce()?;
                out_str.push_str(&self.print_result()?);

                // Reduce the tail of the list
                self.left_ancestor_stack.push(rhs.clone());
                self.reduce()?;

                // Check if the end of the list was reached
                let rhs = self.peek_stack();
                if let AstNode::Constant(T![nil]) = rhs {
                    out_str.push(']');
                    break;
                } else {
                    out_str.push_str(", ");
                }
                top = self.peek_stack();
            }
            Ok(out_str)
        } else {
            // If the Node is not a list it can simply be converted into a string
            Ok(self.peek_stack().to_string())
        }
    }

    ///
    pub fn reduce(&mut self) -> Result<(), SaslError> {
        // Main loop of the left ancestor stack. Nodes are pushed onto the stack until a left leaf is reached
        // where the reduction kicks in.
        loop {
            let top = self.peek_stack();
            match top {
                // Handle global definitions which are still to be inserted in place of their identifier.
                AstNode::App(lhs, rhs) => {
                    let lhs_ = lhs.borrow().clone();
                    let rhs_ = rhs.borrow().clone();
                    match (lhs_, rhs_) {
                        // Something like `f @ x` where both f and x are global definitions
                        (AstNode::Ident(s1), AstNode::Ident(s2)) => {
                            self.insert_global_def(s1.clone(), DefPosition::Lhs)?;
                            self.insert_global_def(s2.clone(), DefPosition::Rhs)?;
                        }
                        // Something like `1 + x` where x is a global definition
                        (_, AstNode::Ident(s)) => {
                            self.insert_global_def(s.clone(), DefPosition::Rhs)?
                        }
                        // Something like `f 1` where f is a globally defined function
                        (AstNode::Ident(s), _) => {
                            self.insert_global_def(s.clone(), DefPosition::Lhs)?
                        }
                        // Otherwise both are builtins or literals. Just the left child onto the stack
                        (_, _) => self.left_ancestor_stack.push(Rc::clone(&lhs)),
                    }
                }
                AstNode::S
                | AstNode::S_
                | AstNode::K
                | AstNode::I
                | AstNode::Y
                | AstNode::U
                | AstNode::B
                | AstNode::C
                | AstNode::C_
                | AstNode::B_
                | AstNode::Builtin(_) => {
                    self.reduce_builtin()?;
                    ()
                }
                // Handle a single global definition
                AstNode::Ident(s) => {
                    *self.left_ancestor_stack.last().unwrap().borrow_mut() =
                        self.ast.global_defs.get(&s).unwrap().1.borrow().clone();
                }
                _ => break,
            };
        }
        Ok(())
    }

    // distribute the reduction steps
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
            AstNode::Builtin(Op::Cond) => self.eval_cond(),
            AstNode::Builtin(Op::PrefixOp(T![not])) => self.eval_unary(),
            AstNode::Builtin(Op::InfixOp(T![:])) => self.eval_cons(),
            AstNode::Builtin(Op::PrefixOp(T![head])) => self.eval_hd(),
            AstNode::Builtin(Op::PrefixOp(T![tail])) => self.eval_tl(),
            AstNode::S => self.eval_s(),
            AstNode::K => self.eval_k(),
            AstNode::I => self.eval_i(),
            AstNode::Y => self.eval_y(),
            AstNode::U => self.eval_u(),
            AstNode::S_ => self.eval_s_(),
            AstNode::B => self.eval_b(),
            AstNode::B_ => self.eval_b_star(),
            AstNode::C => self.eval_c(),
            AstNode::C_ => self.eval_c_(),
            _ => panic!(),
        }
    }
    //reduction of S'
    fn eval_s_(&mut self) -> Result<(), SaslError> {
        //c @ (f @ x) @ (g @ x)
        let c = get_app_child!(rhs(self.left_ancestor_stack.pop().unwrap()));
        let f = get_app_child!(rhs(self.left_ancestor_stack.pop().unwrap()));
        let g = get_app_child!(rhs(self.left_ancestor_stack.pop().unwrap()));
        let top = self.left_ancestor_stack.last().unwrap().clone();
        let x = get_app_child!(rhs(top));
        //Create (f @ x) and (g @ x ) and (c @ ( f @ x))
        let f_and_x = AstNode::App(ptr!(f.borrow().clone()), ptr!(x.borrow().clone()));
        let g_and_x = AstNode::App(ptr!(g.borrow().clone()), ptr!(x.borrow().clone()));

        let c_f_and_x = AstNode::App(ptr!(c.borrow().clone()), ptr!(f_and_x));
        //set app childs
        set_app_child_value!(lhs(top) = c_f_and_x);
        set_app_child_value!(rhs(top) = g_and_x);
        Ok(())
    }
    //redcution of B
    fn eval_b(&mut self) -> Result<(), SaslError> {
        // B @ f @ g @ x ~> f @ (g @ x)
        let f = get_app_child!(rhs(self.left_ancestor_stack.pop().unwrap()));
        let g = get_app_child!(rhs(self.left_ancestor_stack.pop().unwrap()));
        let top = self.left_ancestor_stack.last().unwrap().clone();
        let x = get_app_child!(rhs(top));
        //Create (g @ x)
        let g_and_x = AstNode::App(ptr!(g.borrow().clone()), ptr!(x.borrow().clone()));
        //set app childs
        set_app_child_value!(lhs(top) = f.borrow().clone());
        set_app_child_value!(rhs(top) = g_and_x);

        Ok(())
    }
    //Reduction of B*
    fn eval_b_star(&mut self) -> Result<(), SaslError> {
        // c @ (f @ (g @ x))
        let c = get_app_child!(rhs(self.left_ancestor_stack.pop().unwrap()));
        let f = get_app_child!(rhs(self.left_ancestor_stack.pop().unwrap()));
        let g = get_app_child!(rhs(self.left_ancestor_stack.pop().unwrap()));
        let top = self.left_ancestor_stack.last().unwrap().clone();
        let x = get_app_child!(rhs(top));
        //Create ( g @ x) and ( f @ ( g @ x))
        let g_and_x = AstNode::App(ptr!(g.borrow().clone()), ptr!(x.borrow().clone()));
        let f_and_g_and_x = AstNode::App(ptr!(f.borrow().clone()), ptr!(g_and_x));
        //set app childs
        set_app_child_value!(lhs(top) = c.borrow().clone());
        set_app_child_value!(rhs(top) = f_and_g_and_x);
        Ok(())
    }
    //Reduction of C
    fn eval_c(&mut self) -> Result<(), SaslError> {
        // f @ x @ g
        let f = get_app_child!(rhs(self.left_ancestor_stack.pop().unwrap()));
        let g = get_app_child!(rhs(self.left_ancestor_stack.pop().unwrap()));
        let top = self.left_ancestor_stack.last().unwrap().clone();
        let x = get_app_child!(rhs(top));
        //Create (f @ x)
        let f_and_x = AstNode::App(ptr!(f.borrow().clone()), ptr!(x.borrow().clone()));
        //set app childs
        set_app_child_value!(rhs(top) = g.borrow().clone());
        set_app_child_value!(lhs(top) = f_and_x);

        Ok(())
    }
    //reduction of C'
    fn eval_c_(&mut self) -> Result<(), SaslError> {
        // c @ (f @ x) @ g )
        let c = get_app_child!(rhs(self.left_ancestor_stack.pop().unwrap()));
        let f = get_app_child!(rhs(self.left_ancestor_stack.pop().unwrap()));
        let g = get_app_child!(rhs(self.left_ancestor_stack.pop().unwrap()));
        let top = self.left_ancestor_stack.last().unwrap().clone();
        let x = get_app_child!(rhs(top));
        //Create ( f @ x) and ( c @ ( f @ x))
        let f_and_x = AstNode::App(ptr!(f.borrow().clone()), ptr!(x.borrow().clone()));
        let c_and_f_and_x = AstNode::App(ptr!(c.borrow().clone()), ptr!(f_and_x));
        //set app childs
        set_app_child_value!(rhs(top) = g.borrow().clone());
        set_app_child_value!(lhs(top) = c_and_f_and_x);
        Ok(())
    }
    //reduction of recursion
    fn eval_y(&mut self) -> Result<(), SaslError> {
        // f @ (Y @ f)
        let top = self.left_ancestor_stack.last().unwrap().clone();
        let f = get_app_child!(rhs(top)).deref().borrow().clone();
        // Create ( Y @ f)
        let y_and_f = AstNode::App(ptr!(AstNode::Y), ptr!(f.clone()));
        set_app_child_value!(rhs(top) = y_and_f);

        set_app_child_value!(lhs(top) = f);
        Ok(())
    }
    //reduction for several variables
    fn eval_u(&mut self) -> Result<(), SaslError> {
        // (f @ (hd @ z)) @ (tl @ z)
        let f = get_app_child!(rhs(self.left_ancestor_stack.pop().unwrap()));
        let top = self.left_ancestor_stack.last().unwrap().clone();
        let z = get_app_child!(rhs(top));

        // Create (hd @ z)
        let hd_and_z = AstNode::App(
            ptr!(AstNode::Builtin(Op::PrefixOp(T![head]))),
            ptr!(z.borrow().clone()),
        );
        //Create(tl @ z)
        let tl_and_z = AstNode::App(
            ptr!(AstNode::Builtin(Op::PrefixOp(T![tail]))),
            ptr!(z.borrow().clone()),
        );
        //Create (f @ (tl @ z))
        let f_hd_and_z = AstNode::App(ptr!(f.borrow().clone()), ptr!(hd_and_z));

        set_app_child_value!(lhs(top) = f_hd_and_z);
        set_app_child_value!(rhs(top) = tl_and_z);
        Ok(())
    }

    fn eval_s(&mut self) -> Result<(), SaslError> {
        // switch to turn of/ on the optimization
        if self.optimize {
            //optimization
            self.optimize()?;
            Ok(())
        } else {
            // S @ f @ g @ x ~> (f @ x) @ (g @ x)
            let f = get_app_child!(rhs(self.left_ancestor_stack.pop().unwrap()));
            let g = get_app_child!(rhs(self.left_ancestor_stack.pop().unwrap()));
            let top = self.left_ancestor_stack.last().unwrap().clone();
            let x = get_app_child!(rhs(top));

            //Create ( f @ x) and ( g @ x)
            let f_and_x = AstNode::App(ptr!(f.borrow().clone()), ptr!(x.borrow().clone()));
            let g_and_x = AstNode::App(ptr!(g.borrow().clone()), ptr!(x.borrow().clone()));
            set_app_child_value!(lhs(top) = f_and_x);
            set_app_child_value!(rhs(top) = g_and_x);
            //println!("hier, {}", &*top.borrow());
            Ok(())
        }
    }

    fn optimize(&mut self) -> Result<(), SaslError> {
        // fib 5 where fib n = if (n=0) or (n=1) then 1 else (fib (n-1)) + (fib (n-2))
        fn eval_s(x: AstNodePtr, y: AstNodePtr, next_top: AstNodePtr) {
            // No optimization possible: S @ x @ y @ z ~> (x @ z) @ (y @ z)
            let z = get_app_child!(rhs(next_top));

            let x_at_z = AstNode::App(ptr!(x.borrow().clone()), ptr!(z.borrow().clone()));
            let y_at_z = AstNode::App(ptr!(y.borrow().clone()), ptr!(z.borrow().clone()));
            set_app_child_value!(lhs(next_top) = x_at_z);
            set_app_child_value!(rhs(next_top) = y_at_z);
        }
        // S @ x @ y where S was already poped from the stack
        // ^ not in stack
        //   ^ On top of stack when this function is called
        let x = get_app_child!(rhs(self.left_ancestor_stack.pop().unwrap()));
        let top = self.left_ancestor_stack.last().unwrap().clone();
        let y = get_app_child!(rhs(top));
        // Stack: S @ x @ y
        //              ^ top of stack
        if match_astnode!(x; app) {
            let x_lhs = get_app_child!(lhs(x));
            let x_rhs = get_app_child!(rhs(x));
            if match_astnode!(x_lhs; K) {
                if match_astnode!(y; app) {
                    let y_lhs = get_app_child!(lhs(y));
                    let y_rhs = get_app_child!(rhs(y));
                    if match_astnode!(y_lhs; K) {
                        // Rule 1: S @ (K @ f) @ (K @ g) ~> K @ (f @ g)
                        // x = (K @ f), y = (K @ g), x_rhs = f, y_rhs = g
                        set_app_child_value!(lhs(top) = AstNode::K);
                        let f_at_g = AstNode::App(
                            ptr!(x_rhs.borrow().clone()),
                            ptr!(y_rhs.borrow().clone()),
                        );
                        set_app_child_value!(rhs(top) = f_at_g);
                    } else if match_astnode!(y_lhs; app)
                        && match_astnode!(get_app_child!(lhs(y_lhs)); B)
                    {
                        // Rule 3; S @ (K @ f) @ (B @ g @ h) ~> B* @ f @ g @ h
                        // f = x_rhs, g = y_lhs_rhs, h = y_rhs
                        let y_lhs_rhs = get_app_child!(rhs(y_lhs));
                        let b_at_f = AstNode::App(ptr!(AstNode::B_), ptr!(x_rhs.borrow().clone()));
                        let b_at_f_at_g =
                            AstNode::App(ptr!(b_at_f), ptr!(y_lhs_rhs.borrow().clone()));
                        set_app_child_value!(lhs(top) = b_at_f_at_g);
                        set_app_child_value!(rhs(top) = y_rhs.borrow().clone());
                    } else {
                        self.left_ancestor_stack.pop();
                        eval_s(x, y, self.left_ancestor_stack.last().unwrap().clone());
                    }
                } else if match_astnode!(y; I) {
                    // Rule 2: S @ (K @ f) @ I
                    // f = x_rhs
                    *top.borrow_mut() = x_rhs.borrow().clone();
                } else {
                    // Rule 4: S @ (K @ f) @ g ~> B @ f @ g
                    // x = (K @ f), g = y, x_rhs = f
                    let b_at_f = AstNode::App(ptr!(AstNode::B), ptr!(x_rhs.borrow().clone()));
                    set_app_child_value!(lhs(top) = b_at_f);
                }
            } else if match_astnode!(x_lhs; app) {
                let x_lhs_lhs = get_app_child!(lhs(x_lhs));
                let x_lhs_rhs = get_app_child!(rhs(x_lhs));
                if match_astnode!(x_lhs_lhs; B) {
                    if match_astnode!(y; app) && match_astnode!(get_app_child!(lhs(y)); K) {
                        // Rule 5: S @ (B @ f @ g) @ (K @ h) ~> C' @ f @ g @ h
                        // f = x_lhs_rhs, g = x_rhs, h = y_rhs
                        let y_rhs = get_app_child!(rhs(y));
                        let c_at_f_at_g = AstNode::App(
                            ptr!(AstNode::App(
                                ptr!(AstNode::C_),
                                ptr!(x_lhs_rhs.borrow().clone())
                            )),
                            ptr!(x_rhs.borrow().clone()),
                        );
                        set_app_child_value!(lhs(top) = c_at_f_at_g);
                        set_app_child_value!(rhs(top) = y_rhs.borrow().clone());
                    } else {
                        // Rule 7: S @ (B @ f @ g) @ h ~> S' @ f @ g @ h
                        // f = x_lhs_rhs, g = x_rhs, h = y
                        let s_at_f_at_g = AstNode::App(
                            ptr!(AstNode::App(
                                ptr!(AstNode::S_),
                                ptr!(x_lhs_rhs.borrow().clone())
                            )),
                            ptr!(x_rhs.borrow().clone()),
                        );
                        set_app_child_value!(lhs(top) = s_at_f_at_g);
                    }
                } else {
                    self.left_ancestor_stack.pop();
                    eval_s(x, y, self.left_ancestor_stack.last().unwrap().clone());
                }
            } else {
                self.left_ancestor_stack.pop();
                eval_s(x, y, self.left_ancestor_stack.last().unwrap().clone());
            }
        } else {
            if match_astnode!(y; app) && match_astnode!(get_app_child!(lhs(y)); K) {
                // Rule 6: S @ f @ (K @ g) ~> C @ f @ g
                // f = x, g = y_rhs
                let y_rhs = get_app_child!(rhs(y));
                let c_at_f = AstNode::App(ptr!(AstNode::C), ptr!(x.borrow().clone()));
                set_app_child_value!(lhs(top) = c_at_f);
                set_app_child_value!(rhs(top) = y_rhs.borrow().clone());
            } else {
                self.left_ancestor_stack.pop();
                eval_s(x, y, self.left_ancestor_stack.last().unwrap().clone());
            }
        }
        Ok(())
    }

    fn eval_k(&mut self) -> Result<(), SaslError> {
        //I @ x
        let x = get_app_child!(rhs(self.left_ancestor_stack.pop().unwrap()));
        //self.left_ancestor_stack.pop();
        let mut top = self.left_ancestor_stack.last().unwrap().clone();
        //Build

        set_app_child_value!(rhs(&mut top) = x.borrow().clone());
        set_app_child_value!(lhs(top) = AstNode::I);
        Ok(())
    }

    pub fn eval_i(&mut self) -> Result<(), SaslError> {
        //x
        let x = get_app_child!(rhs(self.left_ancestor_stack.pop().unwrap()));
        self.left_ancestor_stack.push(x);
        Ok(())
    }
    //reduce binary operations
    fn eval_binary(&mut self, op: &Type) -> Result<(), SaslError> {
        //println!("stack,{}", &self.left_ancestor_stack.last().unwrap().borrow().clone());
        let lhs = get_app_child!(rhs(self.left_ancestor_stack.pop().unwrap()));
        //println!("stack,{}", &self.left_ancestor_stack.last().unwrap().borrow().clone());
        let top = self.left_ancestor_stack.last().unwrap().clone();
        let rhs = get_app_child!(rhs(top));
        //reduce to the value of lhs
        self.left_ancestor_stack.push(lhs);
        self.reduce()?;
        let lhs = self.left_ancestor_stack.pop().unwrap();
        //reduce to the value of rhs
        self.left_ancestor_stack.push(rhs);
        self.reduce()?;
        let rhs = self.left_ancestor_stack.pop().unwrap();

        set_app_child_value!(lhs(top) = AstNode::I);
        // Eval binary arithmetic operators
        if check_type!(&lhs; number) && check_type!(&rhs; number) {
            let num_lhs = get_const_val!(lhs; number);
            let num_rhs = get_const_val!(rhs; number);

            match op {
                T![+] => {
                    set_app_child_value!(
                        rhs(top) = AstNode::Constant(Type::Number(num_lhs + num_rhs))
                    );
                    Ok(())
                }
                T![-] => {
                    set_app_child_value!(
                        rhs(top) = AstNode::Constant(Type::Number(num_lhs - num_rhs))
                    );
                    Ok(())
                }
                T![*] => {
                    set_app_child_value!(
                        rhs(top) = AstNode::Constant(Type::Number(num_lhs * num_rhs))
                    );
                    Ok(())
                }
                T![/] => {
                    set_app_child_value!(
                        rhs(top) = AstNode::Constant(Type::Number(num_lhs / num_rhs))
                    );
                    Ok(())
                }
                T![=] => {
                    set_app_child_value!(
                        rhs(top) = AstNode::Constant(Type::Boolean(num_lhs == num_rhs))
                    );
                    Ok(())
                }
                T![~=] => {
                    set_app_child_value!(
                        rhs(top) = AstNode::Constant(Type::Boolean(num_lhs != num_rhs))
                    );
                    Ok(())
                }
                T![<] => {
                    set_app_child_value!(
                        rhs(top) = AstNode::Constant(Type::Boolean(num_lhs < num_rhs))
                    );
                    Ok(())
                }
                T![<=] => {
                    set_app_child_value!(
                        rhs(top) = AstNode::Constant(Type::Boolean(num_lhs <= num_rhs))
                    );
                    Ok(())
                }
                T![>] => {
                    set_app_child_value!(
                        rhs(top) = AstNode::Constant(Type::Boolean(num_lhs > num_rhs))
                    );
                    Ok(())
                }
                T![>=] => {
                    set_app_child_value!(
                        rhs(top) = AstNode::Constant(Type::Boolean(num_lhs >= num_rhs))
                    );
                    Ok(())
                }
                _ => self.throw_compile_err(&format!(
                    "Expected arithmetic operation or comparison. Found {} instead.",
                    &op
                )),
            }
            // Eval binary logic operators
        } else if check_type!(&lhs; boolean) && check_type!(&rhs; boolean) {
            let bool_lhs = get_const_val!(lhs; boolean);
            let bool_rhs = get_const_val!(rhs; boolean);
            match op {
                T![=] => {
                    set_app_child_value!(
                        rhs(top) = AstNode::Constant(Type::Boolean(bool_lhs == bool_rhs))
                    );
                    Ok(())
                }
                T![~=] => {
                    set_app_child_value!(
                        rhs(top) = AstNode::Constant(Type::Boolean(bool_lhs != bool_rhs))
                    );
                    Ok(())
                }
                T![and] => {
                    set_app_child_value!(
                        rhs(top) = AstNode::Constant(Type::Boolean(bool_lhs && bool_rhs))
                    );
                    Ok(())
                }
                T![or] => {
                    set_app_child_value!(
                        rhs(top) = AstNode::Constant(Type::Boolean(bool_lhs || bool_rhs))
                    );
                    Ok(())
                }
                _ => self.throw_compile_err(&format!(
                    "Expected binary logic operation (=, ~=, and, or). Found {} instead.",
                    &op
                )),
            }
        // Eval comparions with Nil!
        //both Paramter are nil
        } else if check_type!(&lhs; nil) && check_type!(&rhs; nil) {
            match op {
                T![=] => {
                    set_app_child_value!(rhs(top) = AstNode::Constant(Type::Boolean(true)));
                    Ok(())
                }
                T![~=] => {
                    set_app_child_value!(rhs(top) = AstNode::Constant(Type::Boolean(false)));
                    Ok(())
                }
                _ => self.throw_compile_err(&format!("Expected list comparison. Found {} instead.", &op)),
            }

        //Only one Parameter ist nil
        } else if check_type!(&lhs; nil) || check_type!(&rhs; nil) {
            match op {
                T![=] => {
                    set_app_child_value!(rhs(top) = AstNode::Constant(Type::Boolean(false)));
                    Ok(())
                }
                T![~=] => {
                    set_app_child_value!(rhs(top) = AstNode::Constant(Type::Boolean(true)));
                    Ok(())
                }
                _ => self.throw_compile_err(&format!("Expected list comparison. Found {} instead.", &op)),
            }
        } else {
            self.throw_compile_err(&format!("Unkown binary operation: {}", op))
        }
    }
    //eval unary oparions
    fn eval_unary(&mut self) -> Result<(), SaslError> {
        // (not @ bool) ? not already borrowed !!
        let top = self.left_ancestor_stack.last().unwrap().clone();
        let rhs = get_app_child!(rhs(top));
        //reduce to the value of rhs
        self.left_ancestor_stack.push(rhs);
        self.reduce()?;
        let rhs = self.left_ancestor_stack.pop().unwrap();

        set_app_child_value!(lhs(top) = AstNode::I);
        if check_type!(&rhs; boolean) {
            let rhs_val = get_const_val!(rhs; boolean);
            set_app_child_value!(rhs(top) = AstNode::Constant(Type::Boolean(!rhs_val)));
            Ok(())
        } else {
            self.throw_compile_err(&format!("Compilation error: Expected boolean expression after not. Found {} instead.", &*rhs.borrow()))
        }
    }
    //reduce if conditions
    fn eval_cond(&mut self) -> Result<(), SaslError> {
        //gets the boolean predicate
        let predicate = get_app_child!(rhs(self.left_ancestor_stack.pop().unwrap()));
        // reduce predicate to true or false

        self.left_ancestor_stack.push(predicate);
        self.reduce()?;
        let predicate = self.left_ancestor_stack.pop().unwrap();

        if get_const_val!(predicate; boolean) {
            //condition is true
            let true_val = get_app_child!(rhs(self.left_ancestor_stack.pop().unwrap()))
                .borrow()
                .clone();

            let top = self.left_ancestor_stack.last().unwrap().clone();
            set_app_child_value!(lhs(top) = AstNode::I);
            set_app_child_value!(rhs(top) = true_val);
        } else {
            //condition is false
            self.left_ancestor_stack.pop().unwrap();
            let top = self.left_ancestor_stack.last().unwrap().clone();

            set_app_child_value!(lhs(top) = AstNode::I);
        }
        Ok(())
    }

    fn eval_hd(&mut self) -> Result<(), SaslError> {
        let top = self.left_ancestor_stack.last().unwrap().clone();

        let pair = get_app_child!(rhs(top));

        // reduce list to pair
        self.left_ancestor_stack.push(pair);
        self.reduce()?;
        let pair = self.left_ancestor_stack.pop().unwrap();
        // get left pair child
        let x = get_pair_child!(lhs(pair));
        set_app_child_value!(rhs(top) = x.borrow().clone());
        set_app_child_value!(lhs(top) = AstNode::I);

        Ok(())
    }

    fn eval_tl(&mut self) -> Result<(), SaslError> {
        let top = self.left_ancestor_stack.last().unwrap().clone();
        let pair = get_app_child!(rhs(top));
        //reduce list to pair
        self.left_ancestor_stack.push(pair);
        self.reduce()?;
        let pair = self.left_ancestor_stack.pop().unwrap();
        //get right pair child
        let x = get_pair_child!(rhs(pair));

        set_app_child_value!(rhs(top) = x.borrow().clone());

        set_app_child_value!(lhs(top) = AstNode::I);

        Ok(())
    }
    //reduce a list
    fn eval_cons(&mut self) -> Result<(), SaslError> {
        let x = get_app_child!(rhs(self.left_ancestor_stack.pop().unwrap()));
        let top = self.left_ancestor_stack.last().unwrap().clone();
        let y = get_app_child!(rhs(top));

        set_app_child_value!(lhs(top) = AstNode::I);
        //make a list to a pair
        let pair = AstNode::Pair(
            ptr!(x.borrow().deref().clone()),
            ptr!(y.borrow().deref().clone()),
        );
        set_app_child_value!(rhs(top) = pair);
        Ok(())
    }

    fn insert_global_def(&mut self, s: String, def_pos: DefPosition) -> Result<(), SaslError> {
        let top = self.left_ancestor_stack.last().unwrap().clone();
        //look into Hashmap
        let x = self
            .ast
            .global_defs
            .get(&s)
            .unwrap_or_else(|| panic!("Could not find global definition for {}.", &s))
            .1
            .deref()
            .borrow()
            .clone();
        match def_pos {
            DefPosition::Lhs => set_app_child_value!(lhs(top) = x),
            DefPosition::Rhs => set_app_child_value!(rhs(top) = x),
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend::{lexer::*, parser::*};
    use crate::backend::abstractor::compile;

    fn evaluate(code: &str) -> String {
        let mut ast = Parser::new(Lexer::new(code).tokenize().unwrap())
            .parse()
            .unwrap();
        compile(&mut ast).unwrap();
        let mut vm = ReductionMachine::new(ast, true);
        vm.reduce().unwrap();
        vm.print_result().unwrap()
    }

    #[test]
    fn test_simple_operations() {
        let result = evaluate( "1 + 6 * 5 / 3");
        assert_eq!(result, "11");

        let result = evaluate("[1,2,3] ~= nil");
        assert_eq!(result, "true");

        let result = evaluate("hd [1,2,\"ab\", false]");
        assert_eq!(result, "1");

        let result = evaluate("tl (hd [[1,2,3],4])");
        assert_eq!(result, "[2, 3]");

        let result = evaluate("a or b where a = true; b = false");
        assert_eq!(result, "true");

        let result = evaluate("1 / 3 > 0.33");
        assert_eq!(result, "true");
    }

    #[test]
    fn test_complex_programs() {
        let program = std::fs::read_to_string("reference-bin/example.sasl").unwrap();
        assert_eq!(evaluate(&program), "5050");

        let program = std::fs::read_to_string("reference-bin/sieve.sasl").unwrap();
        assert_eq!(
            evaluate(&program),
            "[2, 3, 5, 7, 11, 13, 17, 19, 23, 29]"
        );

        let program = "f where f = g + 1; g = 1";
        assert_eq!(
            evaluate(&program),
            "2"
        );
        let program = "f where g = 1; f = g + 1";
        assert_eq!(
            evaluate(&program),
            "2"
        );
    }
}
