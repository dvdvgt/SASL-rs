use crate::frontend::token::Type;
use crate::{
    error::SaslError,
    frontend::ast::{Ast, AstNode, AstNodePtr, Op},
};
use crate::{ptr, T};
use std::{cell::RefCell, ops::Deref, rc::Rc};
use std::io::empty;

macro_rules! get_app_child {
    (rhs($node:expr)) => {
        match &*$node.borrow() {
            AstNode::App(_, rhs) => Rc::clone(&rhs),
            _ => panic!(),
        }
    };
    (lhs($node:expr)) => {
        match &*$node.borrow() {
            AstNode::App(lhs, _) => Rc::clone(&lhs),
            _ => panic!(),
        }
    };
}

macro_rules! get_pair_child {
    (rhs($node:expr)) => {
        match &*$node.borrow() {
            AstNode::Pair(_, rhs) => Rc::clone(rhs),
            _ => panic!(),
        }
    };
    (lhs($node:expr)) => {
        match &*$node.borrow() {
            AstNode::Pair(lhs, _) => Rc::clone(lhs),
            _ => panic!(),
        }
    };
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
    };
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
    ($nodeptr:expr; string) => {
        if let AstNode::Constant(Type::String(_)) = &*$nodeptr.borrow() {
            true
        } else {
            false
        }
    };
    ($nodeptr:expr; nil) => {
        if let AstNode::Constant(Type::Nil) = &*$nodeptr.borrow() {
            true
        } else {
            false
        }
    };
    ($nodeptr:expr; pair) => {
        if let AstNode::Pair(_,_) = &*$nodeptr.borrow() {
            true
        } else {
            false
        }
    };
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
    };
    ($node:expr; string) => {
        if let AstNode::Constant(Type::String(x)) = &*$node.borrow() {
            x.clone()
        } else {
            panic!("Expected string.")
        }
    };
}

enum DefPosition {
    Lhs,
    Rhs,
}
type Stack<T> = Vec<T>;
pub struct ReductionMachine {
    ast: Ast,
    left_ancestor_stack: Stack<AstNodePtr>,
}

impl ReductionMachine {
    pub fn new(ast: Ast) -> Self {
        let stack = vec![Rc::clone(&ast.body)];
        Self {
            ast,
            left_ancestor_stack: stack,
        }
    }
    // Control of reduction

    pub fn reduce(&mut self) -> Result<AstNode, SaslError> {
        // if no more action steps are to be executed, the loop terminates
        loop {
            println!("{}", &self.ast);
            let top = self.left_ancestor_stack.last().unwrap().borrow().clone();
            match top {
                AstNode::App(lhs, rhs) => {
                    let lhs_ = lhs.borrow().clone();
                    let rhs_ = rhs.borrow().clone();
                    match (lhs_,rhs_) {
                        (AstNode::Ident(s1), AstNode::Ident(s2)) => {
                            self.reduce_global_defs(s1.clone(), DefPosition::Lhs)?;
                            self.reduce_global_defs(s2.clone(), DefPosition::Rhs)?;
                        }
                        (AstNode::Ident(s), _) => {
                            self.reduce_global_defs(s.clone(), DefPosition::Lhs)?;
                        }
                        (_, AstNode::Ident(s)) => {
                            self.reduce_global_defs(s.clone(), DefPosition::Rhs)?;
                        }
                        (_,_) => self.left_ancestor_stack.push(Rc::clone(&lhs))
                    }

                },
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
                },
                AstNode::Ident(s) => {
                    *self.left_ancestor_stack.last().unwrap().borrow_mut() = self.ast.global_defs.get(&s).unwrap().1.borrow().clone();
                }
                _ => break,
            };
        }
        /*loop {
            if check_type!( &self.left_ancestor_stack.last(); pair ){
                let lhs = get_app_child!(lhs(self.left_ancestor_stack.last().unwrap()));
                let rhs = get_app_child!(rhs(self.left_ancestor_stack.last().unwrap()));
                print!("{}", &*lhs.borrow());
                self.left_ancestor_stack.push(rhs);
                self.reduce()?;
                let rhs = self.left_ancestor_stack.pop().clone();

                if check_type!(&rhs; nil) {
                    break;
                }
            }else{
                break;
            }
        }*/
        self.print_list();

        Ok(self
            .left_ancestor_stack
            .last()
            .unwrap()
            .clone()
            .borrow()
            .clone())
    }

    pub fn print_list(&mut self) -> Result<(), SaslError> {
        if check_type!(&*self.left_ancestor_stack.last().unwrap(); pair) {
             let mut printer = String::from("[");
            while check_type!(&*self.left_ancestor_stack.last().unwrap(); pair) {
                let lhs = get_pair_child!(lhs(self.left_ancestor_stack.last().unwrap()));
                let rhs = get_pair_child!(rhs(self.left_ancestor_stack.last().unwrap()));

                self.left_ancestor_stack.push(lhs);
                self.reduce();
                let lhs = self.left_ancestor_stack.pop().unwrap();

                if check_type!(&lhs; boolean){
                    let lhs_val = get_const_val!(lhs; boolean);
                    printer.push_str(&lhs_val.to_string());
                }else if check_type!(&lhs; number){
                    let lhs_val = get_const_val!(lhs; number);
                    printer.push_str(&lhs_val.to_string());
                }else if check_type!(&lhs; string){
                    let lhs_val = get_const_val!(lhs; string);
                    printer.push_str(&lhs_val.to_string());
                }

                println!("{}", printer.clone());
                self.left_ancestor_stack.push(ptr!(rhs.borrow().clone()));
                self.reduce();
               // let rhs = self.left_ancestor_stack.pop().unwrap();

                if check_type!(&rhs; nil){
                    printer.push(']');
                    self.left_ancestor_stack.push(ptr!(AstNode::Constant(Type::String(printer.clone()))));
                }else {
                    printer.push(',');
                }

            }

        }

            Ok(())

    }

    pub fn get_result(&mut self) -> AstNode {
        self.left_ancestor_stack
            .pop()
            .unwrap()
            .deref()
            .borrow()
            .clone()
    }

    fn throw_compile_err(&self, msg: &str) -> Result<(), SaslError> {
        Err(SaslError::CompilerError {
            msg: msg.to_string(),
        })
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
            | AstNode::Builtin(Op::InfixOp(op @ T![or])) => self.reduce_binary(&op),
            AstNode::Builtin(Op::Cond) => self.reduce_cond(),
            AstNode::Builtin(Op::PrefixOp(T![not])) => self.reduce_unary(),
            AstNode::Builtin(Op::InfixOp(T![:])) => self.reduce_cons(),
            AstNode::Builtin(Op::PrefixOp(T![head])) => self.reduce_hd(),
            AstNode::Builtin(Op::PrefixOp(T![tail])) => self.reduce_tl(),
           // AstNode::Ident(s) => self.reduce_global_defs(s),
            AstNode::S => self.reduce_S(),
            AstNode::K => self.reduce_K(),
            AstNode::I => self.reduce_I(),
            AstNode::Y => self.reduce_Y(),
            AstNode::U => self.reduce_U(),
            AstNode::S_ => self.eval_S_(),
            AstNode::B => self.eval_B(),
            AstNode::B_ => self.eval_B_star(),
            AstNode::C => self.eval_C(),
            AstNode::C_ => self.eval_C_(),
            _ => panic!(),
        }
    }
    //reduction of S'
    fn eval_S_(&mut self) -> Result<(), SaslError> {
        //c @ (f @ x) @ (g @ x)
        let c = get_app_child!(rhs(self.left_ancestor_stack.pop().unwrap()));
        let f = get_app_child!(rhs(self.left_ancestor_stack.pop().unwrap()));
        let g = get_app_child!(rhs(self.left_ancestor_stack.pop().unwrap()));
        let top = self.left_ancestor_stack.last().unwrap().clone();
        let x = get_app_child!(rhs(top));
        //build ast Apps
        let f_and_x = AstNode::App(ptr!(f.borrow().clone()), ptr!(x.borrow().clone()));
        let g_and_x = AstNode::App(ptr!(g.borrow().clone()), ptr!(x.borrow().clone()));

        let c_f_and_x = AstNode::App(ptr!(c.borrow().clone()), ptr!(f_and_x));
        //set app childs
        set_app_child_value!(lhs(top) = c_f_and_x);
        set_app_child_value!(lhs(top) = g_and_x);
        Ok(())
    }
    //redcution of B
    fn eval_B(&mut self) -> Result<(), SaslError> {
        // f @ (g @ x)
        let f = get_app_child!(rhs(self.left_ancestor_stack.pop().unwrap()));
        let g = get_app_child!(rhs(self.left_ancestor_stack.pop().unwrap()));
        let top = self.left_ancestor_stack.last().unwrap().clone();
        let x = get_app_child!(rhs(top));
        //build ast Apps
        let g_and_x = AstNode::App(ptr!(g.borrow().clone()), ptr!(x.borrow().clone()));
        //set app childs
        set_app_child_value!(lhs(top) = (f.borrow().clone()));
        set_app_child_value!(rhs(top) = g_and_x);

        Ok(())
    }
    //Reduction of B*
    fn eval_B_star(&mut self) -> Result<(), SaslError> {
        // c @ (f @ (g @ x))
        let c = get_app_child!(rhs(self.left_ancestor_stack.pop().unwrap()));
        let f = get_app_child!(rhs(self.left_ancestor_stack.pop().unwrap()));
        let g = get_app_child!(rhs(self.left_ancestor_stack.pop().unwrap()));
        let top = self.left_ancestor_stack.last().unwrap().clone();
        let x = get_app_child!(rhs(top));
        //build ast Apps
        let g_and_x = AstNode::App(ptr!(g.borrow().clone()), ptr!(x.borrow().clone()));
        let f_and_g_and_x = AstNode::App(ptr!(f.borrow().clone()), ptr!(g_and_x));
        //set app childs
        set_app_child_value!(lhs(top) = (c.borrow().clone()));
        set_app_child_value!(rhs(top) = f_and_g_and_x);
        Ok(())
    }
    //Reduction of C
    fn eval_C(&mut self) -> Result<(), SaslError> {
        // f @ x @ g
        let f = get_app_child!(rhs(self.left_ancestor_stack.pop().unwrap()));
        let g = get_app_child!(rhs(self.left_ancestor_stack.pop().unwrap()));
        let top = self.left_ancestor_stack.last().unwrap().clone();
        let x = get_app_child!(rhs(top));
        //build ast Apps
        let f_and_x = AstNode::App(ptr!(f.borrow().clone()), ptr!(x.borrow().clone()));
        //set app childs
        set_app_child_value!(lhs(top) = (g.borrow().clone()));
        set_app_child_value!(lhs(top) = f_and_x);

        Ok(())
    }
    //reduction of C'
    fn eval_C_(&mut self) -> Result<(), SaslError> {
        // c @ (f @ x) @ g )
        let c = get_app_child!(rhs(self.left_ancestor_stack.pop().unwrap()));
        let f = get_app_child!(rhs(self.left_ancestor_stack.pop().unwrap()));
        let g = get_app_child!(rhs(self.left_ancestor_stack.pop().unwrap()));
        let top = self.left_ancestor_stack.last().unwrap().clone();
        let x = get_app_child!(rhs(top));
        //build ast Apps
        let f_and_x = AstNode::App(ptr!(f.borrow().clone()), ptr!(x.borrow().clone()));
        let c_and_f_and_x = AstNode::App(ptr!(c.borrow().clone()), ptr!(f_and_x));
        //set app childs
        set_app_child_value!(rhs(top) = (g.borrow().clone()));
        set_app_child_value!(lhs(top) = c_and_f_and_x);
        Ok(())
    }
    //reduction of recursion
    fn reduce_Y(&mut self) -> Result<(), SaslError> {
        // f @ (Y @ f)
        let top = self.left_ancestor_stack.last().unwrap().clone();
        let f = get_app_child!(rhs(top)).deref().borrow().clone();

        let y_and_f = AstNode::App(ptr!(AstNode::Y), ptr!(f.clone()));
        set_app_child_value!(rhs(top) = y_and_f);

        set_app_child_value!(lhs(top) = f);
        println!("hier,{}", &*top.borrow());
        //panic!()
        Ok(())
    }
    //reduction for several variables
    fn reduce_U(&mut self) -> Result<(), SaslError> {
        // (f @ (hd @ z)) @ (tl @ z)
        let f = get_app_child!(rhs(self.left_ancestor_stack.pop().unwrap()));
        let top = self.left_ancestor_stack.last().unwrap().clone();
        let z = get_app_child!(rhs(top));
        //println!("hier,{}", &*top.borrow());
        // build (hd @ z)
        let hd_and_z = AstNode::App(
            ptr!(AstNode::Builtin(Op::PrefixOp(T![head]))),
            ptr!(z.borrow().clone()),
        );
        //build (tl @ z)
        let tl_and_z = AstNode::App(
            ptr!(AstNode::Builtin(Op::PrefixOp(T![tail]))),
            ptr!(z.borrow().clone()),
        );
        //build (f @ (tl @ z))
        let f_hd_and_z = AstNode::App(f, ptr!(hd_and_z));

        set_app_child_value!(lhs(top) = f_hd_and_z);
        set_app_child_value!(rhs(top) = tl_and_z);
        Ok(())
    }

    fn reduce_S(&mut self) -> Result<(), SaslError> {
        // switch to turn of/ on the optimization
        let switch = false;
        if switch {
            //optimization
            self.optimizer();
            Ok(())
        } else {
            // (f @ x) @ (g @ x)
            let f = get_app_child!(rhs(self.left_ancestor_stack.pop().unwrap()));
            let g = get_app_child!(rhs(self.left_ancestor_stack.pop().unwrap()));
            let top = self.left_ancestor_stack.last().unwrap().clone();
            let x = get_app_child!(rhs(top));

            //build
            let f_and_x = AstNode::App(ptr!(f.borrow().clone()), ptr!(x.borrow().clone()));
            let g_and_x = AstNode::App(ptr!(g.borrow().clone()), ptr!(x.borrow().clone()));
            set_app_child_value!(lhs(top) = f_and_x);
            set_app_child_value!(rhs(top) = g_and_x);
            //println!("hier, {}", &*top.borrow());
            Ok(())
        }
    }

    fn optimizer(&mut self) -> Result<(), SaslError> {
        let f = get_app_child!(rhs(self.left_ancestor_stack.pop().unwrap()));
        let top = self.left_ancestor_stack.last().unwrap().clone();
        let g = get_app_child!(rhs(top));

        // getting the left and right child of f and g
        let f_rhs = get_app_child!(rhs(f));
        let g_rhs = get_app_child!(rhs(g));
        let f_lhs = get_app_child!(lhs(f));
        //define astnode K and B for pattern matching
        let k = ptr!(AstNode::K);
        let b = ptr!(AstNode::B);
        //match the optimatzation rules
        match f.borrow().clone() {
            // f = K @ f
            AstNode::App(k, _) => {
                match g.borrow().clone() {
                    AstNode::App(k, _) => {
                        //S @ (K @ f) @ (K @ g) =>  K @ (f @ g)

                        let f_rhs_and_g_rhs = AstNode::App(
                            ptr!(f_rhs.borrow().clone()),
                            ptr!(g_rhs.borrow().clone()),
                        );
                        set_app_child_value!(lhs(top) = AstNode::K);
                        set_app_child_value!(rhs(top) = f_rhs_and_g_rhs);
                    }
                    AstNode::I => {
                        //S @ (K @ f) @ I => f
                        let top = f_rhs.borrow().clone();
                        self.left_ancestor_stack.push(ptr!(top));
                    }
                    _ => {
                        //S @ (K @ f) @ g => B @ f @ g
                        let b_and_f_rhs =
                            AstNode::App(ptr!(AstNode::B), ptr!(f_rhs.borrow().clone()));

                        set_app_child_value!(lhs(top) = b_and_f_rhs);
                        set_app_child_value!(rhs(top) = g.borrow().clone());
                    }
                }
            }

            _ => {
                match f_lhs.borrow().clone() {
                    // f = B @ f @ g
                    AstNode::App(b, _) => {
                        let f_botton_rhs = get_app_child!(rhs(f_lhs));

                        match g.borrow().clone() {
                            AstNode::App(k, _) => {
                                // S @ ( B @ f @ g) @ (K @ h) => C' @ f @ g @ h
                                let c_and_f = AstNode::App(
                                    ptr!(AstNode::C_),
                                    ptr!(f_botton_rhs.borrow().clone()),
                                );
                                let c_and_f_and_f =
                                    AstNode::App(ptr!(c_and_f), ptr!(f_rhs.borrow().clone()));

                                set_app_child_value!(lhs(top) = c_and_f_and_f);
                                set_app_child_value!(rhs(top) = g_rhs.borrow().clone());
                            }
                            _ => {
                                // S @ ( B @ f @ g) @ h => S' @ f @ g @ h
                                let s_and_f = AstNode::App(
                                    ptr!(AstNode::S_),
                                    ptr!(f_botton_rhs.borrow().clone()),
                                );
                                let s_and_f_and_f =
                                    AstNode::App(ptr!(s_and_f), ptr!(f_rhs.borrow().clone()));

                                set_app_child_value!(lhs(top) = s_and_f_and_f);
                                set_app_child_value!(rhs(top) = g.borrow().clone());
                            }
                        }
                    }
                    //
                    _ => {
                        // f = f
                        match g.borrow().clone() {
                            AstNode::App(k, rhs) => {
                                //(S @ f) @ ( K @ g) => C @ f @ g
                                let s_and_f =
                                    AstNode::App(ptr!(AstNode::C), ptr!(f_rhs.borrow().clone()));

                                set_app_child_value!(lhs(top) = s_and_f);
                                set_app_child_value!(rhs(top) = rhs.borrow().clone());
                            }
                            _ => {
                                // (f @ x) @ (g @ x)
                                let top = self.left_ancestor_stack.last().unwrap().clone();
                                let x = get_app_child!(rhs(top));
                                let f_and_x = AstNode::App(
                                    ptr!(f.borrow().clone()),
                                    ptr!(x.borrow().clone()),
                                );
                                let g_and_x = AstNode::App(
                                    ptr!(g.borrow().clone()),
                                    ptr!(x.borrow().clone()),
                                );
                                set_app_child_value!(lhs(top) = f_and_x);
                                set_app_child_value!(rhs(top) = g_and_x);
                                //println!("hier, {}", &*top.borrow());
                            }
                        }
                    }
                }
            }
        };
        Ok(())
    }

    fn reduce_K(&mut self) -> Result<(), SaslError> {
        //I @ x
        let x = get_app_child!(rhs(self.left_ancestor_stack.pop().unwrap()));
        //self.left_ancestor_stack.pop();
        let mut top = self.left_ancestor_stack.last().unwrap().clone();
        //Build

        set_app_child_value!(rhs(&mut top) = (x.borrow().clone()));
        set_app_child_value!(lhs(top) = AstNode::I);
        Ok(())
    }

    pub fn reduce_I(&mut self) -> Result<(), SaslError> {
        //x
        let x = get_app_child!(rhs(self.left_ancestor_stack.pop().unwrap()));
        self.left_ancestor_stack.push(x);
        Ok(())
    }
    //reduce binary operations
    fn reduce_binary(&mut self, op: &Type) -> Result<(), SaslError> {
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
                T![+] => set_app_child_value!(
                    rhs(top) = AstNode::Constant(Type::Number(num_lhs + num_rhs))
                ),
                T![-] => set_app_child_value!(
                    rhs(top) = AstNode::Constant(Type::Number(num_lhs - num_rhs))
                ),
                T![*] => set_app_child_value!(
                    rhs(top) = AstNode::Constant(Type::Number(num_lhs * num_rhs))
                ),
                T![/] => set_app_child_value!(
                    rhs(top) = AstNode::Constant(Type::Number(num_lhs / num_rhs))
                ),
                T![=] => set_app_child_value!(
                    rhs(top) = AstNode::Constant(Type::Boolean(num_lhs == num_rhs))
                ),
                T![~=] => set_app_child_value!(
                    rhs(top) = AstNode::Constant(Type::Boolean(num_lhs != num_rhs))
                ),
                T![<] => set_app_child_value!(
                    rhs(top) = AstNode::Constant(Type::Boolean(num_lhs < num_rhs))
                ),
                T![<=] => set_app_child_value!(
                    rhs(top) = AstNode::Constant(Type::Boolean(num_lhs <= num_rhs))
                ),
                T![>] => set_app_child_value!(
                    rhs(top) = AstNode::Constant(Type::Boolean(num_lhs > num_rhs))
                ),
                T![>=] => set_app_child_value!(
                    rhs(top) = AstNode::Constant(Type::Boolean(num_lhs >= num_rhs))
                ),

                _ => panic!(),
            }
            Ok(())
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
                _ => self.throw_compile_err("This Operation ist not possible on Boolean Value"),
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
                _ => self.throw_compile_err("This Operation ist not possible on Nil"),
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
                _ => self.throw_compile_err("This Operation ist not possible on Nil"),
            }
        } else {
            self.throw_compile_err("This Operation ist not possible on the variables")
        }
    }
    //eval unary oparions
    fn reduce_unary(&mut self) -> Result<(), SaslError> {
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
            self.throw_compile_err("Semantic Error: Expected boolean expression after not")
        }
    }
    //reduce if conditions
    fn reduce_cond(&mut self) -> Result<(), SaslError> {
        //gets the boolean predicate
        let predicate = get_app_child!(rhs(self.left_ancestor_stack.pop().unwrap()));
        let top = self.left_ancestor_stack.last().unwrap().clone();
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

    fn reduce_hd(&mut self) -> Result<(), SaslError> {
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

    fn reduce_tl(&mut self) -> Result<(), SaslError> {
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
    fn reduce_cons(&mut self) -> Result<(), SaslError> {
        let x = get_app_child!(rhs(self.left_ancestor_stack.pop().unwrap()));
        let top = self.left_ancestor_stack.last().unwrap().clone();
        let y = get_app_child!(rhs(top));
        // I @ Pair(x,y)
        //println!("dort, {}", &*top.borrow());
        //println!("dort, {}", &*x.borrow());
        //println!("dort, {}", &*y.borrow());

        set_app_child_value!(lhs(top) = AstNode::I);
        //make a list to a pair
        let pair = AstNode::Pair(
            ptr!(x.borrow().deref().clone()),
            ptr!(y.borrow().deref().clone()),
        );
        set_app_child_value!(rhs(top) = pair);
        Ok(())
    }

    fn reduce_global_defs(&mut self, s: String ,def_pos : DefPosition) -> Result<(), SaslError> {
        let top = self.left_ancestor_stack.last().unwrap().clone();
        //look into Hashmap
        let x = self
            .ast
            .global_defs
            .get(&s)
            .unwrap_or_else(|| panic!())
            .1
            .deref()
            .borrow()
            .clone();
        match def_pos {
            DefPosition::Lhs => set_app_child_value!(lhs(top) = x),
            DefPosition::Rhs => set_app_child_value!(rhs(top) = x)
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use std::ops::Deref;

    use super::*;
    use crate::backend::compiler::compile;
    use crate::frontend::{lexer::*, parser::*};

    fn compile_to_ast(code: &str) -> Ast {
        let mut ast = Parser::new(Lexer::new(code).tokenize().unwrap())
            .parse()
            .unwrap();
        compile(&mut ast);
        ast
    }
    #[test]
    fn test_check_reduction() {
        let mut ast = compile_to_ast(
            "def incr x = 1 + x \
     def err x = if x > 2 then true else err x+1 \
     def test = if 12 > 12-0 then true else false \
     def plus x y = x+y \
     . incr 3\
     . err 0\
     . plus 4 3",
        );
        let ast = ReductionMachine::new(ast).reduce().unwrap();
        assert_eq!(ast.to_string(), "Number:4");
        assert_eq!(ast.to_string(), "true");
        assert_eq!(ast.to_string(), "true");
        assert_eq!(ast.to_sting(), "Number:7")
    }
}
