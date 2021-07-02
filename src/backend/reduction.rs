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

macro_rules! get_pair_child {
	(rhs($node:expr)) => {
	  match &*$node.borrow() {
	   AstNode::Pair(_,rhs) => Rc::clone(rhs),
	   _ => panic!()
	  }
	};
	(lhs($node:expr)) => {
	  match &*$node.borrow() {
	   AstNode::Pair(lhs,_) => Rc::clone(lhs),
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
	    println!("stack,{}", &self.left_ancestor_stack.last().unwrap().borrow().clone());
            let top = self.left_ancestor_stack.last().unwrap().borrow().clone();
            match top {
                AstNode::App(lhs, _) => self.left_ancestor_stack.push(Rc::clone(&lhs)),
                AstNode::S
                | AstNode::K
                | AstNode::I
		| AstNode::Y
		| AstNode::U
	        | AstNode::Ident(_)
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
            | AstNode::Builtin(Op::InfixOp(op @ T![or])) => self.reduce_binary(&op),
            AstNode::Builtin(Op::Cond) => self.reduce_cond(),
            AstNode::Builtin(Op::PrefixOp(T![not])) => self.reduce_unary(),
            AstNode::Builtin(Op::InfixOp(T![:])) => self.reduce_cons(),
            AstNode::Builtin(Op::PrefixOp(T![head])) => self.reduce_hd(),
            AstNode::Builtin(Op::PrefixOp(T![tail])) => self.reduce_tl(),
	    AstNode::Ident(s) => self.reduce_global_defs(s),
            AstNode::S => self.reduce_S(),
	    AstNode::K => self.reduce_K(),
	    AstNode::I => self.reduce_I(),
	    AstNode::Y => self.reduce_Y(),
	    AstNode::U => self.reduce_U(),
	    _ => todo!()
	  }
	     
	}
	
	fn reduce_Y(&mut self) -> Result<(),SaslError> {
	// f @ (Y @ f)
	let top = self.left_ancestor_stack.last().unwrap().clone();
	let f = get_app_child!(rhs(top)).deref().borrow().clone();

	
	let y_and_f = AstNode::App(ptr!(AstNode::Y), ptr!(f.clone()));
	set_app_child_value!(rhs(top) = y_and_f);
	//noch Probleme bei den Rechten erwartet Refcell<_> ist aber Rc<Refcell<_>>
	set_app_child_value!(lhs(top) = f);
	
	Ok(())
	}
	
	fn reduce_U(&mut self) -> Result<(),SaslError> {
	// (f @ (hd @ z)) @ (tl @ z)
	let f = get_app_child!(rhs(self.left_ancestor_stack.pop().unwrap()));
	let top = self.left_ancestor_stack.last().unwrap().clone();
	let z = get_app_child!(rhs(top));
	println!("hier,{}", &*top.borrow());

	let hd_and_z =  AstNode::App(ptr!(AstNode::Builtin(Op::PrefixOp(T![head]))), ptr!(z.borrow().clone()));
	let tl_and_z =  AstNode::App(ptr!(AstNode::Builtin(Op::PrefixOp(T![tail]))), ptr!(z.borrow().clone()));
	let f_hd_and_z = AstNode::App(f,ptr!(hd_and_z));
	set_app_child_value!(lhs(top) = f_hd_and_z);
	set_app_child_value!(rhs(top) = tl_and_z);
	Ok(())
	}


	fn reduce_S(&mut self) -> Result<(), SaslError> {
	// (f @ x) @ (g @ x)
	let f = get_app_child!(rhs(self.left_ancestor_stack.pop().unwrap()));
	let g = get_app_child!(rhs(self.left_ancestor_stack.pop().unwrap()));
	let top = self.left_ancestor_stack.last().unwrap().clone();
	let x = get_app_child!(rhs(top));
	println!("hier,{}", &*top.borrow());

	//build
	let f_and_x = AstNode::App(ptr!(f.borrow().clone()), ptr!(x.borrow().clone()));
	let g_and_x = AstNode::App(ptr!(g.borrow().clone()), ptr!(x.borrow().clone())); 
	set_app_child_value!(lhs(top) = f_and_x);
	set_app_child_value!(rhs(top) = g_and_x);
	println!("hier, {}", &*top.borrow());
	Ok(())
	}
	
	 fn reduce_K(&mut self) -> Result<(),SaslError> {
	//I @ x
	let x = get_app_child!(rhs(self.left_ancestor_stack.pop().unwrap()));
	//self.left_ancestor_stack.pop();
	let mut top = self.left_ancestor_stack.last().unwrap().clone();
	//Build
	
	set_app_child_value!(rhs(&mut top) = (x.borrow().clone()));
	set_app_child_value!(lhs(top) = AstNode::I);
	Ok(())
	}

	pub fn reduce_I(&mut self) -> Result<(),SaslError> {
	//x
	let x = get_app_child!(rhs(self.left_ancestor_stack.pop().unwrap()));
	self.left_ancestor_stack.push(x);
	Ok(())
	
	}

    fn reduce_binary(&mut self, op: &Type) -> Result<(), SaslError> {
 	//println!("stack,{}", &self.left_ancestor_stack.last().unwrap().borrow().clone());
        let lhs = get_app_child!(rhs(self.left_ancestor_stack.pop().unwrap()));  
	//println!("stack,{}", &self.left_ancestor_stack.last().unwrap().borrow().clone());
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

    fn reduce_unary(&mut self) -> Result<(), SaslError> {
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


   fn reduce_cond(&mut self) -> Result<(), SaslError> {
        let boo = get_app_child!(rhs(self.left_ancestor_stack.pop().unwrap()));
        let top = self.left_ancestor_stack.last().unwrap().clone();
       

        self.left_ancestor_stack.push(boo);
        self.reduce()?;
        let boo = self.left_ancestor_stack.pop().unwrap();

       
	
	if get_const_val!(boo; boolean) {
	//condition is true
	set_app_child_value!(lhs(top) = AstNode::I);
	} else {
	//condition is false
	self.left_ancestor_stack.pop().unwrap();
	let top = self.left_ancestor_stack.last().unwrap().clone();
	let y = get_app_child!(rhs(top));
	//self.left_ancestor_stack.push(y);
        //self.reduce()?;
        //let y = self.left_ancestor_stack.pop().unwrap();

        set_app_child_value!(lhs(top) = AstNode::I);
	
	}
	Ok(())
   }
	
   fn reduce_hd(&mut self) -> Result<(),SaslError> {
	let top = self.left_ancestor_stack.last().unwrap().clone();
	
	// get pair child and 
	let x =  get_pair_child!(lhs(top)) ;
	set_app_child_value!(rhs(top) = x.borrow().clone());
	set_app_child_value!(lhs(top) = AstNode::I);
	
	Ok(())
   }
	
   fn reduce_tl(&mut self) -> Result<(),SaslError> {
	
	let top = self.left_ancestor_stack.last().unwrap().clone();
	
	
	let x =  get_pair_child!(rhs(top)) ;
	set_app_child_value!(rhs(top) = x.borrow().clone());
	set_app_child_value!(lhs(top) = AstNode::I);
	
	Ok(())
   }

  fn reduce_cons(&mut self) -> Result<(),SaslError> {
	let x = get_app_child!(rhs(self.left_ancestor_stack.pop().unwrap()));
	let top = self.left_ancestor_stack.last().unwrap().clone();
	let y = get_app_child!(rhs(top));
	// I @ Pair(x,y)
	println!("dort, {}", &*top.borrow());
	set_app_child_value!(lhs(top) = AstNode::I);
	set_app_child_value!(rhs(top) = AstNode::Pair(x,y));	
	Ok(())

   }
 
  fn reduce_global_defs(&mut self, s : String) -> Result<(), SaslError> {
	let top = self.left_ancestor_stack.last().unwrap().clone();
	//look into Hashmap
        let x = self.ast.global_defs.get(&s).unwrap_or_else(||panic!()).1.deref().borrow().clone();
	set_app_child_value!(lhs(top) = x);  
        Ok(())
	
  }

}

