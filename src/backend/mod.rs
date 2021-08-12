//! This module contains all modules needed for the backend of the compiler.
//! 
//! The backend features two (three counting optimizations) stages:
//! 1. Introducing combinators into the AST and removing all ocurences of parameters and
//! local where definitions. This stage is handled by the `Abstractor`.
//! 2. Evaluating the program in a virtual machine. This stage is handled by the `ReductionMachine`.
//! The virtual machine simplifies the AST step by step adhering the rules given in the language
//! specifications for the combinators. The VM also applys optimization rules which can lead to
//! performance increase with up to ~40% quicker execution time. The optimizations can be activated
//! by setting the `-o` flag. (There's really no reason not to do that.)

pub mod abstractor;
pub mod reduction;
pub mod utils;
