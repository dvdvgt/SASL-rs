//! The frontend module contains everything that is concerned with tokenizing and parsing the input string.
//! 
//! # Lexer
//! Firstly the lexer is responsible for converting the input string into a vector of tokens which 
//! are defined in the token module.
//! ### Example
//! ```rust
//! use sasl::frontend::lexer::Lexer;
//! let mut tokens_or_err = Lexer::new("1 + 2").tokenize();
//! ```
//! `tokenize` either returns an error or a vector containing all tokens.
//! 
//! # Parser
//! The parser module is responsible for consuming the token stream and turn it into a intermediate
//! representation which is an AST (abstract syntax tree).
//! ### Example
//! ```rust
//! use sasl::frontend::{lexer::Lexer, parser::Parser};
//! let mut tokens_or_err = Lexer::new("1 + 2").tokenize();
//! let mut parser = Parser::new(tokens_or_err.unwrap()).parse();
//! ```
//! Again, the parser returns either an error informing the user of a parse error or the parse result
//! which is an instance of the `frontend::ast::Ast` and contains the body expressions as well as the
//! global definitions.
//! 
//! # Visualization
//! There's also a small Graphviz DOT parser which can be used to visualize a given AST in order to 
//! better reason about and debug a faulty AST during development.

pub mod ast;
pub mod lexer;
pub mod parser;
pub mod token;
pub mod position;
pub mod visualize;
