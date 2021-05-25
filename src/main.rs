use io::Write;
use std::{
    env, fs,
    io::{self, Read},
};

use clap::{App, Arg};

use sasl::frontend::{lexer::Lexer, parser::Parser, visualize::Visualizer};

fn main() {
    let matches = App::new("SASL-rs")
        .version("0.0.1")
        .author("David Voigt <david.voigt@student.uni-tuebingen.de>\nLars Vogtmann <lars.vogtmann@studen.uni-tuebingen.de")
        .about("SASL compiler written in Rust.")
        .arg(Arg::new("visualize")
            .short('v')
            .long("visualize")
            .about("Visualizes the abstract syntax tree with the help of GraphViz/DOT and outputs a PDF with the AST.")
            .takes_value(false))
        .arg(Arg::new("compile")
            .value_name("FILE")
            .short('c')
            .about("Path to the SASL file that will be compiled.")
            .takes_value(true)).get_matches();

    match matches.value_of("compile") {
        Some(x) => run_file(x),
        None => run_prompt()
    }
}

/// Starts a REPL like prompt used for entering single expressions. Useful for interactive debugging.
fn run_prompt() {
    let mut inpt = String::new();
    loop {
        print!("> ");
        io::stdout().flush().unwrap();
        let num_bytes = io::stdin().read_line(&mut inpt).unwrap();
        let line = inpt.trim_end();
        if num_bytes == 0 {
            break;
        }
        run(line);
        inpt.clear();
    }
}

/// Reads and runs a file.
fn run_file(path: &str) {
    let mut file = fs::File::open(path).unwrap();
    let mut src = String::new();
    file.read_to_string(&mut src).unwrap();
    //println!("{}", &src);
    run(&src);
}

/// Runs a string input.
pub fn run(src: &str) {
    let mut lx = Lexer::new(src);
    let tokens = lx.tokenize();
    println!("Tokens:");
    match tokens {
        Err(ref e) => {
            eprintln!("{}", e);
            return
        }
        Ok(ref tokens) => {
            tokens.iter()
                .for_each(|token| println!("\t{}", token))
        }
    }
    println!("AST:");
    let mut parser = Parser::new(tokens.unwrap());
    let expr = parser.parse();
    match expr {
        Err(ref e) => eprintln!("{}", e),
        Ok(ref ast) => {
            println!("\t{}", ast);
            let mut viz = Visualizer::new("g", false);
            viz.visualize_ast(ast);
            viz.write_to_pdf("graph.pdf");
            viz.write_to_dot("graph.dot");
        }
    }
}
