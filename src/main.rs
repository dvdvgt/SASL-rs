use io::Write;
use std::{
    fs,
    io::{self, Read},
};

use clap::{App, Arg, ArgMatches};
use sasl::{backend::{abstractor, reduction::ReductionMachine}};
use sasl::frontend::{lexer::Lexer, parser::Parser, visualize::Visualizer};

fn main() {
    let matches = App::new("SASL-rs")
        .version("0.0.1")
        .author("David Voigt <david.voigt@student.uni-tuebingen.de>\nLars Vogtmann <lars.vogtmann@studen.uni-tuebingen.de")
        .about("Compiler for the SASL functional programming language written in Rust.")
        .arg(Arg::new("visualize")
            .long("visualize")
            .about("Visualizes the abstract syntax tree with the help of GraphViz/DOT and outputs \
            a PDF with the AST as well as the corresponding .dot file with the given filename.")
            .takes_value(true)
            .value_name("PATH"))
        .arg(Arg::new("compile")
            .value_name("FILE")
            .short('c')
            .about("Path to the SASL file that will be compiled.")
            .takes_value(true))
        .arg(Arg::new("verbose")
            .short('v')
            .about("Output tokens as well as the AST. Useful for debugging.")
            .takes_value(false))
        .arg(Arg::new("optimize")
            .short('o')
            .takes_value(false)
            .about("Activate optimizations."))
        .get_matches();

    match matches.value_of("compile") {
        Some(x) => run_file(x, &matches),
        None => run_prompt(&matches),
    }
}

/// Starts a REPL like prompt used for entering single expressions. Useful for interactive debugging.
fn run_prompt(args: &ArgMatches) {
    let mut inpt = String::new();
    loop {
        print!("> ");
        io::stdout().flush().unwrap();
        let num_bytes = io::stdin().read_line(&mut inpt).unwrap();
        let line = inpt.trim_end();
        if num_bytes == 0 {
            break;
        }
        run(line, args);
        inpt.clear();
    }
}

/// Reads and runs a file.
fn run_file(path: &str, args: &ArgMatches) {
    let mut file = fs::File::open(path).unwrap();
    let mut src = String::new();
    file.read_to_string(&mut src).unwrap();
    run(&src, args);
}

/// Runs a string input.
pub fn run(src: &str, args: &ArgMatches) {
    // Tokenize the input.
    let mut lx = Lexer::new(src);
    let tokens = lx.tokenize();
    // Only output tokens if verbose flag is set.
    match tokens {
        Err(ref e) => {
            eprintln!("{}", e);
            return;
        }
        Ok(ref tokens) => {
            if args.is_present("verbose") {
                println!("Tokens:");
                tokens.iter().for_each(|token| println!("\t{}", token))
            }
        }
    }
    // Parse the tokens.
    let mut parser = Parser::new(tokens.unwrap());
    let expr = parser.parse();
    match expr {
        Err(ref e) => {
            eprintln!("{}", e);
            return;
        }
        Ok(ref ast) => {
            // Only output AST if verbose flag is set.
            if args.is_present("verbose") {
                println!("AST:");
                println!("\t{:?}", ast);
            }
            // Only create graph if flag is set.
            if args.is_present("visualize") {
                let mut viz = Visualizer::new("g", false);
                viz.visualize_ast(ast);
                let filename = args.value_of("visualize").unwrap();
                viz.write_to_pdf(&format!("{}.pdf", filename));
                viz.write_to_dot(&format!("{}.dot", filename));
            }
        }
    }
    // Run abstractor
    let mut expr = expr.unwrap();
    abstractor::compile(&mut expr).unwrap();
    // Eval
    let mut reductor = ReductionMachine::new(expr, args.is_present("optimize"));
    match reductor.reduce() {
        Ok(_) => println!("{}", reductor.print_result().unwrap()),
        Err(e) => eprintln!("{}", e)
    }
}
