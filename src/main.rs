use io::Write;
use std::{
    env, fs,
    io::{self, Read},
};

use sasl::frontend::lexer::Lexer;
use sasl::frontend::parser::Parser;

fn main() {
    let args: Vec<String> = env::args().collect();
    match args.len() {
        1 => run_prompt(),
        2 => run_file(&args[1]),
        _ => panic!("Unsupported number of arguments."),
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
    let expr = parser.parse_expr();
    match expr {
        Err(ref e) => eprintln!("{}", e),
        Ok(ref ast) => println!("\t{:?}", ast)
    }
}
