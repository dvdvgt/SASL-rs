use std::{env, fs, io::{self, Read}};
use io::Write;

use frontend::lexer::Lexer;

mod frontend;
mod error;

fn main() {
    let args: Vec<String> = env::args().collect();
    match args.len() {
        1 => run_prompt(),
        2 => run_file(&args[1]),
        _ => panic!("Unsupported number of arguments.")
    }
}

fn run_prompt() {
    let mut inpt = String::new();
    loop {
        print!("> ");
        io::stdout().flush().unwrap();
        let num_bytes = io::stdin().read_line(&mut inpt).unwrap();
        if num_bytes == 0 {
            break;
        }
        run(&inpt);
        inpt.clear();
    }
}

fn run_file(path: &str) {
    let mut file = fs::File::open(path).unwrap();
    let mut src = String::new();
    file.read_to_string(&mut src).unwrap();
    //println!("{}", &src);
    run(&src);
}

fn run(src: &str) {
    let mut lx = Lexer::new(src);
    match lx.tokenize() {
        Err(e) => eprintln!("{}", e),
        Ok(tokens) => {
            for token in tokens {
                println!("\t{}", token);
            }
        }
    }
}
