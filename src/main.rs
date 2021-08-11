use io::Write;
use std::{
    collections::HashMap,
    error::Error,
    fs,
    io::{self, Read},
    time::Instant,
};

use clap::{App, Arg, ArgMatches};
use sasl::frontend::{lexer::Lexer, parser::Parser, visualize::Visualizer};
use sasl::{
    backend::{abstractor::compile, reduction::ReductionMachine},
    frontend::ast::{AstNodePtr, Identifier, Params},
};

fn main() {
    let matches = App::new("SASL-rs")
        .version("1.0.0")
        .author("David Voigt <david.voigt@student.uni-tuebingen.de>\nLars Vogtmann <lars.vogtmann@studen.uni-tuebingen.de")
        .about("A compiler for the SASL functional programming language written in Rust.")
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
        Some(_) => Runner::run_with_mode(RunMode::File, &matches)
            .unwrap_or_else(|err| eprintln!("{}: {}", err, matches.value_of("compile").unwrap())),
        None => Runner::run_with_mode(RunMode::Prompt, &matches)
            .unwrap_or_else(|err| eprintln!("{}", err)),
    };
}

/// Indicate whether the compiler shall be run in REPL/prompt mode or
/// to compile and evaluate a SASL source file.
enum RunMode {
    Prompt,
    File,
}

/// Simple struct responsible for coordinating the execution of either the
/// REPL or a SASL file.
struct Runner<'a> {
    mode: RunMode,
    args: &'a ArgMatches,
    /// Save the defs from the previous REPL queries in order to still
    /// have access to them later on.
    prompt_defs: HashMap<Identifier, (Params, AstNodePtr)>,
}

impl<'a> Runner<'a> {
    pub fn run_with_mode(mode: RunMode, args: &'a ArgMatches) -> Result<(), Box<dyn Error>> {
        let mut runner = Self {
            mode,
            args,
            prompt_defs: HashMap::new(),
        };
        match runner.mode {
            RunMode::File => {
                let src = runner.load_source_file()?;
                runner.run(&src);
            }
            RunMode::Prompt => runner.run_prompt()?,
        }
        Ok(())
    }

    /// Helper function for getting the content of a file.
    fn load_source_file(&self) -> Result<String, io::Error> {
        let path = self.args.value_of("compile").unwrap();
        let mut file = fs::File::open(path)?;
        let mut src = String::new();
        file.read_to_string(&mut src)?;
        Ok(src)
    }

    /// Starts a REPL like prompt used for entering single expressions. Useful for interactive debugging.
    fn run_prompt(&mut self) -> Result<(), io::Error> {
        let mut inpt = String::new();
        println!("SASL-rs 1.0.0\
        \nA compiler for the SASL functional programming language written in Rust.\
        \nPress ctrl+d or ctrl+c to exit.");
        loop {
            print!("\u{1b}[0;38;5;171mλ > \u{1b}[0m");
            io::stdout().flush()?;
            let num_bytes = io::stdin().read_line(&mut inpt)?;
            let line = inpt.trim_end();
            if num_bytes == 0 {
                // Terminate line
                println!();
                return Ok(());
            }
            self.run(line);
            inpt.clear();
        }
    }

    /// Evaluates/Executes a SASL program represented as string.
    pub fn run(&mut self, src: &str) {
        // Time the execution duration
        let start = Instant::now();
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
                if self.args.is_present("verbose") {
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
                if self.args.is_present("verbose") {
                    println!("AST:");
                    println!("\t{:?}", ast);
                }
                // Only create graph if flag is set.
                if self.args.is_present("visualize") {
                    let mut viz = Visualizer::new("g", false);
                    viz.visualize_ast(ast);
                    let filename = self.args.value_of("visualize").unwrap();
                    viz.write_to_pdf(&format!("{}.pdf", filename));
                    viz.write_to_dot(&format!("{}.dot", filename));
                }
            }
        }
        // Run abstractor
        let mut ast = expr.unwrap();
        compile(&mut ast).unwrap();
        ast.insert_defs(&self.prompt_defs);
        // Eval
        let mut reductor = ReductionMachine::new(ast.clone(), self.args.is_present("optimize"));
        match reductor.reduce() {
            Ok(_) => {
                println!("{}", reductor.print_result().unwrap());
                println!("\ntook \u{1b}[32;40m{:.2?}\u{1b}[0m", start.elapsed());
                self.prompt_defs = ast.global_defs.clone();
            }
            Err(e) => eprintln!("{}", e),
        }
    }
}
