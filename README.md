# Table of content
1. [About](#About)
2. [Installation](#Installation)
3. [Usage](#Usage)
4. [Examples](#Examples)
5. [Benchmarks](#Benchmarks)

# About
SASL is a purely functional programming language developed by David Turner in 1972. This projects contains a compiler written in [Rust](https://www.rust-lang.org/) for said language with support for most of what the SASL language is capable of, like:
- Lazy evaluation
- Currying
- Purely functional programming paradigm

The compiler is divided into two sections: the frontend and the backend. The frontend contains the lexer, parser and the implementation of the abstract syntax tree which is used throughout the project. The backend contains the compiler and a virtual machine for evaluation. \
Furthermore a simple parser for the [Graphviz DOT DSL](https://graphviz.org/) is included which can be used for debugging and visualizing the abstract syntax tree.

# Installation
1. If you already have Rust installed you can skip this part. Otherwise you may want to look at [how to install Rust](https://www.rust-lang.org/learn/get-started).
2. Simply build the project with cargo. All dependencies are downloaded and installed automatically (nice isn't it?):
    ```
    $ git clone https://github.com/dvdvgt/SASL-rs
    $ cd SASL-rs
    $ cargo build --release
    ```
    The compiled executable is now available with e.g. `./target/release/sasl --help`

## Optional Dependencies
As previously mentioned this project contains a small parser for the DOT language. If you want to use the `--visualize` option you have to have `DOT` installed. It is available with most package managers or can installed directly from [here](https://graphviz.org/download/).

# Usage
```
$ sasl --help
    SASL-rs 0.0.1
    David Voigt <david.voigt@student.uni-tuebingen.de>
    Lars Vogtmann <lars.vogtmann@studen.uni-tuebingen.de
    Compiler for the SASL functional programming language written in Rust.

    USAGE:
        sasl [FLAGS] [OPTIONS]

    FLAGS:
        -h, --help       Prints help information
        -v               Output tokens as well as the AST. Useful for debugging.
        -V, --version    Prints version information

    OPTIONS:
        -c <FILE>                 Path to the SASL file that will be compiled.
            --visualize <PATH>    Visualizes the abstract syntax tree with the help of GraphViz/DOT and
                                outputs a PDF with the AST as well as the corresponding .dot file with
                                the given filename.
```

The compiler features a simple REPL environment which can be started by just running `sasl` without the `-c` Option.

# Examples
1. Naive fibonacci algorithm
    ```
    fib n = 
        if (n = 0) or (n = 1) then 1
        else (fib (n-1)) + (fib (n-2))
    .
    fib 20 // = 10946
    ```
2. Currying
    ```
    def plus x y = x + y
    def incr = plus 1
    .
    incr 5 // = 6
    ```
3. Lazy evaluation in action
    ```
    def take n xs = 
        if n = 0 then nil 
        else x : take (n - 1) ys
            where 
                ys = tl xs;
                x = hd xs
    def sum xs = 
        if xs = nil then 0 
        else (hd xs) + (sum (tl xs))
    // Defines infinite list [1, 2, ...]
    def naturalNumbers n = n : (naturalNumbers (n+1))
    .
    sum (take 5 (naturalNumbers 1)) // = 15
    ```

# Benchmarks
The following benchmarks were conducted using [Hyperfine](https://github.com/sharkdp/hyperfine):
```
hyperfine --warumup 3 './sasl -c [FILE.sasl]'
```
1. Naive Fibonacci algorithm with `fib 20`:
    ```
    Time (mean ± σ):     124.4 ms ±  13.5 ms    [User: 123.7 ms, System: 1.0 ms]
    Range (min … max):   114.3 ms … 147.9 ms    24 runs
    ```