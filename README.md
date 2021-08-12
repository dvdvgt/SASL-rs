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
Furthermore a simple parser for the [Graphviz DOT DSL](https://graphviz.org/) is included which can be used for debugging and visualizing the abstract syntax tree. \
The compiler was implemented following the languages specifications listed [here](https://db.inf.uni-tuebingen.de/staticfiles/teaching/ss16/sasl2016.pdf).

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
    SASL-rs 1.0.0
    David Voigt <david.voigt@student.uni-tuebingen.de>
    Lars Vogtmann <lars.vogtmann@studen.uni-tuebingen.de
    A compiler for the SASL functional programming language written in Rust.

    USAGE:
        sasl [FLAGS] [OPTIONS]

    FLAGS:
        -h, --help       Prints help information
        -o               Activate optimizations.
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
    fib 20
    ```
2. Currying
    ```
    def plus x y = x + y
    def incr = plus 1
    .
    incr 5
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
    sum (take 5 (naturalNumbers 1))
    ```
4. A more elaborate example for computing a list of prime numbers using *sieve of eratosthenes*:
    - Note the use of functions as first-class-citiziens
    - The use of lazy evaluation
    ```
    def sieve = go (tl naturalNumbers)
    where
        go xs = (hd xs) : (go (filter (notDivableBy (hd xs)) xs))
    def naturalNumbers = next 0
        where 
            next x = (x + 1) : (next (x + 1))
    def filter p l = 
        if l = nil 
        then nil
        else 
            if p x 
            then x:(filter p xs)
            else filter p xs
                where 
                    x  = hd l;
                    xs = tl l
    def take n xs = 
        if n = 0 then nil 
        else x : take (n - 1) ys
        where 
            ys = tl xs;
            x = hd xs
    def mod x y = if x < y then x else mod (x-y) y
    def flip f x y = f y x
    def notDivableBy x y = (flip mod x y) ~= 0
    .
    take 50 sieve
    ```
5. It's possible to import other SASL files by just specifiying the relative path to the file
to import.

    ```
    use prelude

    take 2 [1, 2, 3]
    ```
    
    There has to be `prelude.sasl` file within the same directory the file importing is in. It is also possible to import SASL files from subdirectories by specifiying the relative path including subdirectories. Imports from root directories are not (yet) supported.

# Benchmarks
The following benchmarks were conducted using [Hyperfine](https://github.com/sharkdp/hyperfine):
```
hyperfine --warumup 3 './sasl -c [FILE.sasl]'
```
1. Naive Fibonacci algorithm shown in the examples: `fib 25` \
    Without optimizations:
    ```
    Time (mean ± σ):      1.385 s ±  0.037 s    [User: 1.385 s, System: 0.001 s]
    Range (min … max):    1.318 s …  1.431 s    10 runs
    ```
    With optimizations ~11% faster:
    ```
    Time (mean ± σ):      1.229 s ±  0.026 s    [User: 1.227 s, System: 0.002 s]
    Range (min … max):    1.196 s …  1.266 s    10 runs
    ```
2. Computing the first 50 prime numbers using the sieve of eratosthenes implementation shown in the examples: `take 50 sieve` \
    Without optimizations:
    ```
    Time (mean ± σ):     824.3 ms ±  21.8 ms    [User: 818.6 ms, System: 4.6 ms]
    Range (min … max):   801.5 ms … 850.1 ms    10 runs
    ```
    With optimizations ~42% faster:
    ```
    Time (mean ± σ):     477.8 ms ±  17.5 ms    [User: 475.6 ms, System: 2.1 ms]
    Range (min … max):   454.4 ms … 510.5 ms    10 runs
    ```
3. Computing the ackermann function:
    ```
    def ackermann m n = 
    if m > 0 and n = 0 
        then (ackermann (m-1) 1) 
    else 
        if m > 0 and n > 0
            then (ackermann (m-1) (ackermann m (n-1))) 
        else n+1
    .
    ackermann 3 4
    ```
    Without optimizations:
    ```
    Time (mean ± σ):     380.9 ms ±  16.7 ms    [User: 378.9 ms, System: 2.2 ms]
    Range (min … max):   354.5 ms … 402.9 ms    10 runs
    ```
    With optimizations ~35% faster:
    ```
    Time (mean ± σ):     247.0 ms ±  13.4 ms    [User: 246.1 ms, System: 1.5 ms]
    Range (min … max):   230.7 ms … 268.1 ms    11 runs
    ```