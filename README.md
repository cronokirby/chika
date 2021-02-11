# chika

This is a little programming language I'm working on, that's at about
the same abstraction level as C, but without a lot of the cruft.

My main goal with this project is *not* to make a better C, but rather
to learn about writing optimizing compilers, and compiling down to assembly.
I could do this by writing a C compiler, but I think it's easier to work with
a green-field language, without having to worry about the all the weird
decisions we're left with in C after all of these years.

# Examples

*This syntax is still experiemental*.

```chika
fn foo(x: I32, y: I32): I32 {
  return x + y;
}

fn main(): Unit {
  #print_i32(foo(33, 34));
}
```

# Usage

At the moment, a basic C backend has been implemented, along with a small subset
of the language.

The CLI looks like this

```txt
chika 0.2.0
A command that our CLI can process

USAGE:
    chika <SUBCOMMAND>

FLAGS:
    -h, --help       Prints help information
    -V, --version    Prints version information

SUBCOMMANDS:
    compile       Compile the file
    help          Prints this message or the help of the given subcommand(s)
    lex           Print the tokens produced by the lexer
    parse         Print the AST produced by the parser
    type-check    Run the type checker, printing the typed AST
```

## Lexing

```txt
chika-lex 0.2.0
Print the tokens produced by the lexer

USAGE:
    chika lex [FLAGS] <INPUT_FILE>

FLAGS:
        --debug      Print using debug format instead
    -h, --help       Prints help information
    -V, --version    Prints version information

ARGS:
    <INPUT_FILE>    The file containing Chika code you want to lex
```

## Parsing

```txt
chika-parse 0.2.0
Print the AST produced by the parser

USAGE:
    chika parse <INPUT_FILE>

FLAGS:
    -h, --help       Prints help information
    -V, --version    Prints version information

ARGS:
    <INPUT_FILE>    The file containing Chika code you want to parse
```

## Type Checking

```
chika-type-check 0.2.0
Run the type checker, printing the typed AST

USAGE:
    chika type-check <INPUT_FILE>

FLAGS:
    -h, --help       Prints help information
    -V, --version    Prints version information

ARGS:
    <INPUT_FILE>    The file containing Chika code you want to check
```

## Compilation

At the moment, only a basic C backend has been implemented, and compilation
will output a C file.

```txt
chika-compile 0.2.0
Compile the file

USAGE:
    chika compile <INPUT_FILE> --output <output>

FLAGS:
    -h, --help       Prints help information
    -V, --version    Prints version information

OPTIONS:
    -o, --output <output>    The output file to use

ARGS:
    <INPUT_FILE>    The file containing Chika code you want to check
```
