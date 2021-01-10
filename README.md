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
struct X {
  y: I32;
  z: I32;
}

fn foo(x: I32, y: I32): I32 {
  var s: X = {y: y, z: x};
  return s.y + s.z;
}

fn main() {
  print_int(foo(33, 34));
}
```

# Usage

Nothing is implemented yet, but this is how the CLI looks so far:

```txt
chika 0.1.0
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
    simplify      Print the simplified AST
    type-check    Run the type checker, printing the typed AST
```

## Lexing

**Not implemented yet**

```txt
chika-lex 0.1.0
Print the tokens produced by the lexer

USAGE:
    chika lex <INPUT_FILE>

FLAGS:
    -h, --help       Prints help information
    -V, --version    Prints version information

ARGS:
    <INPUT_FILE>    The file containing Chika code you want to lex
```

## Parsing

**Not implemented yet**

```txt
chika-parse 0.1.0
Print the AST produced by the parser

USAGE:
    chika parse <INPUT_FILE>

FLAGS:
    -h, --help       Prints help information
    -V, --version    Prints version information

ARGS:
    <INPUT_FILE>    The file containing Chika code you want to parse
```

## Simplification

**Not implemented yet**

```txt
chika-simplify 0.1.0
Print the simplified AST

USAGE:
    chika simplify <INPUT_FILE>

FLAGS:
    -h, --help       Prints help information
    -V, --version    Prints version information

ARGS:
    <INPUT_FILE>    The file containing Chika code you want to simplify
```

## Type Checking

**Not implemented yet**

```
chika-type-check 0.1.0
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

**Not implemented yet**

```txt
chika-compile 0.1.0
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
