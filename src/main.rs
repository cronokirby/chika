mod interner;
mod lexer;
mod printer;
mod types;
use printer::Printable;

use std::fs;
use std::io;
use std::io::Write;
use std::path::{Path, PathBuf};
use structopt::StructOpt;

/// A command that our CLI can process.
#[derive(Debug, StructOpt)]
enum Command {
    /// Print the tokens produced by the lexer
    Lex {
        /// Print using debug format instead
        #[structopt(long = "debug")]
        debug: bool,
        /// The file containing Chika code you want to lex
        #[structopt(name = "INPUT_FILE", parse(from_os_str))]
        input_file: PathBuf,
    },
    /// Print the AST produced by the parser
    Parse {
        /// The file containing Chika code you want to parse
        #[structopt(name = "INPUT_FILE", parse(from_os_str))]
        input_file: PathBuf,
    },
    /// Print the simplified AST
    Simplify {
        /// The file containing Chika code you want to simplify
        #[structopt(name = "INPUT_FILE", parse(from_os_str))]
        input_file: PathBuf,
    },
    /// Run the type checker, printing the typed AST
    TypeCheck {
        /// The file containing Chika code you want to check
        #[structopt(name = "INPUT_FILE", parse(from_os_str))]
        input_file: PathBuf,
    },
    /// Compile the file
    Compile {
        /// The file containing Chika code you want to check
        #[structopt(name = "INPUT_FILE", parse(from_os_str))]
        input_file: PathBuf,
        /// The output file to use
        #[structopt(short, long, parse(from_os_str))]
        output: PathBuf,
    },
}

fn lex(input_file: &Path, debug: bool) -> io::Result<()> {
    let input = fs::read_to_string(&input_file)?;
    let mut interner = interner::StringInterner::new();
    let tokens: Vec<lexer::Token> = lexer::lex(&input, &mut interner).collect();

    let table = interner.make_table();
    let mut stdout = io::stdout();
    let mut printer = printer::Printer::new(&mut stdout, &table);
    writeln!(&mut printer, "Tokens:")?;
    for t in tokens {
        if debug {
            write!(&mut printer, "{:?}", t)?;
        } else {
            t.print(&mut printer)?;
        }
        writeln!(&mut printer)?;
    }
    if debug {
        writeln!(&mut printer, "Table:\n{:?}", &table)?;
    }
    printer.flush()
}

fn main() -> io::Result<()> {
    use Command::*;

    let args = Command::from_args();
    match args {
        Lex { input_file, debug } => lex(&input_file, debug)?,
        Parse { .. } => eprintln!("Parsing is not yet implemented."),
        Simplify { .. } => eprintln!("Simplification is not yet implemented."),
        TypeCheck { .. } => eprintln!("Type Checking is not yet implemented."),
        Compile { .. } => eprintln!("Compilation is not yet implemented."),
    };
    Ok(())
}
