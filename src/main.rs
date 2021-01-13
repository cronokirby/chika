mod interner;
mod lexer;
mod presentation;
mod types;

use presentation::Printable;

use std::fs;
use std::io;
use std::io::Write;
use std::path::{Path, PathBuf};
use structopt::StructOpt;

extern crate codespan_reporting;

use codespan_reporting::term::termcolor::{Color, ColorSpec, StandardStream, WriteColor};
use codespan_reporting::{files::SimpleFile, term::termcolor::ColorChoice};

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
    let file_name = input_file.to_string_lossy().to_string();
    let simple_file = SimpleFile::new(file_name, input);
    let mut interner = interner::StringInterner::new();

    let mut tokens = Vec::<lexer::Token>::new();
    let mut errors = Vec::<lexer::Error>::new();
    for res in lexer::lex(simple_file.source(), &mut interner) {
        match res {
            Ok(tok) => tokens.push(tok),
            Err(e) => errors.push(e),
        }
    }
    if !errors.is_empty() {
        let table = interner.make_table();
        let mut out = StandardStream::stderr(ColorChoice::Always);
        let mut printer = presentation::Printer::new(&mut out, &table, &simple_file);
        printer
            .buf
            .set_color(ColorSpec::new().set_fg(Some(Color::Red)).set_bold(true))
            .unwrap();
        writeln!(&mut printer, "Lexer Errors:\n")?;
        printer.buf.reset().unwrap();
        for e in errors {
            e.print(&mut printer)?;
        }
        return Ok(());
    } else if debug {
        let table = interner.make_table();
        for t in tokens {
            println!("{:?}", t);
        }
        println!("Table:\n{:?}", &table);
    } else {
        let table = interner.make_table();
        let mut stdout = StandardStream::stdout(ColorChoice::Always);
        let mut printer = presentation::Printer::new(&mut stdout, &table, &simple_file);
        writeln!(&mut printer, "Tokens:")?;
        for t in tokens {
            t.print(&mut printer)?;
            writeln!(&mut printer)?;
        }
        printer.flush()?;
    }
    Ok(())
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
