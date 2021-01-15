mod context;
mod errors;
mod interner;
mod lexer;
mod parser;
mod types;

use context::{Context, Printable};
use errors::Error;

use std::io::Write;
use std::path::{Path, PathBuf};
use structopt::StructOpt;

extern crate codespan_reporting;

use codespan_reporting::term::termcolor::{Color, ColorSpec, StandardStream, WriteColor};
use codespan_reporting::{files::Files, term::termcolor::ColorChoice};

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

fn lex(input_file: &Path, debug: bool) -> Result<(), Error> {
    let mut ctx = Context::with_main_file(input_file)?;

    let mut tokens = Vec::<lexer::Token>::new();
    let mut errors = Vec::<lexer::Error>::new();

    let source = ctx.source(ctx.main_file).unwrap().to_string();
    for res in lexer::lex(&source, &mut ctx) {
        match res {
            Ok(tok) => tokens.push(tok),
            Err(e) => errors.push(e),
        }
    }

    if !errors.is_empty() {
        let mut out = StandardStream::stderr(ColorChoice::Always);
        let mut printer = context::Printer::new(&mut out, &ctx);
        printer.set_color(ColorSpec::new().set_fg(Some(Color::Red)).set_bold(true))?;
        writeln!(&mut printer, "Lexer Errors:\n")?;
        printer.reset()?;
        for e in errors {
            e.print(&mut printer)?;
        }
        return Ok(());
    } else if debug {
        for t in tokens {
            println!("{:?}", t);
        }
        println!("Context:\n{:#?}", &ctx);
    } else {
        let mut stdout = StandardStream::stdout(ColorChoice::Always);
        let mut printer = context::Printer::new(&mut stdout, &ctx);
        writeln!(&mut printer, "Tokens:")?;
        for t in tokens {
            t.print(&mut printer)?;
            writeln!(&mut printer)?;
        }
        printer.flush()?;
    }
    Ok(())
}

fn main() {
    use Command::*;

    let args = Command::from_args();
    let res = match args {
        Lex { input_file, debug } => lex(&input_file, debug),
        Parse { .. } => {
            eprintln!("Parsing is not yet implemented.");
            Ok(())
        }
        Simplify { .. } => {
            eprintln!("Simplification is not yet implemented.");
            Ok(())
        }
        TypeCheck { .. } => {
            eprintln!("Type Checking is not yet implemented.");
            Ok(())
        }
        Compile { .. } => {
            eprintln!("Compilation is not yet implemented.");
            Ok(())
        }
    };
    if let Err(e) = res {
        eprintln!("Unexpected Error:\n{}", e);
    }
}
