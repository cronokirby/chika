mod context;
mod interner;
mod lexer;
mod types;

use context::{Context, Printable};

use std::fs;
use std::io;
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

fn lex(input_file: &Path, debug: bool) -> io::Result<()> {
    let mut ctx = Context::with_main_file(input_file)?;

    // TODO: Avoid copy here
    let main_file = ctx.main_file;
    let source = ctx.source(main_file).unwrap().to_string();
    let mut interner = interner::StringInterner::new(&mut ctx);

    let mut tokens = Vec::<lexer::Token>::new();
    let mut errors = Vec::<lexer::Error>::new();
    for res in lexer::lex(&source, main_file, &mut interner) {
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
