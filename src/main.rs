mod analysis;
mod backend;
mod builtin;
mod context;
mod errors;
mod interner;
mod lexer;
mod parser;

use crate::context::DisplayWithContext;
use analysis::analyze;
use context::{Context, IsDiagnostic};
use errors::Error;

use std::fs::File;
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

fn lex(ctx: &mut Context) -> Result<Option<Vec<lexer::Token>>, Error> {
    let mut tokens = Vec::<lexer::Token>::new();
    let mut errors = Vec::<lexer::Error>::new();

    let source = ctx.files.source(ctx.main_file).unwrap().to_string();
    for res in lexer::lex(&source, ctx) {
        match res {
            Ok(tok) => tokens.push(tok),
            Err(e) => errors.push(e),
        }
    }

    if !errors.is_empty() {
        let mut out = StandardStream::stderr(ColorChoice::Always);
        out.set_color(ColorSpec::new().set_fg(Some(Color::Red)).set_bold(true))?;
        writeln!(&mut out, "Lexer Errors:\n")?;
        out.reset()?;
        for e in errors {
            ctx.emit_diagnostic(&mut out, &e.diagnostic(ctx))?;
        }
        return Ok(None);
    }

    Ok(Some(tokens))
}

fn lex_and_stop(input_file: &Path, debug: bool) -> Result<(), Error> {
    let mut ctx = Context::with_main_file(input_file)?;

    let tokens = match lex(&mut ctx)? {
        None => return Ok(()),
        Some(tokens) => tokens,
    };

    if debug {
        for t in tokens {
            println!("{:?}", t);
        }
        println!("Context:\n{:#?}", &ctx);
    } else {
        let mut stdout = StandardStream::stdout(ColorChoice::Always);
        writeln!(stdout, "Tokens:")?;
        for t in tokens {
            writeln!(stdout, "{}", t.with_ctx(&ctx))?;
        }
        stdout.flush()?;
    }
    Ok(())
}

fn parse(ctx: &Context, tokens: Vec<lexer::Token>) -> Result<Option<parser::AST>, Error> {
    let file_size = ctx.files.file_size(ctx.main_file)?;
    let res = parser::parse(tokens, ctx.main_file, file_size);
    match res {
        Ok(ast) => Ok(Some(ast)),
        Err(errors) => {
            let mut out = StandardStream::stderr(ColorChoice::Always);
            out.set_color(ColorSpec::new().set_fg(Some(Color::Red)).set_bold(true))?;
            writeln!(out, "Parser Errors:\n")?;
            out.reset()?;
            for e in errors {
                ctx.emit_diagnostic(&mut out, &e.diagnostic(&ctx))?;
            }
            Ok(None)
        }
    }
}

fn parse_and_stop(input_file: &Path) -> Result<(), Error> {
    let mut ctx = Context::with_main_file(input_file)?;

    let tokens = match lex(&mut ctx)? {
        None => return Ok(()),
        Some(tokens) => tokens,
    };

    let ast = match parse(&ctx, tokens)? {
        None => return Ok(()),
        Some(tokens) => tokens,
    };

    println!("{}", ast.with_ctx(&ctx));
    Ok(())
}

fn typecheck(ctx: &Context, ast: parser::AST) -> Result<Option<analysis::AST>, Error> {
    match analyze(ctx, &ast) {
        Ok(ast) => Ok(Some(ast)),
        Err(errors) => {
            let mut out = StandardStream::stderr(ColorChoice::Always);
            out.set_color(ColorSpec::new().set_fg(Some(Color::Red)).set_bold(true))?;
            writeln!(out, "Typer Errors:\n")?;
            out.reset()?;
            for e in errors {
                ctx.emit_diagnostic(&mut out, &e.diagnostic(&ctx))?;
            }
            Ok(None)
        }
    }
}

fn typecheck_and_stop(input_file: &Path) -> Result<(), Error> {
    let mut ctx = Context::with_main_file(input_file)?;

    let tokens = match lex(&mut ctx)? {
        None => return Ok(()),
        Some(tokens) => tokens,
    };

    let parsed_ast = match parse(&ctx, tokens)? {
        None => return Ok(()),
        Some(parsed_ast) => parsed_ast,
    };

    let ast = match typecheck(&ctx, parsed_ast)? {
        None => return Ok(()),
        Some(ast) => ast,
    };

    println!("{}", ast.with_ctx(&ctx));
    Ok(())
}

fn compile(input_file: &Path, output: &Path) -> Result<(), Error> {
    let mut ctx = Context::with_main_file(input_file)?;

    let tokens = match lex(&mut ctx)? {
        None => return Ok(()),
        Some(tokens) => tokens,
    };

    let parsed_ast = match parse(&ctx, tokens)? {
        None => return Ok(()),
        Some(parsed_ast) => parsed_ast,
    };

    let ast = match typecheck(&ctx, parsed_ast)? {
        None => return Ok(()),
        Some(ast) => ast,
    };

    let mut file = File::create(output)?;
    backend::generate_c(&mut file, ast)
}

fn main() {
    use Command::*;

    let args = Command::from_args();
    let res = match args {
        Lex { input_file, debug } => lex_and_stop(&input_file, debug),
        Parse { input_file } => parse_and_stop(&input_file),
        TypeCheck { input_file } => typecheck_and_stop(&input_file),
        Compile { input_file, output } => compile(&input_file, &output),
    };
    if let Err(e) = res {
        eprintln!("Unexpected Error:\n{}", e);
    }
}
