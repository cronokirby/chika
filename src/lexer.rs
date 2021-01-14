use std::{iter::Peekable, ops::Range, str::Chars};

use codespan_reporting::diagnostic::Diagnostic;

use crate::context::{Context, Printable, Printer, StringID};
use crate::errors;
use crate::interner::StringInterner;
use crate::types::BuiltinType;
use crate::{codespan_reporting::diagnostic::Label, context::FileID};
use std::io::Write;

/// Represents the contents of a given token, letting us separate different variants.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum TokenType {
    /// { symbol
    OpenBrace,
    /// } symbol,
    CloseBrace,
    /// ( symbol
    OpenParens,
    /// ) symbol
    CloseParens,
    /// ; symbol
    Semicolon,
    /// : symbol
    Colon,
    /// , symbol
    Comma,
    /// + symbol
    Plus,
    /// - symbol
    Minus,
    /// / symbol
    Div,
    /// * symbol
    Times,
    /// = symbol
    Equals,
    /// `fn` keyword
    Fn,
    /// `return` keyword
    Return,
    /// `var` keyword
    Var,
    /// An integer litteral
    IntLit(u32),
    /// A variable name
    VarName(StringID),
    /// A builtin type, as a token
    BuiltinTypeName(BuiltinType),
}

impl Printable for TokenType {
    fn print<'a>(&self, printer: &mut Printer<'a>) -> errors::Result<()> {
        use TokenType::*;

        match *self {
            OpenBrace => write!(printer, "{{")?,
            CloseBrace => write!(printer, "}}")?,
            OpenParens => write!(printer, "(")?,
            CloseParens => write!(printer, ")")?,
            Semicolon => write!(printer, ";")?,
            Colon => write!(printer, ":")?,
            Comma => write!(printer, ",")?,
            Plus => write!(printer, "+")?,
            Minus => write!(printer, "-")?,
            Div => write!(printer, "/")?,
            Times => write!(printer, "*")?,
            Equals => write!(printer, "=")?,
            Fn => write!(printer, "fn")?,
            Return => write!(printer, "return")?,
            Var => write!(printer, "var")?,
            IntLit(i) => write!(printer, "{}", i)?,
            VarName(id) => write!(printer, "{}", printer.ctx.get_string(id))?,
            BuiltinTypeName(b) => b.print(printer)?,
        }
        Ok(())
    }
}

/// A token that we actually emit.
///
/// This includes the range in the source code that the token spans, as well
/// as the underlying token type.
#[derive(Clone, Debug, PartialEq)]
pub struct Token {
    /// The range in indices that this token spans in the code
    pub range: Range<usize>,
    /// The underlying type of this token
    pub token: TokenType,
}

impl Token {
    /// Create a new token from a range and a token type
    pub fn new(range: Range<usize>, token: TokenType) -> Self {
        Token { range, token }
    }
}

impl Printable for Token {
    fn print<'a>(&self, printer: &mut Printer<'a>) -> errors::Result<()> {
        self.token.print(printer)?;
        write!(printer, "\t{:?}", self.range)?;
        Ok(())
    }
}

#[derive(Clone, Copy, Debug)]
enum ErrorType {
    UnexpectedChar(char),
}

impl ErrorType {
    fn at(self, file: FileID, range: Range<usize>) -> Error {
        Error {
            error: self,
            file,
            range,
        }
    }
}

#[derive(Debug)]
pub struct Error {
    file: FileID,
    range: Range<usize>,
    error: ErrorType,
}

impl Printable for Error {
    fn print<'a>(&self, printer: &mut Printer<'a>) -> errors::Result<()> {
        use ErrorType::*;

        let diagnostic = match self.error {
            UnexpectedChar(c) => Diagnostic::error()
                .with_message(format!("Unexpected Character: `{}`", c))
                .with_labels(vec![Label::primary(self.file, self.range.clone())]),
        };
        printer.write_diagnostic(diagnostic)
    }
}

/// A lexer uses a stream of characters to yield tokens
#[derive(Debug)]
struct Lexer<'a> {
    /// The compilation context we're using
    ctx: &'a mut Context,
    /// An iterator of characters we can peek
    chars: Peekable<Chars<'a>>,
    /// The start position of the current token
    start: usize,
    /// The end position of the current token
    end: usize,
    /// The interner for strings we encounter
    interner: StringInterner,
}

impl<'a> Lexer<'a> {
    fn new(input: &'a str, ctx: &'a mut Context) -> Self {
        Lexer {
            chars: input.chars().peekable(),
            ctx,
            start: 0,
            end: 0,
            interner: StringInterner::new(),
        }
    }

    fn next_char(&mut self) -> Option<char> {
        let next = self.chars.next();
        if let Some(c) = next{
            self.end += c.len_utf8();
        }
        next
    }

    fn skip_whitespace(&mut self) {
        // UNSTABLE: you could use `next_if` here when it stabilizes
        while self.chars.peek().map_or(false, |c| c.is_whitespace()) {
            self.next_char();
        }
    }

    fn continue_identifier(&mut self, start: char) -> String {
        let mut ident = String::from(start);
        while let Some(&peek) = self.chars.peek() {
            if !peek.is_alphanumeric() {
                break;
            }
            self.next_char();
            ident.push(peek);
        }
        ident
    }

    fn continue_int_lit(&mut self, start: char) -> u32 {
        let mut acc: u32 = start.to_digit(10).unwrap();
        while let Some(&peek) = self.chars.peek() {
            match peek.to_digit(10) {
                None => break,
                Some(d) => {
                    self.next_char();
                    acc = 10 * acc + d
                }
            }
        }
        acc
    }
}

impl<'a> Iterator for Lexer<'a> {
    type Item = Result<Token, Error>;

    fn next(&mut self) -> Option<Self::Item> {
        use TokenType::*;

        self.skip_whitespace();

        self.start = self.end;

        let next = match self.next_char() {
            None => return None,
            Some(c) => c,
        };

        let item = match next {
            '{' => OpenBrace,
            '}' => CloseBrace,
            '(' => OpenParens,
            ')' => CloseParens,
            ';' => Semicolon,
            ':' => Colon,
            '+' => Plus,
            '-' => Minus,
            '/' => Div,
            '*' => Times,
            '=' => Equals,
            ',' => Comma,
            c if c.is_digit(10) => {
                let lit = self.continue_int_lit(c);
                IntLit(lit)
            }
            c if c.is_uppercase() => {
                let ident = self.continue_identifier(c);
                match ident.as_str() {
                    "I32" => BuiltinTypeName(BuiltinType::I32),
                    "Unit" => BuiltinTypeName(BuiltinType::Unit),
                    _ => panic!("Unknown type: {}", ident),
                }
            }
            c if c.is_alphabetic() => {
                let ident = self.continue_identifier(c);
                match ident.as_str() {
                    "fn" => Fn,
                    "return" => Return,
                    "var" => Var,
                    _ => VarName(self.interner.intern(&mut self.ctx, ident)),
                }
            }
            c => {
                return Some(Err(
                    ErrorType::UnexpectedChar(c).at(self.ctx.main_file, self.start..self.end)
                ))
            }
        };

        let range = self.start..self.end;
        Some(Ok(Token::new(range, item)))
    }
}

/// Run a lexer on some character input.
///
/// This will return an iterator that lives as long as the string data,
/// and yielding tokens.
pub fn lex<'a>(
    input: &'a str,
    ctx: &'a mut Context,
) -> impl Iterator<Item = Result<Token, Error>> + 'a {
    Lexer::new(input, ctx)
}
