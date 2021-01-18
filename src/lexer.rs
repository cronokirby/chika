use std::{iter::Peekable, ops::Range, str::Chars};

use codespan_reporting::diagnostic::Diagnostic;

use crate::context::{Context, DisplayWithContext, Location, Printable, Printer, StringID};
use crate::errors;
use crate::interner::StringInterner;
use crate::types::BuiltinType;
use crate::{codespan_reporting::diagnostic::Label, context::FileID};
use std::fmt;
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

impl DisplayWithContext for TokenType {
    fn fmt_with(&self, ctx: &Context, f: &mut fmt::Formatter) -> fmt::Result {
        use TokenType::*;

        match *self {
            OpenBrace => write!(f, "{{"),
            CloseBrace => write!(f, "}}"),
            OpenParens => write!(f, "("),
            CloseParens => write!(f, ")"),
            Semicolon => write!(f, ";"),
            Colon => write!(f, ":"),
            Comma => write!(f, ","),
            Plus => write!(f, "+"),
            Minus => write!(f, "-"),
            Div => write!(f, "/"),
            Times => write!(f, "*"),
            Equals => write!(f, "="),
            Fn => write!(f, "fn"),
            Return => write!(f, "return"),
            Var => write!(f, "var"),
            IntLit(i) => write!(f, "{}", i),
            VarName(id) => write!(f, "{}", ctx.get_string(id)),
            BuiltinTypeName(b) => write!(f, "{}", b),
        }
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
        write!(printer, "{}\t{:?}", self.token.with_ctx(printer.ctx), self.range)?;
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
            location: Location::new(file, range),
        }
    }
}

#[derive(Debug)]
pub struct Error {
    location: Location,
    error: ErrorType,
}

impl Printable for Error {
    fn print<'a>(&self, printer: &mut Printer<'a>) -> errors::Result<()> {
        use ErrorType::*;

        let diagnostic = match self.error {
            UnexpectedChar(c) => Diagnostic::error()
                .with_message(format!("Unexpected Character: `{}`", c))
                .with_labels(vec![Label::primary(
                    self.location.file,
                    self.location.range.clone(),
                )]),
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
        if let Some(c) = next {
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

#[cfg(test)]
mod test {
    use super::*;

    fn get_errors(input: &str) -> Vec<Error> {
        let mut errors = Vec::new();
        for res in Lexer::new(input, &mut Context::empty()) {
            if let Err(e) = res {
                errors.push(e);
            }
        }
        errors
    }

    fn should_lex(input: &str) {
        let errors = get_errors(input);
        assert!(errors.is_empty(), "errors = {:?}", errors);
    }

    fn should_not_lex(input: &str) {
        let errors = get_errors(input);
        assert!(!errors.is_empty(), "errors = {:?}", errors);
    }

    #[test]
    fn basic_operators_lex() {
        should_lex("+ / * - () ; : {}");
    }

    #[test]
    fn identifiers_lex() {
        should_lex("a b foo地3 a34 I32 Unit");
    }

    #[test]
    fn literals_lex() {
        should_lex("23 2343 1234567890");
    }

    #[test]
    fn unknown_characters_fail() {
        should_not_lex("² ΅ ´");
    }
}
