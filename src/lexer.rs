use std::{iter::Peekable, str::Chars};

use crate::builtin;
use crate::context::{
    Context, Diagnostic, DisplayContext, DisplayWithContext, IsDiagnostic, Location, StringID,
};
use crate::interner::StringInterner;
use crate::{codespan_reporting::diagnostic::Label, context::FileID};
use std::fmt;

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
    /// += symbol
    PlusEqual,
    /// - symbol
    Minus,
    /// -= symbol
    MinusEqual,
    /// / symbol
    Div,
    /// /= symbol
    DivEqual,
    /// * symbol
    Times,
    /// *= symbol
    TimesEqual,
    /// = symbol
    Equals,
    /// == symbol
    EqualsEquals,
    /// ! symbol
    Bang,
    /// != symbol
    BangEquals,
    /// < symbol
    Less,
    /// <= symbol
    LessEqual,
    /// > symbol
    Greater,
    /// >= symbol
    GreaterEqual,
    /// | symbol
    Or,
    /// |= symbol
    OrEqual,
    /// || symbol
    OrOr,
    /// & symbol
    And,
    /// &= symbol
    AndEqual,
    /// && symbol
    AndAnd,
    /// `fn` keyword
    Fn,
    /// `return` keyword
    Return,
    /// `var` keyword
    Var,
    /// `if` keyword
    If,
    /// `else` keyword
    Else,
    /// An integer litteral
    IntLit(u32),
    /// A variable name
    VarName(StringID),
    /// A builtin type, as a token
    BuiltinTypeName(builtin::Type),
    /// A builtin function, as a token
    BuiltinFunction(builtin::BuiltinFunction),
}

impl DisplayWithContext for TokenType {
    fn fmt_with(&self, ctx: DisplayContext<'_>, f: &mut fmt::Formatter) -> fmt::Result {
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
            PlusEqual => write!(f, "+="),
            Minus => write!(f, "-"),
            MinusEqual => write!(f, "-="),
            Div => write!(f, "/"),
            DivEqual => write!(f, "/="),
            Times => write!(f, "*"),
            TimesEqual => write!(f, "*="),
            Equals => write!(f, "="),
            EqualsEquals => write!(f, "=="),
            Bang => write!(f, "!"),
            BangEquals => write!(f, "!="),
            Less => write!(f, "<"),
            LessEqual => write!(f, "<="),
            Greater => write!(f, ">"),
            GreaterEqual => write!(f, ">="),
            Or => write!(f, "|"),
            OrEqual => write!(f, "|="),
            OrOr => write!(f, "||"),
            And => write!(f, "&"),
            AndEqual => write!(f, "&="),
            AndAnd => write!(f, "&&"),
            Fn => write!(f, "fn"),
            Return => write!(f, "return"),
            Var => write!(f, "var"),
            If => write!(f, "if"),
            Else => write!(f, "else"),
            IntLit(i) => write!(f, "{}", i),
            VarName(id) => write!(f, "{}", ctx.ctx.get_string(id)),
            BuiltinTypeName(b) => write!(f, "{}", b),
            BuiltinFunction(b) => write!(f, "{}", b),
        }
    }
}

/// A token that we actually emit.
///
/// This includes the range in the source code that the token spans, as well
/// as the underlying token type.
#[derive(Clone, Debug)]
pub struct Token {
    /// The location of this token
    pub location: Location,
    /// The underlying type of this token
    pub token: TokenType,
}

impl Token {
    /// Create a new token from a location and a token type
    pub fn new(location: Location, token: TokenType) -> Self {
        Token { location, token }
    }
}

impl DisplayWithContext for Token {
    fn fmt_with<'a>(&self, ctx: DisplayContext<'a>, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}\t{}..{}",
            self.token.with_ctx(ctx),
            self.location.start,
            self.location.end
        )
    }
}

#[derive(Clone, Copy, Debug)]
enum ErrorType {
    UnexpectedChar(char),
}

impl ErrorType {
    fn at(self, file: FileID, start: usize, end: usize) -> Error {
        Error {
            error: self,
            location: Location::new(file, start, end),
        }
    }
}

#[derive(Debug)]
pub struct Error {
    location: Location,
    error: ErrorType,
}

impl IsDiagnostic for Error {
    fn diagnostic(&self, _ctx: &Context) -> Diagnostic {
        use ErrorType::*;

        match self.error {
            UnexpectedChar(c) => Diagnostic::error()
                .with_message(format!("Unexpected Character: `{}`", c))
                .with_labels(vec![Label::primary(self.location.file, self.location)]),
        }
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
            if !(peek.is_alphanumeric() || peek == '_') {
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
            '+' => match self.chars.peek() {
                Some('=') => {
                    self.next();
                    PlusEqual
                }
                _ => Plus,
            },
            '-' => match self.chars.peek() {
                Some('=') => {
                    self.next();
                    MinusEqual
                }
                _ => Minus,
            },
            '/' => match self.chars.peek() {
                Some('=') => {
                    self.next();
                    DivEqual
                }
                _ => Div,
            },
            '*' => match self.chars.peek() {
                Some('=') => {
                    self.next();
                    TimesEqual
                }
                _ => Times,
            },
            ',' => Comma,
            '<' => match self.chars.peek() {
                Some('=') => {
                    self.next();
                    LessEqual
                }
                _ => Less,
            },
            '>' => match self.chars.peek() {
                Some('=') => {
                    self.next();
                    GreaterEqual
                }
                _ => Greater,
            },
            '=' => match self.chars.peek() {
                Some('=') => {
                    self.next();
                    EqualsEquals
                }
                _ => Equals,
            },
            '|' => match self.chars.peek() {
                Some('|') => {
                    self.next();
                    OrOr
                }
                Some('=') => {
                    self.next();
                    OrEqual
                }
                _ => Or,
            },
            '&' => match self.chars.peek() {
                Some('&') => {
                    self.next();
                    AndAnd
                }
                Some('=') => {
                    self.next();
                    AndEqual
                }
                _ => And,
            },
            '!' => match self.chars.peek() {
                Some('=') => {
                    self.next();
                    BangEquals
                }
                _ => Bang,
            },
            '#' => {
                let name = self.continue_identifier('#');
                match builtin::BuiltinFunction::from_name(&name) {
                    None => panic!("Unknown builtin: {}", name),
                    Some(b) => BuiltinFunction(b),
                }
            }
            c if c.is_digit(10) => {
                let lit = self.continue_int_lit(c);
                IntLit(lit)
            }
            c if c.is_uppercase() => {
                let ident = self.continue_identifier(c);
                match builtin::Type::from_name(&ident) {
                    None => panic!("Unknown type: {}", ident),
                    Some(t) => BuiltinTypeName(t),
                }
            }
            c if c.is_alphabetic() || c == '_' => {
                let ident = self.continue_identifier(c);
                match ident.as_str() {
                    "fn" => Fn,
                    "return" => Return,
                    "var" => Var,
                    "if" => If,
                    "else" => Else,
                    _ => VarName(self.interner.intern(&mut self.ctx, ident)),
                }
            }
            c => {
                return Some(Err(ErrorType::UnexpectedChar(c).at(
                    self.ctx.main_file,
                    self.start,
                    self.end,
                )))
            }
        };

        let loc = Location::new(self.ctx.current_file, self.start, self.end);
        Some(Ok(Token::new(loc, item)))
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
        should_lex("a b foo地3 a34 I32 Unit Bool");
    }

    #[test]
    fn literals_lex() {
        should_lex("23 2343 1234567890");
    }

    #[test]
    fn unknown_characters_fail() {
        should_not_lex("² ΅ ´");
    }

    #[test]
    fn if_else_lexes() {
        should_lex("if else")
    }

    #[test]
    fn boolean_operators_lex() {
        should_lex("== != > >= < <= || && | & !");
    }

    #[test]
    fn assignment_operators_lex() {
        should_lex("== += *= /= -= &= |=");
    }

    #[test]
    fn identifiers_with_underscores_lex() {
        should_lex("print_int _foo");
    }

    #[test]
    fn builtin_function_identifiers_lex() {
        should_lex("#print_i32()");
    }
}
