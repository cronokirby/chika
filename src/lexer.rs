use std::{iter::Peekable, ops::Range, str::Chars};

use crate::interner::{StringID, StringInterner};
use crate::types::BuiltinType;

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

/// A lexer uses a stream of characters to yield tokens
#[derive(Debug)]
struct Lexer<'a> {
    /// An iterator of characters we can peek
    chars: Peekable<Chars<'a>>,
    /// The start position of the current token
    start: usize,
    /// The end position of the current token
    end: usize,
    /// The interner for strings we encounter
    interner: &'a mut StringInterner,
}

impl<'a> Lexer<'a> {
    fn new(input: &'a str, interner: &'a mut StringInterner) -> Self {
        Lexer {
            chars: input.chars().peekable(),
            start: 0,
            end: 0,
            interner,
        }
    }

    fn next_char(&mut self) -> Option<char> {
        let next = self.chars.next();
        if next.is_some() {
            self.end += 1;
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
    type Item = Token;

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
                    _ => VarName(self.interner.intern(ident)),
                }
            }
            c => panic!("unexpected character {}", c),
        };

        let range = self.start..self.end;
        Some(Token::new(range, item))
    }
}

/// Run a lexer on some character input.
///
/// This will return an iterator that lives as long as the string data,
/// and yielding tokens.
pub fn lex<'a>(
    input: &'a str,
    interner: &'a mut StringInterner,
) -> impl Iterator<Item = Token> + 'a {
    Lexer::new(input, interner)
}
