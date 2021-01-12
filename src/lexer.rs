use std::{iter::Peekable, str::Chars};

use crate::interner::StringID;
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
    IntLit(i64),
    /// A variable name
    VarName(StringID),
    /// A builtin type, as a token
    BuiltinType(BuiltinType),
}

/// A lexer uses a stream of characters to yield tokens
#[derive(Debug)]
struct Lexer<'a> {
    /// An iterator of characters we can peek
    chars: Peekable<Chars<'a>>,
}

impl<'a> Lexer<'a> {
    fn new(input: &'a str) -> Self {
        Lexer {
            chars: input.chars().peekable(),
        }
    }

    fn skip_whitespace(&mut self) {
        // UNSTABLE: you could use `next_if` here when it stabilizes
        while self.chars.peek().map_or(false, |c| c.is_whitespace()) {
            self.chars.next();
        }
    }
}

impl<'a> Iterator for Lexer<'a> {
    type Item = TokenType;

    fn next(&mut self) -> Option<Self::Item> {
        use TokenType::*;

        self.skip_whitespace();

        let next = match self.chars.next() {
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
            c => panic!("unexpected character {}", c),
        };
        Some(item)
    }
}

/// Run a lexer on some character input.
///
/// This will return an iterator that lives as long as the string data,
/// and yielding tokens.
pub fn lex<'a>(input: &'a str) -> impl Iterator<Item = TokenType> + 'a {
    Lexer::new(input)
}
