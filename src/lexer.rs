use crate::interner::StringID;

/// Represents the contents of a given token, letting us separate different variants.
#[derive(Clone, Copy, Debug, PartialEq)]
enum TokenType {
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
}
