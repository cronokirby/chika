use std::fmt;

/// Represents a kind of builtin type we know about
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum BuiltinType {
    /// The builtin 32 bit signed integer type
    I32,
    /// The unit, or void type
    Unit,
}

impl fmt::Display for BuiltinType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use BuiltinType::*;

        match self {
            I32 => write!(f, "I32"),
            Unit => write!(f, "Unit"),
        }
    }
}
