use std::fmt;

/// Represents a kind of builtin type we know about
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Type {
    /// The builtin 32 bit signed integer type
    I32,
    /// The unit, or void type
    Unit,
    /// The type of booleans
    Bool,
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use Type::*;

        match self {
            I32 => write!(f, "I32"),
            Unit => write!(f, "Unit"),
            Bool => write!(f, "Bool"),
        }
    }
}

/// Represents some known builtin function
#[derive(Clone, Copy, Debug, PartialEq)]
enum BuiltinFunction {
    /// A builtin to print the value of an integer
    PrintI32,
}

impl BuiltinFunction {
    /// Get the signature of some builtin function
    pub fn signature(self) -> (Vec<Type>, Type) {
        match self {
            BuiltinFunction::PrintI32 => (vec![Type::I32], Type::Unit),
        }
    }

    /// Create a known builtin, by checking for a known name
    pub fn from_name(name: &str) -> Option<Self> {
        match name {
            "print_i32" => Some(BuiltinFunction::PrintI32),
            _ => None,
        }
    }
}
