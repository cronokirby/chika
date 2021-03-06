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

impl Type {
    /// Try and recognize a known type name
    pub fn from_name(name: &str) -> Option<Type> {
        match name {
            "I32" => Some(Type::I32),
            "Unit" => Some(Type::Unit),
            "Bool" => Some(Type::Bool),
            _ => None,
        }
    }
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Type::I32 => write!(f, "I32"),
            Type::Unit => write!(f, "Unit"),
            Type::Bool => write!(f, "Bool"),
        }
    }
}

/// Represents some known builtin function
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum BuiltinFunction {
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
            "#print_i32" => Some(BuiltinFunction::PrintI32),
            _ => None,
        }
    }
}

impl fmt::Display for BuiltinFunction {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            BuiltinFunction::PrintI32 => write!(f, "#print_i32"),
        }
    }
}
