/// Represents a kind of builtin type we know about
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum BuiltinType {
    /// The builtin 32 bit signed integer type
    I32,
    /// The unit, or void type
    Unit,
}
