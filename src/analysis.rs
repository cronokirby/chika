use crate::{context::StringID, types::BuiltinType};

/// Represents the information we have about some function
#[derive(Debug)]
pub struct Function {
    /// The original name of this function
    pub name: StringID,
    /// The return type of this function
    pub return_type: BuiltinType,
    /// The types of the arguments, if any.
    ///
    /// This also serves as a way of storing the number of arguments, as well
    pub arg_types: Vec<BuiltinType>,
}

impl Function {
    fn new(name: StringID, return_type: BuiltinType, arg_types: Vec<BuiltinType>) -> Self {
        Function {
            name,
            return_type,
            arg_types,
        }
    }
}

/// The information we have about a variable in the program
#[derive(Debug)]
pub struct Variable {
    /// The original name the variable had
    pub name: StringID,
    /// The type of this variable
    pub typ: BuiltinType,
}

impl Variable {
    fn new(name: StringID, typ: BuiltinType) -> Self {
        Variable { name, typ }
    }
}
