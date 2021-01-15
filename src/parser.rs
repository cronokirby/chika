use std::rc::Rc;

use crate::context::{Location, StringID};

/// Represents the kind of shape that a node can have.
///
/// We need this, because everything we have is stored in this unified
/// node type, and we need to handle terminal things like strings and literals.
#[derive(Debug)]
enum NodeShape {
    /// This node is a terminal reference to a string
    String(StringID),
    /// This node is a terminal reference to an integer
    IntLit(u32),
    /// This node branches off to contain other nodes
    Branch(Vec<Rc<Node>>),
}

/// Represents a single raw Node in our AST.
///
/// Our overall AST structure is based on representing things
/// with our plain untyped representation, and then using a typed outer layer
/// for actually manipulating things.
#[derive(Debug)]
struct Node {
    /// The location of this node in the original file
    location: Location,
    /// The shape of this node
    shape: NodeShape,
}

impl Node {
    fn string(&self) -> StringID {
        match &self.shape {
            NodeShape::String(s) => *s,
            other => panic!("expected string, found: {:?}", other),
        }
    }

    fn int_lit(&self) -> u32 {
        match &self.shape {
            NodeShape::IntLit(v) => *v,
            other => panic!("expected int lit, found: {:?}", other),
        }
    }

    fn branch(&self) -> &[Rc<Node>] {
        match &self.shape {
            NodeShape::Branch(v) => v,
            other => panic!("expected branch, found: {:?}", other),
        }
    }
}
