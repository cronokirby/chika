use std::collections::HashMap;

use crate::context::{Context, StringID};

/// A String interner lets us accumulate strings into a table, mapping them into IDs.
///
/// An interner should be kept around to consume all the strings you want to intern,
/// before then finalizing the interner by turning it into a [StringTable](StringTable).
///
/// The interner is **deterministic**, so interning the same sequence of strings twice
/// should yield the same sequence of IDs.
///
/// # Examples
///
/// ```rust
/// let mut interner = StringInterner::new();
/// let id1 = interner.add("a".into());
/// let id2 = interner.add("b".into());
/// let id3 = interner.add("a".into());
/// assert_eq!(id1, id3);
/// assert_ne!(id1, id2);
/// ```
#[derive(Debug)]
pub struct StringInterner<'a> {
    ctx: &'a mut Context,
    ids: HashMap<String, StringID>,
}

impl<'a> StringInterner<'a> {
    /// Create a new interner, with no state whatsoever.
    pub fn new(ctx: &'a mut Context) -> Self {
        Self {
            ctx,
            ids: HashMap::new(),
        }
    }

    /// Intern a String, returning an ID to use instead.
    ///
    /// Two different strings map to two different IDs, and the same string
    /// will map to the same ID.
    pub fn intern(&mut self, string: String) -> StringID {
        if let Some(&id) = self.ids.get(&string) {
            return id;
        }
        let id = self.ctx.add_string(string.clone());
        self.ids.insert(string, id);
        id
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn adding_two_strings_gives_different_ids() {
        let mut ctx = Context::empty();
        let mut interner = StringInterner::new(&mut ctx);
        let id1 = interner.intern("A".into());
        let id2 = interner.intern("B".into());
        assert_ne!(id1, id2);
    }

    #[test]
    fn adding_same_string_gives_same_ids() {
        let mut ctx = Context::empty();
        let mut interner = StringInterner::new(&mut ctx);
        let id1 = interner.intern("A".into());
        let id2 = interner.intern("A".into());
        assert_eq!(id1, id2);
    }

    #[test]
    fn making_table_uses_interned_strings() {
        let mut ctx = Context::empty();
        let mut interner = StringInterner::new(&mut ctx);
        let id1 = interner.intern("A".into());
        let id2 = interner.intern("B".into());
        assert_eq!(ctx.get_string(id1), "A");
        assert_eq!(ctx.get_string(id2), "B");
    }
}
