use std::{collections::HashMap, ops::Index};

/// A String ID can be used in place of a string basically everywhere.
///
/// The idea is that each unique String ID corresponds to an original string
/// in the source code. The advantage of using IDs is that comparison is much faster,
/// and they use up much less space.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct StringID(u32);

/// A table mapping StringIDs to their original Strings.
///
/// After interning, you have a bunch of IDs representing Strings in the original
/// source code. This table allows displaying these IDs using those strings.
///
/// This struct implements [Index](std::ops::Index), so you can do `table[id]`, provided `id`
/// is a [StringID](StringID)
#[derive(Debug)]
pub struct StringTable {
    table: Vec<String>,
}

impl Index<StringID> for StringTable {
    type Output = str;

    fn index(&self, index: StringID) -> &Self::Output {
        self.table.index(index.0 as usize)
    }
}

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
pub struct StringInterner {
    ids: HashMap<String, StringID>,
    table: Vec<String>,
}

impl StringInterner {
    /// Create a new interner, with no state whatsoever.
    pub fn new() -> Self {
        Self {
            ids: HashMap::new(),
            table: Vec::new(),
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
        let id = StringID(self.table.len() as u32);
        self.table.push(string.clone());
        self.ids.insert(string, id);
        id
    }

    /// Consume this interner, and get a table of all the strings interned.
    ///
    /// Since this moves the interner, this should only be called after all
    /// the strings you'd want to intern have been seen.
    pub fn make_table(self) -> StringTable {
        StringTable { table: self.table }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn adding_two_strings_gives_different_ids() {
        let mut interner = StringInterner::new();
        let id1 = interner.intern("A".into());
        let id2 = interner.intern("B".into());
        assert_ne!(id1, id2);
    }

    #[test]
    fn adding_same_string_gives_same_ids() {
        let mut interner = StringInterner::new();
        let id1 = interner.intern("A".into());
        let id2 = interner.intern("A".into());
        assert_eq!(id1, id2);
    }

    #[test]
    fn making_table_uses_interned_strings() {
        let mut interner = StringInterner::new();
        let id1 = interner.intern("A".into());
        let id2 = interner.intern("B".into());
        let table = interner.make_table();
        assert_eq!(&table[id1], "A");
        assert_eq!(&table[id2], "B");
    }
}
