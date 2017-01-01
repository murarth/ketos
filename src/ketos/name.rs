//! Implements name interning and containers using names as keys.

use std::collections::HashMap;
use std::error::Error as StdError;
use std::fmt;
use std::iter::FromIterator;
use std::mem::replace;
use std::rc::Rc;
use std::slice::Iter;
use std::sync::Arc;

use function::{SystemFn, SYSTEM_FNS};

/// Represents a name interned within a `NameStore`.
#[derive(Copy, Clone, Debug, Hash, Eq, PartialEq, Ord, PartialOrd)]
pub struct Name(u32);

impl Name {
    /// Returns an invalid name. For internal use only.
    #[doc(hidden)]
    pub fn dummy() -> Name {
        Name(!0)
    }

    /// Returns the integer key referring to this name.
    pub fn get(&self) -> u32 {
        self.0
    }
}

/// Returns the standard name for the given integer value, if it exists.
pub fn get_standard_name(name: u32) -> Option<Name> {
    if name < NUM_STANDARD_NAMES {
        Some(Name(name))
    } else {
        None
    }
}

/// Returns whether the given name is a standard name.
pub fn is_standard_name(name: Name) -> bool {
    name.0 < NUM_STANDARD_NAMES
}

/// Returns whether a standard value corresponds to the given name.
pub fn is_standard_value(name: Name) -> bool {
    name.0 < NUM_STANDARD_VALUES
}

/// Returns the system function for the given name, if one exists.
pub fn get_system_fn(name: Name) -> Option<&'static SystemFn> {
    SYSTEM_FNS.get(name.0 as usize)
}

/// Returns whether the given name corresponds to a system function.
pub fn is_system_fn(name: Name) -> bool {
    name.0 < NUM_SYSTEM_FNS as u32
}

/// Returns whether the given name corresponds to a system operator.
pub fn is_system_operator(name: Name) -> bool {
    name.0 >= SYSTEM_OPERATORS_BEGIN && name.0 < SYSTEM_OPERATORS_END
}

macro_rules! standard_names {
    ( $( $s:expr => $name:ident = $value:expr , )+ ) => {
        /// Contains constants standard name values; interned names which are
        /// universal to all programs.
        #[allow(missing_docs)]
        pub mod standard_names {
            use super::Name;
            $( pub const $name: Name = Name($value); )+

            // TODO: When `const fn` is stable, this will be unnecessary.
            pub mod consts {
                $( pub const $name: u32 = $value; )+
            }
        }

        /// Returns the standard name for the given string representation,
        /// if one exists.
        pub fn get_standard_name_for(s: &str) -> Option<Name> {
            match s {
                $( $s => Some(standard_names::$name), )+
                _ => None
            }
        }

        /// Returns the string representation of the given name,
        /// if it is a standard name.
        pub fn standard_name(name: Name) -> Option<&'static str> {
            match name {
                $( standard_names::$name => Some($s), )+
                _ => None
            }
        }
    }
}

// Any addition, deletion, or modification to these constants constitutes
// a breaking change to the bytecode format.
standard_names!{
    // Names of system functions come first; these are available in global scope.
    // Note that the compiler may still treat some of these specially
    // when possible, e.g. replacing an `=` call with the `Eq` instruction.
    "+" => ADD = 0,
    "-" => SUB = 1,
    "*" => MUL = 2,
    "^" => POW = 3,
    "/" => DIV = 4,
    "//" => FLOOR_DIV = 5,
    "rem" => REM = 6,
    "<<" => SHL = 7,
    ">>" => SHR = 8,
    "=" => EQ = 9,
    "/=" => NOT_EQ = 10,
    "<" => LT = 11,
    ">" => GT = 12,
    "<=" => LE = 13,
    ">=" => GE = 14,
    "zero" => ZERO = 15,
    "max" => MAX = 16,
    "min" => MIN = 17,
    "append" => APPEND = 18,
    "elt" => ELT = 19,
    "concat" => CONCAT = 20,
    "join" => JOIN = 21,
    "len" => LEN = 22,
    "slice" => SLICE = 23,
    "first" => FIRST = 24,
    "second" => SECOND = 25,
    "last" => LAST = 26,
    "init" => INIT = 27,
    "tail" => TAIL = 28,
    "list" => LIST = 29,
    "reverse" => REVERSE = 30,
    "abs" => ABS = 31,
    "ceil" => CEIL = 32,
    "floor" => FLOOR = 33,
    "round" => ROUND = 34,
    "trunc" => TRUNC = 35,
    "int" => INT = 36,
    "float" => FLOAT = 37,
    "inf" => INF = 38,
    "nan" => NAN = 39,
    "denom" => DENOM = 40,
    "fract" => FRACT = 41,
    "numer" => NUMER = 42,
    "rat" => RAT = 43,
    "recip" => RECIP = 44,
    "chars" => CHARS = 45,
    "string" => STRING = 46,
    "bytes" => BYTES = 47,
    "id" => ID = 48,
    "is" => IS = 49,
    "is-instance" => IS_INSTANCE = 50,
    "null" => NULL = 51,
    "type-of" => TYPE_OF = 52,
    "." => DOT = 53,
    ".=" => DOT_EQ = 54,
    "new" => NEW = 55,
    "format" => FORMAT = 56,
    "print" => PRINT = 57,
    "println" => PRINTLN = 58,
    "panic" => PANIC = 59,
    "xor" => XOR = 60,
    "not" => NOT = 61,
    // End of names referring to system functions.
    // The constant `NUM_SYSTEM_FNS` below should be one greater than
    // the value immediately above this comment.

    // Boolean names; the parser will replace these with boolean values.
    // These names must follow immediately after system function names.
    "false" => FALSE = 62,
    "true" => TRUE = 63,
    // End of names referring to standard values.
    // The constant `NUM_STANDARD_VALUES` below should be one greater than
    // the value immediately above this comment.

    // Special operators follow; these are not represented as values in global
    // scope. They are only handled by the compiler.
    "apply" => APPLY = 64,
    "do" => DO = 65,
    "let" => LET = 66,
    "define" => DEFINE = 67,
    "macro" => MACRO = 68,
    "struct" => STRUCT = 69,
    "if" => IF = 70,
    "and" => AND = 71,
    "or" => OR = 72,
    "case" => CASE = 73,
    "cond" => COND = 74,
    "lambda" => LAMBDA = 75,
    "export" => EXPORT = 76,
    "use" => USE = 77,
    "const" => CONST = 78,
    "set-module-doc" => SET_MODULE_DOC = 79,

    // Just plain names follow; these are used by system functions or operators
    // to delineate syntactical constructs or just as name values.
    "all" => ALL = 80,
    "else" => ELSE = 81,
    "optional" => OPTIONAL = 82,
    "key" => KEY = 83,
    "rest" => REST = 84,
    "unbound" => UNBOUND = 85,
    "unit" => UNIT = 86,
    "bool" => BOOL = 87,
    "char" => CHAR = 88,
    "integer" => INTEGER = 89,
    "ratio" => RATIO = 90,
    "struct-def" => STRUCT_DEF = 91,
    "keyword" => KEYWORD = 92,
    "object" => OBJECT = 93,
    "name" => NAME = 94,
    "number" => NUMBER = 95,
    "function" => FUNCTION = 96,
    "path" => PATH = 97,
}

/// Number of standard names
pub const NUM_STANDARD_NAMES: u32 = 98;

/// Number of names, starting at `0`, which refer to system functions.
pub const NUM_SYSTEM_FNS: usize = 62;

/// Number of names, starting at `0`, which refer to standard values.
pub const NUM_STANDARD_VALUES: u32 = 64;

/// First standard name which refers to a system operator.
pub const SYSTEM_OPERATORS_BEGIN: u32 = NUM_STANDARD_VALUES;
/// One-past-the-end of standard names which refer to system operators.
pub const SYSTEM_OPERATORS_END: u32 = 80;

/// Number of system operators, beginning at `SYSTEM_OPERATORS_BEGIN`.
pub const NUM_SYSTEM_OPERATORS: usize =
    (SYSTEM_OPERATORS_END - SYSTEM_OPERATORS_BEGIN) as usize;

/// Represents a value which can produce debugging output and may contain
/// one or more interned `Name` values.
pub trait NameDebug {
    /// Writes the value's debug representation to the formatter stream.
    fn fmt(&self, names: &NameStore, f: &mut fmt::Formatter) -> fmt::Result;
}

/// Represents a value which can produce user-facing output and may contain
/// one or more interned `Name` values.
pub trait NameDisplay {
    /// Writes the value's display representation to the formatter stream.
    fn fmt(&self, names: &NameStore, f: &mut fmt::Formatter) -> fmt::Result;
}

/// Displays a `NameDebug` value using standard formatting.
#[derive(Copy, Clone)]
pub struct NameDebugger<'a, T: 'a>(&'a T, &'a NameStore);

/// Returns a `NameDebugger` wrapper around a value.
pub fn debug_names<'a, T: 'a>(names: &'a NameStore, t: &'a T) -> NameDebugger<'a, T> {
    NameDebugger(t, names)
}

impl<'a, T: NameDebug> fmt::Display for NameDebugger<'a, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.0.fmt(self.1, f)
    }
}

/// Displays a `NameDisplay` value using standard formatting.
#[derive(Copy, Clone)]
pub struct NameDisplayer<'a, T: 'a>(&'a T, &'a NameStore);

/// Returns a `NameDisplayer` wrapper around a value.
pub fn display_names<'a, T: 'a>(names: &'a NameStore, t: &'a T) -> NameDisplayer<'a, T> {
    NameDisplayer(t, names)
}

impl<'a, T: NameDisplay> fmt::Display for NameDisplayer<'a, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.0.fmt(self.1, f)
    }
}

impl NameDisplay for Box<StdError> {
    fn fmt(&self, _names: &NameStore, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

macro_rules! impl_box {
    ( $( $name:ident ),+ ) => {
        $(
            impl<T: ?Sized + NameDebug> NameDebug for $name<T> {
                fn fmt(&self, names: &NameStore, f: &mut fmt::Formatter) -> fmt::Result {
                    NameDebug::fmt(&**self, names, f)
                }
            }

            impl<T: ?Sized + NameDisplay> NameDisplay for $name<T> {
                fn fmt(&self, names: &NameStore, f: &mut fmt::Formatter) -> fmt::Result {
                    NameDisplay::fmt(&**self, names, f)
                }
            }
        )+
    }
}

impl_box!{ Box, Rc, Arc }

/// Converts module-local names loaded from bytecode files into global names
/// in a running interpreter.
#[derive(Clone, Debug)]
pub struct NameInputConversion {
    map: HashMap<u32, Name>,
    next_value: u32,
}

impl NameInputConversion {
    /// Creates a new `NameInputConversion` from a local-to-global mapping.
    pub fn new() -> NameInputConversion {
        NameInputConversion{
            map: HashMap::new(),
            next_value: NUM_STANDARD_NAMES,
        }
    }

    /// Returns the global name value for the given module-local value.
    pub fn get(&self, name: u32) -> Option<Name> {
        get_standard_name(name).or_else(|| self.map.get(&name).cloned())
    }

    /// Insert a global name value into the map.
    pub fn insert(&mut self, name: Name) {
        self.map.insert(self.next_value, name);
        self.next_value += 1;
    }
}

/// Converts global names in a running interpreter into module-local names,
/// retaining string representations, which can be written to a bytecode file.
#[derive(Clone, Debug)]
pub struct NameOutputConversion<'a> {
    /// Name strings, mapped to local name values
    names: Vec<&'a str>,
    map: HashMap<Name, u32>,
    store: &'a NameStore
}

impl<'a> NameOutputConversion<'a> {
    /// Creates a new `NameOutputConversion`, using the given `NameStore`
    /// to lookup global name values.
    pub fn new(store: &NameStore) -> NameOutputConversion {
        NameOutputConversion{
            names: Vec::new(),
            map: HashMap::new(),
            store: store,
        }
    }

    /// Adds a name to the collection and returns a module-local value.
    pub fn add(&mut self, name: Name) -> u32 {
        if is_standard_name(name) {
            name.0
        } else {
            let names = &mut self.names;
            let store = self.store;
            *self.map.entry(name).or_insert_with(|| {
                let name = store.get(name);
                let n = names.len();
                names.push(name);
                n as u32 + NUM_STANDARD_NAMES
            })
        }
    }

    /// Returns the collection of name string representations.
    pub fn names(&self) -> &[&'a str] {
        &self.names
    }

    /// Returns the number of names collected.
    pub fn len(&self) -> usize {
        self.names.len()
    }

    /// Returns whether any name was collected.
    pub fn is_empty(&self) -> bool {
        self.names.is_empty()
    }
}

/// Maps interned `Name` values to their `String` representations
#[derive(Clone, Debug)]
pub struct NameStore {
    /// Name string representation mapped to name values.
    names: Vec<String>,
}

impl NameStore {
    /// Constructs an empty `NameStore`.
    pub fn new() -> NameStore {
        NameStore{
            names: Vec::new(),
        }
    }

    /// Adds a name to the `NameStore` if it is not present.
    /// Returns a `Name` value to refer to the new or existing name.
    pub fn add(&mut self, name: &str) -> Name {
        if let Some(name) = get_standard_name_for(name) {
            name
        } else if let Some(pos) = self.names.iter().position(|n| n == name) {
            Name(pos as u32 + NUM_STANDARD_NAMES)
        } else {
            let n = self.names.len();
            self.names.push(name.to_owned());
            Name(n as u32 + NUM_STANDARD_NAMES)
        }
    }

    /// Returns the `Name` value of a given string, if it exists.
    pub fn get_name(&self, name: &str) -> Option<Name> {
        if let Some(pos) = self.names.iter().position(|n| n == name) {
            Some(Name(pos as u32 + NUM_STANDARD_NAMES))
        } else {
            None
        }
    }

    /// Returns the string representation of an interned name.
    pub fn get(&self, name: Name) -> &str {
        if name == Name::dummy() {
            "<dummy name>"
        } else {
            match standard_name(name) {
                Some(s) => s,
                None => &self.names[(name.0 - NUM_STANDARD_NAMES) as usize]
            }
        }
    }

    /// Iterates over all stored names.
    pub fn iter(&self) -> Iter<String> {
        self.names.iter()
    }
}

/// Maps names to values in a sorted `Vec`
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct NameMap<T> {
    values: Vec<(Name, T)>,
}

impl<T> NameMap<T> {
    /// Returns a new `NameMap`.
    pub fn new() -> NameMap<T> {
        NameMap{values: Vec::new()}
    }

    /// Lowers the map into a `NameMapSlice`, which may not receive new
    /// key-value pairs, but can overwrite existing values.
    pub fn into_slice(self) -> NameMapSlice<T> {
        NameMapSlice::new(self.values.into_boxed_slice())
    }

    /// Removes all values from the map.
    pub fn clear(&mut self) {
        self.values.clear();
    }

    /// Returns whether the map contains a value for the given name.
    pub fn contains_key(&self, name: Name) -> bool {
        self.values.binary_search_by(|&(ref n, _)| n.cmp(&name)).is_ok()
    }

    /// Returns the value corresponding to the given name.
    pub fn get(&self, name: Name) -> Option<&T> {
        self.values.binary_search_by(|&(ref n, _)| n.cmp(&name))
            .ok().map(|pos| &self.values[pos].1)
    }

    /// Returns a slice of the contained names and values.
    pub fn values(&self) -> &[(Name, T)] {
        &self.values
    }

    /// Returns whether the given map is empty.
    pub fn is_empty(&self) -> bool {
        self.values.is_empty()
    }

    /// Returns an iterator over names and values.
    pub fn iter(&self) -> Iter<(Name, T)> {
        self.values.iter()
    }

    /// Insert a name-value pair into the map.
    /// If a value was already present for the name, it is returned.
    pub fn insert(&mut self, name: Name, value: T) -> Option<T> {
        match self.values.binary_search_by(|&(ref n, _)| n.cmp(&name)) {
            Ok(pos) => {
                let old = replace(&mut self.values[pos].1, value);
                Some(old)
            }
            Err(pos) => {
                self.values.insert(pos, (name, value));
                None
            }
        }
    }

    /// Returns the number of name-value pairs contained in the map.
    pub fn len(&self) -> usize {
        self.values.len()
    }
}

impl<T> FromIterator<(Name, T)> for NameMap<T> {
    fn from_iter<I>(iterator: I) -> Self where I: IntoIterator<Item=(Name, T)> {
        let mut v = iterator.into_iter().collect::<Vec<_>>();
        v.sort_by(|a, b| a.0.cmp(&b.0));
        NameMap{values: v}
    }
}

impl<'a, T> IntoIterator for &'a NameMap<T> {
    type Item = &'a (Name, T);
    type IntoIter = Iter<'a, (Name, T)>;

    fn into_iter(self) -> Iter<'a, (Name, T)> {
        self.iter()
    }
}

/// Maps names to values in a sorted boxed slice.
///
/// Values may overwrite existing values, but new names cannot be inserted.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct NameMapSlice<T> {
    values: Box<[(Name, T)]>,
}

impl<T> NameMapSlice<T> {
    /// Creates a `NameMapSlice` wrapping the given boxed slice,
    /// which must already be sorted by name.
    fn new(values: Box<[(Name, T)]>) -> NameMapSlice<T> {
        NameMapSlice{values: values}
    }

    /// Returns whether the map contains a value for the given name.
    pub fn contains_key(&self, name: Name) -> bool {
        self.index(name).is_some()
    }

    /// Returns the index within the internal `Vec` of the given key.
    pub fn index(&self, name: Name) -> Option<usize> {
        self.values.binary_search_by(|&(n, _)| n.cmp(&name)).ok()
    }

    /// Returns the value corresponding to the given name.
    pub fn get(&self, name: Name) -> Option<&T> {
        self.values.binary_search_by(|&(n, _)| n.cmp(&name))
            .ok().map(|pos| &self.values[pos].1)
    }

    /// Returns a slice of the contained names and values.
    pub fn values(&self) -> &[(Name, T)] {
        &self.values
    }

    /// Overwrites the value for the given name.
    ///
    /// Returns `None` if the name does not exist in the mapping.
    /// When `None` is returned, no value will have been stored in the mapping.
    pub fn set(&mut self, name: Name, value: T) -> Option<T> {
        match self.values.binary_search_by(|&(n, _)| n.cmp(&name)) {
            Ok(n) => Some(replace(&mut self.values[n].1, value)),
            Err(_) => None
        }
    }

    /// Returns whether the given map is empty.
    pub fn is_empty(&self) -> bool {
        self.values.is_empty()
    }

    /// Returns an iterator over names and values.
    pub fn iter(&self) -> Iter<(Name, T)> {
        self.values.iter()
    }

    /// Elevates the map into `NameMap`, which may receive new key-value pairs.
    pub fn into_name_map(self) -> NameMap<T> {
        NameMap{values: self.values.into_vec()}
    }

    /// Returns the number of name-value pairs contained in the map.
    pub fn len(&self) -> usize {
        self.values.len()
    }
}

impl<T> FromIterator<(Name, T)> for NameMapSlice<T> {
    fn from_iter<I>(iterator: I) -> Self where I: IntoIterator<Item=(Name, T)> {
        iterator.into_iter().collect::<NameMap<_>>().into_slice()
    }
}

impl<'a, T> IntoIterator for &'a NameMapSlice<T> {
    type Item = &'a (Name, T);
    type IntoIter = Iter<'a, (Name, T)>;

    fn into_iter(self) -> Iter<'a, (Name, T)> {
        self.iter()
    }
}

/// Represents a set of names
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct NameSet {
    map: NameMap<()>,
}

impl NameSet {
    /// Returns a new `NameSet`.
    pub fn new() -> NameSet {
        NameSet{map: NameMap::new()}
    }

    /// Removes all names from the set.
    pub fn clear(&mut self) {
        self.map.clear();
    }

    /// Returns whether the set contains the given name.
    pub fn contains(&self, name: Name) -> bool {
        self.map.contains_key(name)
    }

    /// Inserts the given name into the set.
    /// Returns `true` if the name was not already contained.
    pub fn insert(&mut self, name: Name) -> bool {
        self.map.insert(name, ()).is_none()
    }

    /// Lowers the set into a `NameSetSlice`, which may not receive new name values.
    pub fn into_slice(self) -> NameSetSlice {
        NameSetSlice::new(self.map.into_slice())
    }

    /// Returns whether the set is empty.
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    /// Returns an iterator over the set of contained names.
    pub fn iter(&self) -> SetIter {
        SetIter(self.map.iter())
    }

    /// Returns the number of names contained in the set.
    pub fn len(&self) -> usize {
        self.map.len()
    }
}

impl FromIterator<Name> for NameSet {
    fn from_iter<I>(iterator: I) -> Self where I: IntoIterator<Item=Name> {
        NameSet{map: iterator.into_iter().map(|n| (n, ())).collect()}
    }
}

impl<'a> IntoIterator for &'a NameSet {
    type Item = Name;
    type IntoIter = SetIter<'a>;

    fn into_iter(self) -> SetIter<'a> {
        self.iter()
    }
}

/// Represents a set of names.
///
/// New names cannot be inserted into the set.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct NameSetSlice {
    map: NameMapSlice<()>,
}

impl NameSetSlice {
    /// Creates a `NameSetSlice` wrapping the given boxed slice,
    /// which must already be sorted.
    fn new(map: NameMapSlice<()>) -> NameSetSlice {
        NameSetSlice{map: map}
    }

    /// Returns whether the set contains the given name.
    pub fn contains(&self, name: Name) -> bool {
        self.map.contains_key(name)
    }

    /// Elevates the set into a `NameSet`, which may receive new name values.
    pub fn into_name_set(self) -> NameSet {
        NameSet{map: self.map.into_name_map()}
    }

    /// Returns whether the set is empty.
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    /// Returns an iterator over names in the set.
    pub fn iter(&self) -> SetIter {
        SetIter(self.map.iter())
    }

    /// Returns the number of names in the set.
    pub fn len(&self) -> usize {
        self.map.len()
    }
}

impl FromIterator<Name> for NameSetSlice {
    fn from_iter<I>(iterator: I) -> Self where I: IntoIterator<Item=Name> {
        iterator.into_iter().collect::<NameSet>().into_slice()
    }
}

impl<'a> IntoIterator for &'a NameSetSlice {
    type Item = Name;
    type IntoIter = SetIter<'a>;

    fn into_iter(self) -> SetIter<'a> {
        self.iter()
    }
}

/// Iterates over names in a `NameSet` or `NameSetSlice`.
pub struct SetIter<'a>(Iter<'a, (Name, ())>);

impl<'a> Iterator for SetIter<'a> {
    type Item = Name;

    #[inline]
    fn next(&mut self) -> Option<Name> {
        self.0.next().map(|&(n, _)| n)
    }
}
