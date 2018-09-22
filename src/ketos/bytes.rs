//! Implements a reference-counted byte string supporting efficient subslicing.

use std::cmp::Ordering;
use std::fmt;
use std::ops;
use std::slice::Iter;

use rc_vec::{RangeArgument, RcVec};

/// Shared byte string container
#[derive(Clone)]
pub struct Bytes(RcVec<u8>);

impl Bytes {
    /// Creates an empty byte string.
    pub fn new(v: Vec<u8>) -> Bytes {
        Bytes(RcVec::new(v))
    }

    /// Returns whether the byte string is empty.
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// Returns the number of bytes contained in the byte string.
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Returns a subslice of the byte string.
    pub fn slice<R: RangeArgument<usize>>(&self, range: R) -> Bytes {
        Bytes(self.0.slice(range))
    }

    /// Consumes the container and returns a `Vec<u8>`.
    pub fn into_bytes(self) -> Vec<u8> {
        self.0.into_vec()
    }

    /// Inserts a byte at the end of the byte string.
    pub fn push(&mut self, b: u8) {
        self.0.push(b);
    }
}

impl AsRef<[u8]> for Bytes {
    fn as_ref(&self) -> &[u8] {
        self.0.as_ref()
    }
}

impl ops::Deref for Bytes {
    type Target = [u8];

    fn deref(&self) -> &[u8] {
        self.0.deref()
    }
}

impl ops::DerefMut for Bytes {
    fn deref_mut(&mut self) -> &mut [u8] {
        self.0.deref_mut()
    }
}

impl fmt::Debug for Bytes {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl Extend<u8> for Bytes {
    fn extend<I>(&mut self, iterable: I) where I: IntoIterator<Item=u8> {
        self.0.extend(iterable);
    }
}

impl<'a> Extend<&'a u8> for Bytes {
    fn extend<I>(&mut self, iterable: I) where I: IntoIterator<Item=&'a u8> {
        self.0.extend(iterable);
    }
}

impl<'a> IntoIterator for &'a Bytes {
    type Item = &'a u8;
    type IntoIter = Iter<'a, u8>;

    fn into_iter(self) -> Iter<'a, u8> {
        self.0.into_iter()
    }
}

macro_rules! impl_eq_vec {
    ( $lhs:ty, $rhs:ty ) => {
        impl<'a> PartialEq<$rhs> for $lhs {
            fn eq(&self, rhs: &$rhs) -> bool { self[..] == rhs[..] }
        }
    }
}

macro_rules! impl_eq_array {
    ( $( $n:expr )+ ) => {
        $(
            impl PartialEq<[u8; $n]> for Bytes {
                fn eq(&self, rhs: &[u8; $n]) -> bool { self[..] == rhs[..] }
            }

            impl<'a> PartialEq<&'a [u8; $n]> for Bytes {
                fn eq(&self, rhs: &&'a [u8; $n]) -> bool { self[..] == rhs[..] }
            }
        )+
    }
}

impl_eq_vec!{ Bytes, Bytes }
impl_eq_vec!{ Bytes, Vec<u8> }
impl_eq_vec!{ Bytes, [u8] }
impl_eq_vec!{ Bytes, &'a [u8] }

impl_eq_array!{
    0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16
    17 18 19 20 21 22 23 24 25 26 27 28 29 30 31 32
}

impl Eq for Bytes {}

impl PartialOrd for Bytes {
    fn partial_cmp(&self, rhs: &Bytes) -> Option<Ordering> { self.0.partial_cmp(&rhs.0) }

    fn lt(&self, rhs: &Bytes) -> bool { self.0 < rhs.0 }
    fn le(&self, rhs: &Bytes) -> bool { self.0 <= rhs.0 }
    fn gt(&self, rhs: &Bytes) -> bool { self.0 > rhs.0 }
    fn ge(&self, rhs: &Bytes) -> bool { self.0 >= rhs.0 }
}

impl Ord for Bytes {
    fn cmp(&self, rhs: &Bytes) -> Ordering { self.0.cmp(&rhs.0) }
}

impl From<String> for Bytes {
    fn from(s: String) -> Bytes {
        Bytes(RcVec::new(s.into_bytes()))
    }
}

impl<'a> From<&'a str> for Bytes {
    fn from(s: &str) -> Bytes {
        Bytes::from(s.to_owned())
    }
}

impl From<Vec<u8>> for Bytes {
    fn from(b: Vec<u8>) -> Bytes {
        Bytes(RcVec::new(b))
    }
}

impl<'a> From<&'a [u8]> for Bytes {
    fn from(b: &[u8]) -> Bytes {
        Bytes(RcVec::new(b.to_vec()))
    }
}
