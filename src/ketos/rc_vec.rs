//! Implements a reference-counted `Vec` supporting efficient subslicing.

use std::borrow::Cow;
use std::cmp::Ordering;
use std::ffi::OsStr;
use std::fmt;
use std::ops;
use std::path::Path;
use std::rc::Rc;
use std::slice::Iter;

// A duplicate of `collections::range::RangeArgument`, which is unstable.
/// Argument for functions accepting a range
pub trait RangeArgument<T> {
    /// Returns start value
    fn start(&self) -> Option<&T> { None }
    /// Returns end value
    fn end(&self) -> Option<&T> { None }
}

impl<T> RangeArgument<T> for ops::RangeFull {}
impl<T> RangeArgument<T> for ops::Range<T> {
    fn start(&self) -> Option<&T> { Some(&self.start) }
    fn end(&self) -> Option<&T> { Some(&self.end) }
}
impl<T> RangeArgument<T> for ops::RangeFrom<T> {
    fn start(&self) -> Option<&T> { Some(&self.start) }
}
impl<T> RangeArgument<T> for ops::RangeTo<T> {
    fn end(&self) -> Option<&T> { Some(&self.end) }
}

/// Represents a reference-counted view into a `String`.
/// Subslices may be created which will share the underlying data buffer.
#[derive(Clone)]
pub struct RcString {
    data: Rc<String>,
    start: usize,
    end: usize,
}

impl RcString {
    /// Constructs a new `RcString` from a `String`.
    pub fn new(data: String) -> RcString {
        let n = data.len();

        RcString{
            data: Rc::new(data),
            start: 0,
            end: n,
        }
    }

    /// Returns whether the visible slice is empty.
    pub fn is_empty(&self) -> bool {
        self.start == self.end
    }

    /// Returns the length of the visible slice.
    pub fn len(&self) -> usize {
        self.end - self.start
    }

    /// Returns a subslice of the `RcString`.
    pub fn slice<R: RangeArgument<usize>>(&self, range: R) -> RcString {
        let start = range.start().map_or(0, |v| *v);
        let end = range.end().map_or(self.len(), |v| *v);

        let a = self.start + start;
        let b = self.start + end;

        if a > self.end {
            panic!("RcString slice out of bounds; start is {} but length is {}",
                start, self.len());
        }

        if b > self.end {
            panic!("RcString slice out of bounds; end is {} but length is {}",
                end, self.len());
        }

        if !self.data.is_char_boundary(a) || !self.data.is_char_boundary(b) {
            panic!("index {} and/or {} in RcString `{}` do not lie on \
                character boundary", a, b, &self[..]);
        }

        RcString{
            data: self.data.clone(),
            start: a,
            end: b,
        }
    }

    /// Consumes the `RcString` and returns a `String`.
    pub fn into_string(self) -> String {
        match Rc::try_unwrap(self.data) {
            Ok(mut s) => {
                let _ = s.drain(self.end..);
                let _ = s.drain(..self.start);
                s
            }
            Err(data) => data[self.start..self.end].to_owned()
        }
    }

    /// Pushes a `char` to the end of the contained `String`.
    pub fn push(&mut self, ch: char) {
        self.make_mut().push(ch);
        self.end += ch.len_utf8();
    }

    /// Pushes a `&str` to the end of the contained `String`.
    pub fn push_str(&mut self, s: &str) {
        self.make_mut().push_str(s);
        self.end += s.len();
    }

    fn make_mut(&mut self) -> &mut String {
        let s = Rc::make_mut(&mut self.data);

        let _ = s.drain(self.end..);
        let _ = s.drain(..self.start);
        let n = s.len();

        self.start = 0;
        self.end = n;

        s
    }
}

impl AsRef<str> for RcString {
    fn as_ref(&self) -> &str {
        &self.data[self.start..self.end]
    }
}

impl AsRef<[u8]> for RcString {
    fn as_ref(&self) -> &[u8] {
        AsRef::<str>::as_ref(self).as_ref()
    }
}

impl AsRef<Path> for RcString {
    fn as_ref(&self) -> &Path {
        AsRef::<str>::as_ref(self).as_ref()
    }
}

impl AsRef<OsStr> for RcString {
    fn as_ref(&self) -> &OsStr {
        AsRef::<str>::as_ref(self).as_ref()
    }
}

impl ops::Deref for RcString {
    type Target = str;

    fn deref(&self) -> &str {
        self.as_ref()
    }
}

impl ops::DerefMut for RcString {
    fn deref_mut(&mut self) -> &mut str {
        self.make_mut()
    }
}

impl fmt::Debug for RcString {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(&self[..], f)
    }
}

impl fmt::Display for RcString {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(&self[..], f)
    }
}

macro_rules! impl_eq_str {
    ( $lhs:ty, $rhs:ty ) => {
        impl<'a> PartialEq<$rhs> for $lhs {
            fn eq(&self, rhs: &$rhs) -> bool { self[..] == rhs[..] }
        }
    }
}

impl_eq_str!{ RcString, RcString }
impl_eq_str!{ RcString, String }
impl_eq_str!{ RcString, str }
impl_eq_str!{ RcString, &'a str }
impl_eq_str!{ RcString, Cow<'a, str> }

impl Eq for RcString {}

impl PartialOrd for RcString {
    fn partial_cmp(&self, rhs: &RcString) -> Option<Ordering> { self[..].partial_cmp(&rhs[..]) }

    fn lt(&self, rhs: &RcString) -> bool { self[..] < rhs[..] }
    fn le(&self, rhs: &RcString) -> bool { self[..] <= rhs[..] }
    fn gt(&self, rhs: &RcString) -> bool { self[..] > rhs[..] }
    fn ge(&self, rhs: &RcString) -> bool { self[..] >= rhs[..] }
}

impl Ord for RcString {
    fn cmp(&self, rhs: &RcString) -> Ordering { self[..].cmp(&rhs[..]) }
}

impl<'a> From<&'a str> for RcString {
    fn from(s: &str) -> RcString {
        RcString::new(s.to_owned())
    }
}

impl From<String> for RcString {
    fn from(s: String) -> RcString {
        RcString::new(s)
    }
}

/// Represents a reference-counted view into a `Vec`.
/// Subslices may be created which will share the underlying data buffer.
#[derive(Clone)]
pub struct RcVec<T> {
    data: Rc<Vec<T>>,
    start: usize,
    end: usize,
}

impl<T> RcVec<T> {
    /// Constructs a new `RcVec` from a `Vec`.
    pub fn new(data: Vec<T>) -> RcVec<T> {
        let n = data.len();

        RcVec{
            data: Rc::new(data),
            start: 0,
            end: n,
        }
    }

    /// Returns whether the `RcVec` is empty.
    pub fn is_empty(&self) -> bool {
        self.start == self.end
    }

    /// Returns the number of elements visible to the `RcVec`.
    pub fn len(&self) -> usize {
        self.end - self.start
    }

    /// Returns a subslice of the `RcVec`, with the range being relative
    /// to this slice's boundaries.
    pub fn slice<R: RangeArgument<usize>>(&self, range: R) -> RcVec<T> {
        let start = range.start().map_or(0, |v| *v);
        let end = range.end().map_or(self.len(), |v| *v);

        let a = self.start + start;
        let b = self.start + end;

        if a > self.end {
            panic!("RcVec slice out of bounds; start is {} but length is {}",
                start, self.len());
        }

        if b > self.end {
            panic!("RcVec slice out of bounds; end is {} but length is {}",
                end, self.len());
        }

        RcVec{
            data: self.data.clone(),
            start: a,
            end: b,
        }
    }
}

impl<T: Clone> RcVec<T> {
    /// Consumes the `RcVec` and returns the contained `Vec`.
    /// This will clone the contained values unless the data was uniquely held.
    pub fn into_vec(self) -> Vec<T> {
        match Rc::try_unwrap(self.data) {
            Ok(mut v) => {
                let _ = v.drain(self.end..);
                let _ = v.drain(..self.start);
                v
            }
            Err(data) => data[self.start..self.end].to_vec()
        }
    }

    /// Makes wrapped data unique and returns a mutable reference,
    /// after adjusting `start` and `end` fields.
    ///
    /// # Note
    ///
    /// If the length of the `Vec` is modified, the `end` field of `RcVec`
    /// must be adjusted manually. That's why this method is private.
    fn make_mut(&mut self) -> &mut Vec<T> {
        let v = Rc::make_mut(&mut self.data);

        let _ = v.drain(self.end..);
        let _ = v.drain(..self.start);
        let n = v.len();

        self.start = 0;
        self.end = n;

        v
    }

    /// Pushes a value into the contained `Vec`.
    pub fn push(&mut self, t: T) {
        self.make_mut().push(t);
        self.end += 1;
    }
}

impl<T> AsRef<[T]> for RcVec<T> {
    fn as_ref(&self) -> &[T] {
        &self.data[self.start..self.end]
    }
}

impl<T> ops::Deref for RcVec<T> {
    type Target = [T];

    fn deref(&self) -> &[T] {
        self.as_ref()
    }
}

impl<T: Clone> ops::DerefMut for RcVec<T> {
    fn deref_mut(&mut self) -> &mut [T] {
        self.make_mut()
    }
}

impl<T: fmt::Debug> fmt::Debug for RcVec<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(&self[..], f)
    }
}

impl<T: Clone> Extend<T> for RcVec<T> {
    fn extend<I>(&mut self, iterable: I) where I: IntoIterator<Item=T> {
        self.make_mut().extend(iterable);
        self.end = self.data.len();
    }
}

impl<'a, T: Clone> Extend<&'a T> for RcVec<T> where T: Copy + 'a {
    fn extend<I>(&mut self, iterable: I) where I: IntoIterator<Item=&'a T> {
        self.make_mut().extend(iterable);
        self.end = self.data.len();
    }
}

impl<'a, T> IntoIterator for &'a RcVec<T> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Iter<'a, T> {
        self.iter()
    }
}

macro_rules! impl_eq_vec {
    ( $lhs:ty, $rhs:ty ) => {
        impl<'a, A, B> PartialEq<$rhs> for $lhs where A: PartialEq<B> {
            fn eq(&self, rhs: &$rhs) -> bool { self[..] == rhs[..] }
        }
    }
}

macro_rules! impl_eq_array {
    ( $( $n:expr )+ ) => {
        $(
            impl<A, B> PartialEq<[B; $n]> for RcVec<A> where A: PartialEq<B> {
                fn eq(&self, rhs: &[B; $n]) -> bool { self[..] == rhs[..] }
            }

            impl<'a, A, B> PartialEq<&'a [B; $n]> for RcVec<A> where A: PartialEq<B> {
                fn eq(&self, rhs: &&'a [B; $n]) -> bool { self[..] == rhs[..] }
            }
        )+
    }
}

impl_eq_vec!{ RcVec<A>, RcVec<B> }
impl_eq_vec!{ RcVec<A>, Vec<B> }
impl_eq_vec!{ RcVec<A>, [B] }
impl_eq_vec!{ RcVec<A>, &'a [B] }

impl_eq_array!{
    0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16
    17 18 19 20 21 22 23 24 25 26 27 28 29 30 31 32
}

impl<T: Eq> Eq for RcVec<T> {}

impl<T: PartialOrd> PartialOrd for RcVec<T> {
    fn partial_cmp(&self, rhs: &RcVec<T>) -> Option<Ordering> { self[..].partial_cmp(&rhs[..]) }

    fn lt(&self, rhs: &RcVec<T>) -> bool { self[..] < rhs[..] }
    fn le(&self, rhs: &RcVec<T>) -> bool { self[..] <= rhs[..] }
    fn gt(&self, rhs: &RcVec<T>) -> bool { self[..] > rhs[..] }
    fn ge(&self, rhs: &RcVec<T>) -> bool { self[..] >= rhs[..] }
}

impl<T: Ord> Ord for RcVec<T> {
    fn cmp(&self, rhs: &RcVec<T>) -> Ordering { self[..].cmp(&rhs[..]) }
}

impl<T> From<Vec<T>> for RcVec<T> {
    fn from(v: Vec<T>) -> RcVec<T> {
        RcVec::new(v)
    }
}

#[cfg(test)]
mod test {
    use super::{RcString, RcVec};

    #[test]
    fn test_rc_string() {
        let a = RcString::from("foobar");
        let mut b = a.slice(1..4);
        let mut c = a.clone();

        assert_eq!(a.data.as_ptr(), b.data.as_ptr());
        assert_eq!(a, "foobar");
        assert_eq!(b, "oob");
        assert_eq!(b.is_empty(), false);
        assert_eq!(b.len(), 3);

        b.push('x');
        assert_eq!(b, "oobx");

        c.push_str("lol");
        assert_eq!(c.into_string(), "foobarlol");
    }

    #[test]
    #[should_panic]
    fn test_rc_string_error() {
        let a = RcString::from("foo\u{2022}");
        let _b = a.slice(2..4);
    }

    #[test]
    fn test_rc_vec() {
        let a = RcVec::new(vec![1, 2, 3]);
        let mut b = a.slice(1..3);
        let mut c = a.clone();

        assert_eq!(a.data.as_ptr(), b.data.as_ptr());
        assert_eq!(a, [1, 2, 3]);
        assert_eq!(b, [2, 3]);
        assert_eq!(b.is_empty(), false);
        assert_eq!(b.len(), 2);

        b.push(4);
        assert_eq!(b, [2, 3, 4]);

        c.extend(&[4, 5, 6]);
        assert_eq!(c.into_vec(), [1, 2, 3, 4, 5, 6]);
    }
}
