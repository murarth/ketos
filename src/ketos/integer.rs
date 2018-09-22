//! Arbitrary precision integer and ratio types.

use std::fmt;
use std::ops;
use std::str::FromStr;

pub use num::bigint::Sign;

use num::{self, BigInt, BigRational};
use num::{FromPrimitive, ToPrimitive, Integer as NumInteger, Signed, Num, Zero, One};

/// Arbitrary precision signed integer
#[derive(Clone, Debug, Default, Eq, PartialEq, Ord, PartialOrd)]
pub struct Integer(BigInt);

/// Arbitrary precision signed integer ratio
#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub struct Ratio(BigRational);

/// Error produced when failing to parse an `Integer` from `&str`.
#[derive(Debug, PartialEq)]
pub struct FromStrIntError(<BigInt as FromStr>::Err);

/// Error produced when failing to parse a `Ratio` from `&str`.
#[derive(Debug, PartialEq)]
pub struct FromStrRatioError(<BigRational as FromStr>::Err);

/// Error produced when failing to parse an `Integer` with radix from `&str`.
#[derive(Debug, PartialEq)]
pub struct FromStrRadixError(<BigInt as Num>::FromStrRadixErr);

impl fmt::Display for FromStrIntError {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(&self.0, f)
    }
}

impl fmt::Display for FromStrRatioError {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(&self.0, f)
    }
}

impl fmt::Display for FromStrRadixError {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(&self.0, f)
    }
}

impl Integer {
    /// Returns the number of bits required to represent the `Integer`.
    #[inline]
    pub fn bits(&self) -> usize {
        self.0.bits()
    }

    /// Creates an `Integer` from a sign and a series of big-endian bytes.
    #[inline]
    pub fn from_bytes_be(sign: Sign, bytes: &[u8]) -> Integer {
        Integer(BigInt::from_bytes_be(sign, bytes))
    }

    /// Creates an `Integer` from a sign and a series of little-endian bytes.
    #[inline]
    pub fn from_bytes_le(sign: Sign, bytes: &[u8]) -> Integer {
        Integer(BigInt::from_bytes_le(sign, bytes))
    }

    /// Creates an `Integer` with the value of the given `f64`.
    /// Returns `None` if the value cannot be converted.
    #[inline]
    pub fn from_f64(f: f64) -> Option<Integer> {
        BigInt::from_f64(f).map(Integer)
    }

    /// Creates an `Integer` with the value of the given `i8`.
    #[inline]
    pub fn from_i8(i: i8) -> Integer {
        Integer(BigInt::from_i8(i).unwrap())
    }

    /// Creates an `Integer` with the value of the given `i16`.
    #[inline]
    pub fn from_i16(i: i16) -> Integer {
        Integer(BigInt::from_i16(i).unwrap())
    }

    /// Creates an `Integer` with the value of the given `i32`.
    #[inline]
    pub fn from_i32(i: i32) -> Integer {
        Integer(BigInt::from_i32(i).unwrap())
    }

    /// Creates an `Integer` with the value of the given `i64`.
    #[inline]
    pub fn from_i64(i: i64) -> Integer {
        Integer(BigInt::from_i64(i).unwrap())
    }

    /// Creates an `Integer` with the value of the given `isize`.
    #[inline]
    pub fn from_isize(i: isize) -> Integer {
        Integer(BigInt::from_isize(i).unwrap())
    }

    /// Creates an `Integer` with the value of the given `u8`.
    #[inline]
    pub fn from_u8(i: u8) -> Integer {
        Integer(BigInt::from_u8(i).unwrap())
    }

    /// Creates an `Integer` with the value of the given `u16`.
    #[inline]
    pub fn from_u16(i: u16) -> Integer {
        Integer(BigInt::from_u16(i).unwrap())
    }

    /// Creates an `Integer` with the value of the given `u32`.
    #[inline]
    pub fn from_u32(i: u32) -> Integer {
        Integer(BigInt::from_u32(i).unwrap())
    }

    /// Creates an `Integer` with the value of the given `u64`.
    #[inline]
    pub fn from_u64(i: u64) -> Integer {
        Integer(BigInt::from_u64(i).unwrap())
    }

    /// Creates an `Integer` with the value of the given `usize`.
    #[inline]
    pub fn from_usize(u: usize) -> Integer {
        Integer(BigInt::from_usize(u).unwrap())
    }

    /// Returns an `Integer` represented by a string in the given radix.
    /// `radix` must be in the range `[2, 36]`.
    #[inline]
    pub fn from_str_radix(s: &str, radix: u32) -> Result<Integer, FromStrRadixError> {
        BigInt::from_str_radix(s, radix)
            .map(Integer).map_err(FromStrRadixError)
    }

    /// Returns integer sign and a series of big-endian bytes.
    #[inline]
    pub fn to_bytes_be(&self) -> (Sign, Vec<u8>) {
        self.0.to_bytes_be()
    }

    /// Returns integer sign and a series of little-endian bytes.
    #[inline]
    pub fn to_bytes_le(&self) -> (Sign, Vec<u8>) {
        self.0.to_bytes_le()
    }

    /// Returns a string representation of the `Integer` in the given radix.
    /// `radix` must be in the range `[2, 36]`.
    pub fn to_str_radix(&self, radix: u32) -> String {
        self.0.to_str_radix(radix)
    }

    /// Returns the `Integer` as an `i8` value.
    #[inline]
    pub fn to_i8(&self) -> Option<i8> {
        self.0.to_i8()
    }

    /// Returns the `Integer` as an `i16` value.
    #[inline]
    pub fn to_i16(&self) -> Option<i16> {
        self.0.to_i16()
    }

    /// Returns the `Integer` as an `i32` value.
    #[inline]
    pub fn to_i32(&self) -> Option<i32> {
        self.0.to_i32()
    }

    /// Returns the `Integer` as an `i64` value.
    #[inline]
    pub fn to_i64(&self) -> Option<i64> {
        self.0.to_i64()
    }

    /// Returns the `Integer` as an `isize` value.
    #[inline]
    pub fn to_isize(&self) -> Option<isize> {
        self.0.to_isize()
    }

    /// Returns the `Integer` as an `u8` value.
    #[inline]
    pub fn to_u8(&self) -> Option<u8> {
        self.0.to_u8()
    }

    /// Returns the `Integer` as an `u16` value.
    #[inline]
    pub fn to_u16(&self) -> Option<u16> {
        self.0.to_u16()
    }

    /// Returns the `Integer` as an `u32` value.
    #[inline]
    pub fn to_u32(&self) -> Option<u32> {
        self.0.to_u32()
    }

    /// Returns the `Integer` as an `u64` value.
    #[inline]
    pub fn to_u64(&self) -> Option<u64> {
        self.0.to_u64()
    }

    /// Returns the `Integer` as an `usize` value.
    #[inline]
    pub fn to_usize(&self) -> Option<usize> {
        self.0.to_usize()
    }

    /// Returns the `Integer` as an `f32` value.
    #[inline]
    pub fn to_f32(&self) -> Option<f32> {
        self.0.to_f32()
    }

    /// Returns the `Integer` as an `f64` value.
    #[inline]
    pub fn to_f64(&self) -> Option<f64> {
        self.0.to_f64()
    }

    /// Raises the value to the power of `exp`.
    #[inline]
    pub fn pow(self, exp: usize) -> Integer {
        Integer(num::pow(self.0, exp))
    }

    /// Returns the absolute value of an `Integer`.
    #[inline]
    pub fn abs(&self) -> Integer {
        Integer(self.0.abs())
    }

    /// Returns whether `self` is a multiple of `rhs`.
    #[inline]
    pub fn is_multiple_of(&self, rhs: &Integer) -> bool {
        self.0.is_multiple_of(&rhs.0)
    }

    /// Returns whether the `Integer` is less than zero.
    #[inline]
    pub fn is_negative(&self) -> bool {
        self.0.is_negative()
    }

    /// Returns whether the `Integer` is greater than zero.
    #[inline]
    pub fn is_positive(&self) -> bool {
        self.0.is_positive()
    }

    /// Returns whether the `Integer` is equal to zero.
    #[inline]
    pub fn is_zero(&self) -> bool {
        self.0.is_zero()
    }

    /// Returns an `Integer` of the value zero.
    #[inline]
    pub fn zero() -> Integer {
        Integer(BigInt::zero())
    }

    /// Returns whether the `Integer` is equal to one.
    #[inline]
    pub fn is_one(&self) -> bool {
        self.to_u32() == Some(1)
    }

    /// Returns an `Integer` of the value one.
    #[inline]
    pub fn one() -> Integer {
        Integer(BigInt::one())
    }

    fn from_bigint_ref(i: &BigInt) -> &Integer {
        unsafe { &*(i as *const _ as *const Integer) }
    }
}

impl Ratio {
    /// Constructs a `Ratio` from numerator and denominator.
    ///
    /// # Panics
    ///
    /// Panics if `denom` is zero.
    #[inline]
    pub fn new(numer: Integer, denom: Integer) -> Ratio {
        Ratio(BigRational::new(numer.0, denom.0))
    }

    /// Creates a `Ratio` with the value of the given `f32`.
    /// Returns `None` if the value cannot be converted.
    #[inline]
    pub fn from_f32(f: f32) -> Option<Ratio> {
        BigRational::from_float(f).map(Ratio)
    }

    /// Creates a `Ratio` with the value of the given `f64`.
    /// Returns `None` if the value cannot be converted.
    #[inline]
    pub fn from_f64(f: f64) -> Option<Ratio> {
        BigRational::from_float(f).map(Ratio)
    }

    /// Creates a `Ratio` from an `Integer` value.
    #[inline]
    pub fn from_integer(i: Integer) -> Ratio {
        Ratio(BigRational::from_integer(i.0))
    }

    /// Returns the `Ratio` as an `f32` value.
    #[inline]
    pub fn to_f32(&self) -> Option<f32> {
        self.numer().to_f32().and_then(
            |n| self.denom().to_f32().map(|d| n / d))
    }

    /// Returns the `Ratio` as an `f64` value.
    #[inline]
    pub fn to_f64(&self) -> Option<f64> {
        self.numer().to_f64().and_then(
            |n| self.denom().to_f64().map(|d| n / d))
    }

    /// Truncates a `Ratio` and returns the whole portion as an `Integer`.
    #[inline]
    pub fn to_integer(&self) -> Integer {
        Integer(self.0.to_integer())
    }

    /// Returns whether the `Ratio` is an integer; i.e. its denominator is `1`.
    #[inline]
    pub fn is_integer(&self) -> bool {
        self.denom().is_one()
    }

    /// Returns the absolute value of the `Ratio`.
    #[inline]
    pub fn abs(&self) -> Ratio {
        Ratio(self.0.abs())
    }

    /// Returns the `Ratio` rounded towards positive infinity.
    #[inline]
    pub fn ceil(&self) -> Ratio {
        Ratio(self.0.ceil())
    }

    /// Returns the `Ratio` rounded towards negative infinity.
    #[inline]
    pub fn floor(&self) -> Ratio {
        Ratio(self.0.floor())
    }

    /// Returns the fractional portion of a `Ratio`.
    #[inline]
    pub fn fract(&self) -> Ratio {
        Ratio(self.0.fract())
    }

    /// Returns the `Ratio` rounded to the nearest integer.
    /// Rounds half-way cases away from zero.
    #[inline]
    pub fn round(&self) -> Ratio {
        Ratio(self.0.round())
    }

    /// Returns the `Ratio` rounded towards zero.
    #[inline]
    pub fn trunc(&self) -> Ratio {
        Ratio(self.0.trunc())
    }

    /// Returns the reciprocal of a `Ratio`.
    ///
    /// # Panics
    ///
    /// Panics if the numerator is zero.
    #[inline]
    pub fn recip(&self) -> Ratio {
        Ratio(self.0.recip())
    }

    /// Returns the `Ratio`'s numerator.
    #[inline]
    pub fn numer(&self) -> &Integer {
        Integer::from_bigint_ref(self.0.numer())
    }

    /// Returns the `Ratio`'s denominator.
    #[inline]
    pub fn denom(&self) -> &Integer {
        Integer::from_bigint_ref(self.0.denom())
    }

    /// Returns whether the `Ratio` is equal to zero.
    pub fn is_zero(&self) -> bool {
        self.numer().is_zero()
    }

    /// Returns whether the `Ratio` is less than zero.
    pub fn is_negative(&self) -> bool {
        self.numer().is_negative()
    }

    /// Returns whether the `Ratio` is greater than zero.
    pub fn is_positive(&self) -> bool {
        self.numer().is_positive()
    }

    /// Returns a `Ratio` of value zero.
    pub fn zero() -> Ratio {
        Ratio(BigRational::zero())
    }

    /// Returns a `Ratio` of value one.
    pub fn one() -> Ratio {
        Ratio(BigRational::one())
    }
}

impl PartialEq<Integer> for Ratio {
    fn eq(&self, rhs: &Integer) -> bool {
        self.denom().is_one() && self.numer() == rhs
    }
}

impl PartialEq<Ratio> for Integer {
    fn eq(&self, rhs: &Ratio) -> bool { rhs == self }
}

impl fmt::Display for Integer {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(&self.0, f)
    }
}

impl FromStr for Integer {
    type Err = FromStrIntError;

    #[inline]
    fn from_str(s: &str) -> Result<Integer, FromStrIntError> {
        s.parse().map(Integer).map_err(FromStrIntError)
    }
}

impl ops::Shl<usize> for Integer {
    type Output = Integer;

    #[inline]
    fn shl(self, rhs: usize) -> Integer {
        Integer(self.0.shl(rhs))
    }
}

impl<'a> ops::Shl<usize> for &'a Integer {
    type Output = Integer;

    #[inline]
    fn shl(self, rhs: usize) -> Integer {
        Integer(self.0.clone().shl(rhs))
    }
}

impl ops::Shr<usize> for Integer {
    type Output = Integer;

    #[inline]
    fn shr(self, rhs: usize) -> Integer {
        Integer(self.0.shr(rhs))
    }
}

impl<'a> ops::Shr<usize> for &'a Integer {
    type Output = Integer;

    #[inline]
    fn shr(self, rhs: usize) -> Integer {
        Integer(self.0.clone().shr(rhs))
    }
}

macro_rules! impl_un_op {
    ( $ty:ident , $trait:ident , $meth:ident ) => {
        impl ::std::ops::$trait for $ty {
            type Output = $ty;

            #[inline]
            fn $meth(self) -> $ty {
                $ty((self.0).$meth())
            }
        }

        impl<'a> ::std::ops::$trait for &'a $ty {
            type Output = $ty;

            #[inline]
            fn $meth(self) -> $ty {
                $ty((&self.0).$meth())
            }
        }
    }
}

macro_rules! impl_bin_op {
    ( $ty:ident , $trait:ident , $meth:ident ) => {
        impl ::std::ops::$trait<$ty> for $ty {
            type Output = $ty;

            #[inline]
            fn $meth(self, rhs: $ty) -> $ty {
                $ty((self.0).$meth(rhs.0))
            }
        }

        impl<'a> ::std::ops::$trait<&'a $ty> for $ty {
            type Output = $ty;

            #[inline]
            fn $meth(self, rhs: &$ty) -> $ty {
                $ty((self.0).$meth(&rhs.0))
            }
        }

        impl<'a> ::std::ops::$trait<$ty> for &'a $ty {
            type Output = $ty;

            #[inline]
            fn $meth(self, rhs: $ty) -> $ty {
                $ty((&self.0).$meth(rhs.0))
            }
        }

        impl<'a, 'b> ::std::ops::$trait<&'b $ty> for &'a $ty {
            type Output = $ty;

            #[inline]
            fn $meth(self, rhs: &$ty) -> $ty {
                $ty((&self.0).$meth(&rhs.0))
            }
        }
    }
}

macro_rules! impl_assign_op {
    ( $ty:ident , $trait:ident , $meth:ident ) => {
        impl ::std::ops::$trait<$ty> for $ty {
            #[inline]
            fn $meth(&mut self, rhs: $ty) {
                (self.0).$meth(rhs.0);
            }
        }

        impl<'a> ::std::ops::$trait<&'a $ty> for $ty {
            #[inline]
            fn $meth(&mut self, rhs: &$ty) {
                (self.0).$meth(&rhs.0);
            }
        }
    }
}

macro_rules! impl_ops {
    ( $ty:ident ) => {
        impl_bin_op!{ $ty, Add, add }
        impl_bin_op!{ $ty, Sub, sub }
        impl_bin_op!{ $ty, Mul, mul }
        impl_bin_op!{ $ty, Div, div }
        impl_bin_op!{ $ty, Rem, rem }

        impl_assign_op!{ $ty, AddAssign, add_assign }
        impl_assign_op!{ $ty, SubAssign, sub_assign }
        impl_assign_op!{ $ty, MulAssign, mul_assign }
        impl_assign_op!{ $ty, DivAssign, div_assign }
        impl_assign_op!{ $ty, RemAssign, rem_assign }

        impl_un_op!{ $ty, Neg, neg }

        impl ::num::Zero for $ty {
            #[inline]
            fn is_zero(&self) -> bool { self.0.is_zero() }
            #[inline]
            fn zero() -> $ty { $ty(Zero::zero()) }
        }
    }
}

macro_rules! impl_integer_ops {
    ( $ty:ident ) => {
        impl_ops!{ $ty }

        impl_bin_op!{ $ty, BitAnd, bitand }
        impl_bin_op!{ $ty, BitOr,  bitor }
        impl_bin_op!{ $ty, BitXor, bitxor }

        impl_assign_op!{ $ty, BitAndAssign, bitand_assign }
        impl_assign_op!{ $ty, BitOrAssign,  bitor_assign }
        impl_assign_op!{ $ty, BitXorAssign, bitxor_assign }

        impl_un_op!{ $ty, Not, not }
    }
}

impl_integer_ops!{Integer}
impl_ops!{Ratio}

impl fmt::Display for Ratio {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(&self.0, f)
    }
}

impl FromStr for Ratio {
    type Err = FromStrRatioError;

    #[inline]
    fn from_str(s: &str) -> Result<Ratio, FromStrRatioError> {
        s.parse().map(Ratio).map_err(FromStrRatioError)
    }
}
