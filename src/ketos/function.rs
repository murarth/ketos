//! Contains implementations of core system functions.

use std::borrow::Cow::{self, Borrowed, Owned};
use std::cmp::{max, Ordering};
use std::f64;
use std::fmt;
use std::path::{Path, PathBuf};
use std::rc::Rc;

use num::{Float, Zero};

use bytecode::Code;
use bytes::Bytes;
use error::Error;
use exec::{Context, ExecError};
use integer::{Integer, Ratio};
use name::{Name, NUM_SYSTEM_FNS};
use restrict::RestrictError;
use scope::{Scope, WeakScope};
use string_fmt::format_string;
use structs::StructDef;
use value::{FromValueRef, Value};

use self::Arity::*;

/// Represents a system function
#[derive(Copy)]
pub struct SystemFn {
    /// Function arity
    pub arity: Arity,
    /// Function implementation
    pub callback: FunctionImpl,
    /// Function documentation
    pub doc: Option<&'static str>,
}

impl Clone for SystemFn {
    fn clone(&self) -> Self { *self }
}

impl PartialEq for SystemFn {
    fn eq(&self, rhs: &SystemFn) -> bool {
        self.callback as *const () == rhs.callback as *const ()
    }
}

/// `SystemFn` implemented by Rust function
pub type FunctionImpl = fn(&Context, &mut [Value]) -> Result<Value, Error>;

macro_rules! sys_fn {
    ( $callback:path , $arity:expr , $doc:expr ) => {
        SystemFn{arity: $arity, callback: $callback, doc: Some($doc)}
    };
}

/// System function implementations.
///
/// These names must correspond exactly to the first `NUM_SYSTEM_FNS`
/// standard names defined in `name.rs`.
pub static SYSTEM_FNS: [SystemFn; NUM_SYSTEM_FNS] = [
    sys_fn!(fn_add,         Min(0),
"Returns the sum of all arguments.

Given no arguments, returns the additive identity, `0`."),
    sys_fn!(fn_sub,         Min(1),
"Returns the cumulative difference between successive arguments."),
    sys_fn!(fn_mul,         Min(0),
"Returns the product of all arguments.

Given no arguments, returns the multiplicative identity, `1`."),
    sys_fn!(fn_pow,         Exact(2),
"Returns a base value raised to an exponent."),
    sys_fn!(fn_div,         Min(1),
"Returns the cumulative quotient of successive arguments."),
    sys_fn!(fn_floor_div,   Min(1),
"Returns the cumulative quotient of successive arguments,
rounded toward negative infinity."),
    sys_fn!(fn_rem,         Exact(2),
"Returns the remainder of two arguments."),
    sys_fn!(fn_shl,         Exact(2),
"Returns an integer, bit shifted left by a given number."),
    sys_fn!(fn_shr,         Exact(2),
"Returns an integer, bit shifted right by a given number."),
    sys_fn!(fn_bit_and,     Min(0),
"Returns the cumulative bitwise AND of all arguments.

Given no arguments, returns the bitwise AND identity, `-1`."),
    sys_fn!(fn_bit_or,      Min(0),
"Returns the cumulative bitwise OR of all arguments.

Given no arguments, returns the bitwise OR identity, `0`."),
    sys_fn!(fn_bit_xor,     Min(0),
"Returns the cumulative bitwise XOR of all arguments.

Given no arguments, returns the bitwise XOR identity, `0`."),
    sys_fn!(fn_bit_not,     Exact(1),
"Returns an integer, the result of a bitwise NOT operation."),
    sys_fn!(fn_eq,          Min(2),
"Returns whether the given arguments compare equal to one another.

Values of different types may not be compared. Attempts to do so will
result in an error."),
    sys_fn!(fn_ne,          Min(2),
"Returns whether each given argument differs in value from each other argument.

Values of different types may not be compared. Attempts to do so will
result in an error."),
    sys_fn!(fn_weak_eq,     Min(2),
"Returns whether the given arguments compare equal to one another.

Comparing values of different types will yield `false`."),
    sys_fn!(fn_weak_ne,     Min(2),
"Returns whether the given arguments compare not equal to one another.

Comparing values of different types will yield `true`."),
    sys_fn!(fn_lt,          Min(2),
"Returns whether each argument compares less than each successive argument.

Values of different types may not be compared. Attempts to do so will
result in an error."),
    sys_fn!(fn_gt,          Min(2),
"Returns whether each argument compares greater than each successive argument.

Values of different types may not be compared. Attempts to do so will
result in an error."),
    sys_fn!(fn_le,          Min(2),
"Returns whether each argument compares less than or equal to each
successive argument.

Values of different types may not be compared. Attempts to do so will
result in an error."),
    sys_fn!(fn_ge,          Min(2),
"Returns whether each argument compares greater than or equal to each
successive argument.

Values of different types may not be compared. Attempts to do so will
result in an error."),
    sys_fn!(fn_zero,        Min(1),
"Returns whether all given values are equal to zero."),
    sys_fn!(fn_max,         Min(1),
"Returns the greatest value of given arguments."),
    sys_fn!(fn_min,         Min(1),
"Returns the least value of given arguments."),
    sys_fn!(fn_append,      Min(1),
"Append a series of elements to a given list."),
    sys_fn!(fn_elt,         Exact(2),
"Returns an element from a sequence, starting at zero index."),
    sys_fn!(fn_concat,      Min(1),
"Concatenates a series of sequences."),
    sys_fn!(fn_join,        Min(1),
"Joins a series of lists or strings and chars using a separator value."),
    sys_fn!(fn_len,         Exact(1),
"Returns the length of the given sequence.

String length is in bytes rather than characters."),
    sys_fn!(fn_slice,       Range(2, 3),
"Returns a subsequence of a list or string."),
    sys_fn!(fn_first,       Exact(1),
"Returns the first element of the given list or string."),
    sys_fn!(fn_second,      Exact(1),
"Returns the second element of the given list."),
    sys_fn!(fn_last,        Exact(1),
"Returns the last element of the given list or string."),
    sys_fn!(fn_init,        Exact(1),
"Returns all but the last element of the given list or string."),
    sys_fn!(fn_tail,        Exact(1),
"Returns all but the first element of the given list or string."),
    sys_fn!(fn_list,        Min(0),
"Returns a list of values. In contrast with the `'(a b c ...)` list
construction syntax, this function will evaluate each of its arguments."),
    sys_fn!(fn_reverse,     Exact(1),
"Returns a list in reverse order."),
    sys_fn!(fn_abs,         Exact(1),
"Returns the absolute value of the given numerical value."),
    sys_fn!(fn_ceil,        Exact(1),
"Returns a number value rounded toward positive infinity."),
    sys_fn!(fn_floor,       Exact(1),
"Returns a number value rounded toward negative infinity."),
    sys_fn!(fn_round,       Exact(1),
"Returns a number rounded to the nearest integer.
Rounds half-way cases away from zero."),
    sys_fn!(fn_trunc,       Exact(1),
"Returns a number rounded toward zero."),
    sys_fn!(fn_int,         Exact(1),
"Truncates a float or ratio value and returns its whole portion as an integer.

If the given value is infinite or `NaN`, an error will result."),
    sys_fn!(fn_float,       Exact(1),
"Returns the given value as a floating point value."),
    sys_fn!(fn_inf,         Min(0),
"Returns whether all given arguments are equal to positive or negative infinity.

Given no arguments, returns the value of positive infinity."),
    sys_fn!(fn_nan,         Min(0),
"Returns whether all given arguments are equal to `NaN`.

Given no arguments, returns the value of `NaN`."),
    sys_fn!(fn_denom,       Exact(1),
"Returns the denominator of a ratio."),
    sys_fn!(fn_fract,       Exact(1),
"Returns the fractional portion of a float or ratio."),
    sys_fn!(fn_numer,       Exact(1),
"Returns the numerator of a ratio."),
    sys_fn!(fn_rat,         Range(1, 2),
"Returns the given numerical value as a ratio."),
    sys_fn!(fn_recip,       Exact(1),
"Returns the reciprocal of the given numeric value.

If the value is of type integer, the value returned will be a ratio."),
    sys_fn!(fn_chars,       Exact(1),
"Returns a string transformed into a list of characters."),
    sys_fn!(fn_string,      Exact(1),
"Returns an argument converted into a string."),
    sys_fn!(fn_path,         Exact(1),
"Returns an argument converted into a path."),
    sys_fn!(fn_bytes,       Exact(1),
"Returns an argument converted into a byte string."),
    sys_fn!(fn_id,          Exact(1),
"Returns the unmodified value of the argument received."),
    sys_fn!(fn_is,          Exact(2),
"    (is type value)

Returns whether a given expression matches the named type.

`is` also accepts `'number` as a type name, which matches `integer`, `float`,
and `ratio` type values."),
    sys_fn!(fn_is_instance, Exact(2),
"    (is-instance def value)

Returns whether a given struct value is an instance of
the named struct definition."),
    sys_fn!(fn_null,        Exact(1),
"Returns whether the given value is unit, `()`."),
    sys_fn!(fn_type_of,     Exact(1),
"Returns a name representing the type of the given value."),
    sys_fn!(fn_dot,         Exact(2),
"    (. value field-name)

Accesses a field from a struct value."),
    sys_fn!(fn_dot_eq,      Min(1),
"    (.= struct :field value)

Returns a new struct value with named fields replaced with new values."),
    sys_fn!(fn_new,         Min(1),
"    (new struct-def :field value)

Creates a struct value."),
    sys_fn!(fn_format,      Min(1),
"Returns a formatted string."),
    sys_fn!(fn_print,       Min(1),
"Prints a formatted string to `stdout`."),
    sys_fn!(fn_println,     Min(1),
"Prints a formatted string to `stdout`, followed by a newline."),
    sys_fn!(fn_panic,       Range(0, 1),
"Immediately interrupts execution upon evaluation.

It accepts an optional parameter describing the reason for the panic."),
    sys_fn!(fn_xor,         Exact(2),
"Returns the exclusive-or of the given boolean values."),
    sys_fn!(fn_not,         Exact(1),
"Returns the inverse of the given boolean value."),
];

/// Describes the number of arguments a function may accept.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum Arity {
    /// Function accepts exactly *n* arguments
    Exact(u32),
    /// Function accepts at least *n* arguments
    Min(u32),
    /// Function accepts an inclusive range of arguments
    Range(u32, u32),
}

impl Arity {
    /// Returns whether this arity may accept `n` arguments.
    pub fn accepts(&self, n: u32) -> bool {
        match *self {
            Arity::Exact(num) => n == num,
            Arity::Min(min) => n >= min,
            Arity::Range(min, max) => n >= min && n <= max,
        }
    }
}

impl fmt::Display for Arity {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Arity::Exact(n) => write!(f, "{} argument{}", n, plural(n)),
            Arity::Min(n) => write!(f, "at least {} argument{}", n, plural(n)),
            Arity::Range(min, max) => if min + 1 == max {
                write!(f, "{} or {} arguments", min, max)
            } else {
                write!(f, "between {} and {} arguments", min, max)
            }
        }
    }
}

// TODO: Should probably go into some utility module
/// Returns the suitable plural suffix `""` or `"s"` for count `n`.
pub fn plural(n: u32) -> &'static str {
    if n == 1 { "" } else { "s" }
}

/// Represents a function implemented in Rust.
#[derive(Copy, Clone)]
pub struct Function {
    /// Function name
    pub name: Name,
    /// System function
    pub sys_fn: SystemFn,
}

impl fmt::Debug for Function {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Function {{ name: {:?}, ... }}", self.name)
    }
}

impl PartialEq for Function {
    fn eq(&self, rhs: &Function) -> bool {
        self.sys_fn == rhs.sys_fn
    }
}

/// Represents a function that evaluates an expression.
#[derive(Clone)]
pub struct Lambda {
    /// Bytecode implementation
    pub code: Rc<Code>,
    /// Scope in which the lambda was created.
    /// A weak reference is used to prevent cycles.
    pub scope: WeakScope,
    /// Enclosed values
    pub values: Option<Rc<Box<[Value]>>>,
}

impl Lambda {
    /// Creates a new `Lambda`.
    pub fn new(code: Rc<Code>, scope: &Scope) -> Lambda {
        Lambda{
            code: code,
            scope: Rc::downgrade(scope),
            values: None,
        }
    }

    /// Creates a new `Lambda` enclosing a set of values.
    pub fn new_closure(code: Rc<Code>, scope: WeakScope, values: Box<[Value]>) -> Lambda {
        Lambda{
            code: code,
            scope: scope,
            values: Some(Rc::new(values)),
        }
    }
}

impl fmt::Debug for Lambda {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // Leave out scope to avoid infinite recursion
        f.debug_struct("Lambda")
            .field("code", &self.code)
            .field("values", &self.values)
            .finish()
    }
}

impl PartialEq for Lambda {
    fn eq(&self, rhs: &Lambda) -> bool {
        let a: &Code = &self.code;
        let b: &Code = &rhs.code;
        (a as *const _) == (b as *const _)
    }
}

fn get_float(v: &Value) -> Result<f64, ExecError> {
    FromValueRef::from_value_ref(v)
}

fn get_keyword(v: &Value) -> Result<Name, ExecError> {
    match *v {
        Value::Keyword(name) => Ok(name),
        ref v => Err(ExecError::expected("keyword", v))
    }
}

fn get_name(v: &Value) -> Result<Name, ExecError> {
    match *v {
        Value::Name(name) => Ok(name),
        ref v => Err(ExecError::expected("name", v))
    }
}

fn get_string(v: &Value) -> Result<&str, ExecError> {
    FromValueRef::from_value_ref(v)
}

fn get_struct_def_for(scope: &Scope, v: &Value) -> Result<Rc<StructDef>, ExecError> {
    match *v {
        Value::Struct(ref s) => Ok(s.def().clone()),
        ref fv @ Value::Foreign(_) => get_foreign_value_struct_def(scope, fv),
        ref v => Err(ExecError::expected("struct", v))
    }
}

fn get_foreign_value_struct_def(scope: &Scope, v: &Value) -> Result<Rc<StructDef>, ExecError> {
    match *v {
        Value::Foreign(ref fv) => {
            scope.get_struct_def(fv.type_id())
                .ok_or_else(|| ExecError::expected("struct", v))
        }
        _ => unreachable!()
    }
}

fn get_struct_def(v: &Value) -> Result<&Rc<StructDef>, ExecError> {
    match *v {
        Value::StructDef(ref d) => Ok(d),
        ref v => Err(ExecError::expected("struct-def", v))
    }
}

fn expect_integer(v: &Value) -> Result<&Integer, ExecError> {
    match *v {
        Value::Integer(ref i) => Ok(i),
        _ => Err(ExecError::expected("integer", v))
    }
}

fn expect_integer_owned(v: Value) -> Result<Integer, ExecError> {
    match v {
        Value::Integer(i) => Ok(i),
        ref v => Err(ExecError::expected("integer", v))
    }
}

fn expect_number(v: &Value) -> Result<(), ExecError> {
    match *v {
        Value::Float(_) | Value::Integer(_) | Value::Ratio(_) => Ok(()),
        _ => Err(ExecError::expected("number", v))
    }
}

fn test_zero<T: Zero>(t: &T) -> Result<(), ExecError> {
    if t.is_zero() {
        Err(ExecError::DivideByZero)
    } else {
        Ok(())
    }
}

/// Returns whether a `Value` matches a given type.
///
/// The type name `number` will match `integer`, `float`, or `ratio` values.
pub fn value_is(scope: &Scope, a: &Value, ty: Name) -> bool {
    use name::standard_names::*;

    match *a {
        Value::Float(_) | Value::Integer(_) | Value::Ratio(_)
            if ty == NUMBER => true,
        Value::Unit | Value::List(_) if ty == LIST => true,
        Value::Foreign(ref a) =>
            scope.with_name(ty, |name| a.is_type(name)),
        _ => type_of(scope, a) == ty
    }
}

fn coerce_numbers(lhs: Value, rhs: &Value) -> Result<(Value, Cow<Value>), ExecError> {
    let (lhs, rhs) = match (lhs, rhs) {
        (lhs @ Value::Float(_), rhs @ &Value::Float(_))
        | (lhs @ Value::Integer(_), rhs @ &Value::Integer(_))
        | (lhs @ Value::Ratio(_), rhs @ &Value::Ratio(_)) => (lhs, Borrowed(rhs)),

        (Value::Float(lhs), &Value::Integer(ref i)) =>
            (lhs.into(), Owned(i.to_f64().ok_or(ExecError::Overflow)?.into())),
        (Value::Integer(ref i), rhs @ &Value::Float(_)) =>
            (i.to_f64().ok_or(ExecError::Overflow)?.into(), Borrowed(rhs)),

        (ref mut lhs @ Value::Ratio(_), &Value::Integer(ref i)) =>
            (lhs.take(), Owned(Ratio::from_integer(i.clone()).into())),
        (Value::Integer(i), rhs @ &Value::Ratio(_)) =>
            (Ratio::from_integer(i).into(), Borrowed(rhs)),

        (Value::Float(lhs), &Value::Ratio(ref r)) =>
            (lhs.into(), Owned(r.to_f64().ok_or(ExecError::Overflow)?.into())),
        (Value::Ratio(ref r), rhs @ &Value::Float(_)) =>
            (r.to_f64().ok_or(ExecError::Overflow)?.into(), Borrowed(rhs)),

        (lhs, rhs) => (lhs, Borrowed(rhs))
    };

    Ok((lhs, rhs))
}

// TODO: Move these doc comments somewhere else.
// An otherwise empty module with docs for functions and operators may suffice.

/// `+` returns the sum of all arguments.
///
/// Given no arguments, returns the additive identity, `0`.
fn fn_add(ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    if args.is_empty() {
        return Ok(Integer::zero().into());
    }

    let mut v = args[0].take();

    expect_number(&v)?;

    for arg in &args[1..] {
        expect_number(arg)?;
        v = add_number(ctx, v, arg)?;
    }

    Ok(v)
}

/// Returns the result of adding two values together.
pub fn add_number(ctx: &Context, lhs: Value, rhs: &Value) -> Result<Value, Error> {
    let (lhs, rhs) = coerce_numbers(lhs, rhs)?;

    match (lhs, &*rhs) {
        (Value::Float(a), &Value::Float(b)) => Ok((a + b).into()),
        (Value::Integer(ref a), &Value::Integer(ref b)) => {
            check_bits(ctx, max(a.bits(), b.bits()) + 1)?;
            Ok((a + b).into())
        }
        (Value::Ratio(ref a), &Value::Ratio(ref b)) => {
            let nd = a.numer().bits() + b.denom().bits();
            let dn = a.denom().bits() + b.numer().bits();
            let dd = a.denom().bits() + b.denom().bits();

            check_bits(ctx, nd + dn)?;
            check_bits(ctx, dd)?;

            Ok((a + b).into())
        }
        (a, b) => Err(From::from(ExecError::TypeMismatch{
            lhs: a.type_name(),
            rhs: b.type_name(),
        })),
    }
}

/// `-` returns the cumulative difference between successive arguments.
fn fn_sub(ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    let mut v = args[0].take();

    if args.len() == 1 {
        neg_number(v)
    } else {
        expect_number(&v)?;

        for arg in &args[1..] {
            expect_number(arg)?;
            v = sub_number(ctx, v, arg)?;
        }

        Ok(v)
    }
}

/// Returns the result of negating a value.
pub fn neg_number(v: Value) -> Result<Value, Error> {
    match v {
        Value::Float(f) => Ok((-f).into()),
        Value::Integer(i) => Ok((-i).into()),
        Value::Ratio(r) => Ok((-r).into()),
        ref v => Err(From::from(ExecError::expected("number", v)))
    }
}

/// Returns the resulting of subtracting a value from another.
pub fn sub_number(ctx: &Context, lhs: Value, rhs: &Value) -> Result<Value, Error> {
    let (lhs, rhs) = coerce_numbers(lhs, rhs)?;

    match (lhs, &*rhs) {
        (Value::Float(a), &Value::Float(b)) => Ok((a - b).into()),
        (Value::Integer(ref a), &Value::Integer(ref b)) => {
            check_bits(ctx, max(a.bits(), b.bits()) + 1)?;
            Ok((a - b).into())
        }
        (Value::Ratio(ref a), &Value::Ratio(ref b)) => {
            let nd = a.numer().bits() + b.denom().bits();
            let dn = a.denom().bits() + b.numer().bits();
            let dd = a.denom().bits() + b.denom().bits();

            check_bits(ctx, nd + dn)?;
            check_bits(ctx, dd)?;

            Ok((a - b).into())
        }
        (a, b) => Err(From::from(ExecError::TypeMismatch{
            lhs: a.type_name(),
            rhs: b.type_name(),
        }))
    }
}

/// `*` returns the product of all arguments.
///
/// Given no arguments, returns the multiplicative identity, `1`.
fn fn_mul(ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    if args.is_empty() {
        return Ok(Integer::one().into());
    }

    let mut v = args[0].take();

    expect_number(&v)?;

    for arg in &args[1..] {
        expect_number(arg)?;
        v = mul_number(ctx, v, arg)?;
    }

    Ok(v)
}

/// Returns the result of multiplying two values together.
pub fn mul_number(ctx: &Context, lhs: Value, rhs: &Value) -> Result<Value, Error> {
    let (lhs, rhs) = coerce_numbers(lhs, rhs)?;

    match (lhs, &*rhs) {
        (Value::Float(a), &Value::Float(b)) => Ok((a * b).into()),
        (Value::Integer(ref a), &Value::Integer(ref b)) => {
            check_bits(ctx, a.bits() + b.bits())?;
            Ok((a * b).into())
        }
        (Value::Ratio(ref a), &Value::Ratio(ref b)) => {
            let nn = a.numer().bits() + b.numer().bits();
            let dd = a.denom().bits() + b.denom().bits();

            check_bits(ctx, nn)?;
            check_bits(ctx, dd)?;

            Ok((a * b).into())
        }
        (a, b) => Err(From::from(ExecError::TypeMismatch{
            lhs: a.type_name(),
            rhs: b.type_name(),
        }))
    }
}

/// `^` returns a base value raised to an exponent.
fn fn_pow(ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    let a = args[0].take();
    let b = args[1].take();

    expect_number(&a)?;
    expect_number(&b)?;

    pow_number(ctx, a, b)
}

// I'm not aware of any method to directly calculate the bit length of an
// exponent without calculating the exponent, so we instead employ a test on
// each multiplication step.
fn try_pow(ctx: &Context, base: &Integer, mut exp: u32) -> Result<Integer, Error> {
    if ctx.restrict().max_integer_size == usize::max_value() {
        return Ok(base.clone().pow(exp as usize));
    }

    if exp == 0 {
        return Ok(Integer::one());
    }

    let mut base = base.clone();

    while exp & 1 == 0 {
        base = try_mul(ctx, &base, &base)?;
        exp >>= 1;
    }

    if exp == 1 {
        return Ok(base);
    }

    let mut acc = base.clone();

    while exp > 1 {
        exp >>= 1;
        base = try_mul(ctx, &base, &base)?;

        if exp & 1 == 1 {
            try_mul_assign(ctx, &mut acc, &base)?;
        }
    }

    Ok(acc)
}

fn try_mul(ctx: &Context, lhs: &Integer, rhs: &Integer) -> Result<Integer, Error> {
    check_bits(ctx, lhs.bits() + rhs.bits())?;

    Ok(lhs * rhs)
}

fn try_mul_assign(ctx: &Context, lhs: &mut Integer, rhs: &Integer) -> Result<(), Error> {
    check_bits(ctx, lhs.bits() + rhs.bits())?;

    *lhs *= rhs;
    Ok(())
}

fn check_bits(ctx: &Context, bits: usize) -> Result<(), RestrictError> {
    if bits > ctx.restrict().max_integer_size {
        Err(RestrictError::IntegerLimitExceeded)
    } else {
        Ok(())
    }
}

fn pow_number(ctx: &Context, lhs: Value, rhs: Value) -> Result<Value, Error> {
    match (&lhs, &rhs) {
        (&Value::Ratio(ref a), &Value::Integer(ref b)) =>
            return pow_ratio_integer(ctx, a, b),
        (&Value::Ratio(ref a), &Value::Ratio(ref b)) if b.is_integer() =>
            return pow_ratio_integer(ctx, a, b.numer()),
        _ => ()
    }

    let (lhs, rhs) = coerce_numbers(lhs, &rhs)?;

    match (lhs, &*rhs) {
        (Value::Float(a), &Value::Float(b)) => {
            Ok(a.powf(b).into())
        }
        (Value::Integer(ref a), &Value::Integer(ref b)) => {
            if b.is_negative() {
                let a = a.to_f64().ok_or(ExecError::Overflow)?;
                let b = b.to_f64().ok_or(ExecError::Overflow)?;
                Ok(a.powf(b).into())
            } else {
                let exp = b.to_u32().ok_or(ExecError::Overflow)?;
                try_pow(ctx, a, exp).map(|i| i.into())
            }
        }
        (Value::Ratio(ref a), &Value::Ratio(ref b)) => {
            let a = a.to_f64().ok_or(ExecError::Overflow)?;
            let b = b.to_f64().ok_or(ExecError::Overflow)?;

            Ok(a.powf(b).into())
        }
        (ref a, b) => Err(From::from(ExecError::TypeMismatch{
            lhs: a.type_name(),
            rhs: b.type_name(),
        })),
    }
}

fn pow_ratio_integer(ctx: &Context, lhs: &Ratio, rhs: &Integer) -> Result<Value, Error> {
    if rhs.is_negative() {
        let lhs = lhs.to_f64().ok_or(ExecError::Overflow)?;
        let rhs = rhs.to_f64().ok_or(ExecError::Overflow)?;

        Ok(lhs.powf(rhs).into())
    } else {
        let rhs = rhs.to_u32().ok_or(ExecError::Overflow)?;
        let a = try_pow(ctx, lhs.numer(), rhs)?;
        let b = try_pow(ctx, lhs.denom(), rhs)?;

        Ok(Ratio::new(a, b).into())
    }
}

/// `/` returns the cumulative quotient of successive arguments.
fn fn_div(ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    let mut v = args[0].take();

    expect_number(&v)?;

    if args.len() == 1 {
        // Call div instead of recip so that (/ 1) = 1
        div_number(ctx, 1.into(), &v)
    } else {
        for arg in &args[1..] {
            expect_number(arg)?;
            v = div_number(ctx, v, arg)?;
        }

        Ok(v)
    }
}

/// `//` returns the cumulative quotient of successive arguments,
/// rounded toward negative infinity.
fn fn_floor_div(ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    let mut v = args[0].take();

    expect_number(&v)?;

    if args.len() == 1 {
        floor_recip_number(v)
    } else {
        for arg in &args[1..] {
            expect_number(arg)?;
            v = floor_div_number_step(ctx, v, arg)?;
        }

        floor_number(v)
    }
}

fn floor_recip_number(v: Value) -> Result<Value, Error> {
    match v {
        Value::Integer(ref i) => {
            test_zero(i)?;
            Ok((Integer::one() / i).into())
        }
        Value::Float(f) => {
            Ok(f.recip().floor().into())
        }
        Value::Ratio(ref r) => {
            test_zero(r)?;
            Ok(r.recip().floor().into())
        }
        ref v => Err(From::from(ExecError::expected("number", v)))
    }
}

/// Returns the result of dividing two values.
pub fn div_number(ctx: &Context, lhs: Value, rhs: &Value) -> Result<Value, Error> {
    let (lhs, rhs) = coerce_numbers(lhs, rhs)?;

    match (lhs, &*rhs) {
        (Value::Float(a), &Value::Float(b)) => {
            Ok((a / b).into())
        }
        (Value::Integer(ref a), &Value::Integer(ref b)) => {
            test_zero(b)?;
            if a.is_multiple_of(b) {
                Ok((a / b).into())
            } else {
                Ok(Ratio::new(a.clone(), b.clone()).into())
            }
        }
        (Value::Ratio(ref a), &Value::Ratio(ref b)) => {
            test_zero(b)?;

            let nd = a.numer().bits() + b.denom().bits();
            let dn = a.denom().bits() + b.numer().bits();

            check_bits(ctx, nd)?;
            check_bits(ctx, dn)?;

            Ok((a / b).into())
        }
        (a, b) => Err(From::from(ExecError::TypeMismatch{
            lhs: a.type_name(),
            rhs: b.type_name(),
        }))
    }
}

/// Returns the result of floor-dividing two values,
/// without calling `floor` on the result.
pub fn floor_div_number_step(ctx: &Context, lhs: Value, rhs: &Value) -> Result<Value, Error> {
    let (lhs, rhs) = coerce_numbers(lhs, rhs)?;

    match (lhs, &*rhs) {
        (Value::Integer(ref a), &Value::Integer(ref b)) => {
            test_zero(b)?;
            Ok((a / b).into())
        }
        (lhs, rhs) => div_number(ctx, lhs, rhs)
    }
}

/// `rem` returns the remainder of two arguments.
fn fn_rem(_ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    let a = args[0].take();
    expect_number(&a)?;

    let b = &args[1];
    expect_number(b)?;

    rem_number(a, b)
}

fn rem_number(lhs: Value, rhs: &Value) -> Result<Value, Error> {
    let (lhs, rhs) = coerce_numbers(lhs, rhs)?;

    match (lhs, &*rhs) {
        (Value::Float(a), &Value::Float(b)) => {
            Ok((a % b).into())
        }
        (Value::Integer(ref a), &Value::Integer(ref b)) => {
            test_zero(b)?;
            Ok((a % b).into())
        }
        (Value::Ratio(ref a), &Value::Ratio(ref b)) => {
            test_zero(b)?;
            Ok((a % b).into())
        }
        (a, b) => Err(From::from(ExecError::TypeMismatch{
            lhs: a.type_name(),
            rhs: b.type_name(),
        }))
    }
}

/// `<<` returns an integer, bit shifted left by a given number.
fn fn_shl(ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    let a = &args[0];
    let b = &args[1];

    shl_integer(ctx, a, b)
}

fn shl_integer(ctx: &Context, lhs: &Value, rhs: &Value) -> Result<Value, Error> {
    let lhs = expect_integer(lhs)?;
    let rhs = expect_integer(rhs)?;

    match rhs.to_u32() {
        Some(n) => {
            check_bits(ctx, lhs.bits() + n as usize)?;
            Ok((lhs << (n as usize)).into())
        }
        None => Err(From::from(ExecError::Overflow)),
    }
}

/// `>>` returns an integer, bit shifted right by a given number.
fn fn_shr(_ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    let a = &args[0];
    let b = &args[1];

    shr_integer(a, b)
}

fn shr_integer(lhs: &Value, rhs: &Value) -> Result<Value, Error> {
    let lhs = expect_integer(lhs)?;
    let rhs = expect_integer(rhs)?;

    match rhs.to_u32() {
        Some(n) => Ok((lhs >> (n as usize)).into()),
        None => Err(From::from(ExecError::Overflow)),
    }
}

/// `bit-and` The bitwise AND operator.
fn fn_bit_and(_ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    if args.is_empty() {
        return Ok((-Integer::one()).into());
    }

    let mut v = expect_integer_owned(args[0].take())?;

    for arg in &args[1..] {
        v &= expect_integer(arg)?;
    }

    Ok(v.into())
}

/// Returns the bitwise AND of two integer values.
pub fn bit_and_integer(lhs: Value, rhs: &Value) -> Result<Value, Error> {
    let lhs = expect_integer_owned(lhs)?;
    let rhs = expect_integer(rhs)?;

    Ok((lhs & rhs).into())
}

/// `bit-or` The bitwise OR operator.
fn fn_bit_or(_ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    if args.is_empty() {
        return Ok(Integer::zero().into());
    }

    let mut v = expect_integer_owned(args[0].take())?;

    for arg in &args[1..] {
        v |= expect_integer(arg)?;
    }

    Ok(v.into())
}

/// Returns the bitwise OR of two integers.
pub fn bit_or_integer(lhs: Value, rhs: &Value) -> Result<Value, Error> {
    let lhs = expect_integer_owned(lhs)?;
    let rhs = expect_integer(rhs)?;

    Ok((lhs | rhs).into())
}

/// `bit-xor` The bitwise XOR operator.
fn fn_bit_xor(_ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    if args.is_empty() {
        return Ok(Integer::zero().into());
    }

    let mut v = expect_integer_owned(args[0].take())?;

    for arg in &args[1..] {
        v ^= expect_integer(arg)?;
    }

    Ok(v.into())
}

/// Returns the bitwise XOR of two integers.
pub fn bit_xor_integer(lhs: Value, rhs: &Value) -> Result<Value, Error> {
    let lhs = expect_integer_owned(lhs)?;
    let rhs = expect_integer(rhs)?;

    Ok((lhs ^ rhs).into())
}

/// `bit_not` The bitwise NOT operator.
fn fn_bit_not(_ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    match args[0].take() {
        Value::Integer(i) => Ok((!i).into()),
        ref v => Err(From::from(ExecError::expected("integer", v))),
    }
}

/// `=` returns whether the given arguments compare equal to one another.
///
/// Values of different types may not be compared. Attempts to do so will
/// result in a `TypeMismatch` error.
fn fn_eq(_ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    let mut r = true;
    let v = &args[0];

    for arg in &args[1..] {
        let eq = v.is_equal(arg)?;

        if !eq {
            r = false;
            break;
        }
    }

    Ok(r.into())
}

/// `/=` returns whether each given argument differs in value from each other argument.
///
/// Values of different types may not be compared. Attempts to do so will
/// result in a `TypeMismatch` error.
fn fn_ne(_ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    let mut r = true;

    'outer: for (i, lhs) in args.iter().enumerate() {
        for rhs in &args[i + 1..] {
            let eq = lhs.is_equal(rhs)?;

            if eq {
                r = false;
                break 'outer;
            }
        }
    }

    Ok(r.into())
}

/// `eq` performs "weak" equality comparison of arguments.
///
/// Any case in which `=` would cause an error, `eq` instead returns `false`.
fn fn_weak_eq(ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    match fn_eq(ctx, args) {
        Ok(v) => Ok(v),
        Err(_) => Ok(false.into())
    }
}

/// `ne` performs "weak" inequality comparison of arguments.
///
/// Any case in which `/=` would cause an error, `ne` instead returns `true`.
fn fn_weak_ne(ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    match fn_ne(ctx, args) {
        Ok(v) => Ok(v),
        Err(_) => Ok(true.into())
    }
}

/// `<` returns whether each argument compares less than each successive argument.
///
/// Values of different types may not be compared. Attempts to do so will
/// result in a `TypeMismatch` error.
fn fn_lt(_ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    let mut r = true;
    let mut v = &args[0];

    for arg in &args[1..] {
        let ord = v.compare(arg)?;

        if ord != Ordering::Less {
            r = false;
            break;
        }
        v = arg;
    }

    Ok(r.into())
}

/// `>` returns whether each argument compares greater than each successive argument.
///
/// Values of different types may not be compared. Attempts to do so will
/// result in a `TypeMismatch` error.
fn fn_gt(_ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    let mut r = true;
    let mut v = &args[0];

    for arg in &args[1..] {
        let ord = v.compare(arg)?;

        if ord != Ordering::Greater {
            r = false;
            break;
        }
        v = arg;
    }

    Ok(r.into())
}

/// `<=` returns whether each argument compares less than or equal to each
/// successive argument.
///
/// Values of different types may not be compared. Attempts to do so will
/// result in a `TypeMismatch` error.
fn fn_le(_ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    let mut r = true;
    let mut v = &args[0];

    for arg in &args[1..] {
        let ord = v.compare(arg)?;

        if ord == Ordering::Greater {
            r = false;
            break;
        }
        v = arg;
    }

    Ok(r.into())
}

/// `>=` returns whether each argument compares greater than or equal to each
/// successive argument.
///
/// Values of different types may not be compared. Attempts to do so will
/// result in a `TypeMismatch` error.
fn fn_ge(_ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    let mut r = true;
    let mut v = &args[0];

    for arg in &args[1..] {
        let ord = v.compare(arg)?;

        if ord == Ordering::Less {
            r = false;
            break;
        }
        v = arg;
    }

    Ok(r.into())
}

/// `zero` returns whether all given values are equal to zero.
fn fn_zero(_ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    let mut r = true;

    for arg in args {
        let is_zero = match *arg {
            Value::Float(a) => a == 0.0,
            Value::Integer(ref a) => a.is_zero(),
            Value::Ratio(ref a) => a.is_zero(),
            ref v => return Err(From::from(ExecError::expected("number", v)))
        };

        if !is_zero {
            r = false;
            break;
        }
    }

    Ok(r.into())
}

/// `xor` returns the exclusive-or of the given boolean values.
fn fn_xor(_ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    let a = &args[0];
    let b = &args[1];

    match (a, b) {
        (&Value::Bool(a), &Value::Bool(b)) => Ok((a ^ b).into()),
        (&Value::Bool(_), b) => Err(From::from(ExecError::expected("bool", b))),
        (a, _) => Err(From::from(ExecError::expected("bool", a)))
    }
}

/// `not` returns the inverse of the given boolean value.
fn fn_not(_ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    match args[0] {
        Value::Bool(a) => Ok((!a).into()),
        ref v => Err(From::from(ExecError::expected("bool", v)))
    }
}

/// `id` returns the unmodified value of the argument received.
fn fn_id(_ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    Ok(args[0].take())
}

/// `is` returns whether a given expression matches the named type.
///
/// ```lisp
/// (is 'integer 1)
/// (is 'list '(1 2 3))
/// ```
///
/// `is` also accepts `'number` as a type name, which matches `integer`, `float`,
/// and `ratio` type values.
fn fn_is(ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    let name = get_name(&args[0])?;
    Ok(Value::Bool(value_is(ctx.scope(), &args[1], name)))
}

/// `is-instance` returns whether a given struct value is an instance of
/// the named struct definition.
fn fn_is_instance(_ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    let def = get_struct_def(&args[0])?;

    let sv = &args[1];

    Ok(def.def().is_instance(sv, def).into())
}

/// `null` returns whether the given value is unit, `()`.
fn fn_null(_ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    let is_null = match args[0] {
        Value::Unit => true,
        _ => false
    };

    Ok(is_null.into())
}

fn type_of(scope: &Scope, v: &Value) -> Name {
    use name::standard_names::*;

    match *v {
        Value::Unit => UNIT,
        // It should never be possible to operate on an Unbound value;
        // however, in the case of a bug, this seems preferrable to a panic.
        Value::Unbound => UNBOUND,
        Value::Bool(_) => BOOL,
        Value::Float(_) => FLOAT,
        Value::Integer(_) => INTEGER,
        Value::Ratio(_) => RATIO,
        Value::Struct(_) => STRUCT,
        Value::StructDef(_) => STRUCT_DEF,
        Value::Name(_) => NAME,
        Value::Keyword(_) => KEYWORD,
        Value::Char(_) => CHAR,
        Value::String(_) => STRING,
        Value::Bytes(_) => BYTES,
        Value::Path(_) => PATH,
        Value::List(_) => LIST,
        Value::Function(_) => FUNCTION,
        Value::Lambda(_) => LAMBDA,
        Value::Quasiquote(_, _) |
        Value::Comma(_, _) |
        Value::CommaAt(_, _) |
        Value::Quote(_, _) => OBJECT,
        Value::Foreign(ref a) => scope.add_name(a.type_name()),
    }
}

/// `type-of` returns a name representing the type of the given value.
fn fn_type_of(ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    Ok(Value::Name(type_of(ctx.scope(), &args[0])))
}

/// `.` accesses a field from a struct value.
///
/// ```lisp
/// (. foo :bar)
/// ```
fn fn_dot(ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    let def = get_struct_def_for(ctx.scope(), &args[0])?;
    let field = get_keyword(&args[1])?;

    def.def().get_field(ctx.scope(), &def, &args[0], field)
}

/// `.=` assigns a value to one or more fields of a struct value.
///
/// ```lisp
/// (.= foo :bar 1)
/// ```
fn fn_dot_eq(ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    let value = args[0].take();

    let def = get_struct_def_for(ctx.scope(), &value)?;

    let mut fields = Vec::with_capacity(args.len() / 2);

    let mut iter = args[1..].iter_mut();

    while let Some(name) = iter.next() {
        let name = get_keyword(name)?;

        let value = match iter.next() {
            Some(v) => v.take(),
            None => return Err(From::from(ExecError::OddKeywordParams))
        };

        if fields.iter().any(|&(n, _)| n == name) {
            return Err(ExecError::DuplicateField(name).into());
        }

        fields.push((name, value));
    }

    def.def().replace_fields(ctx.scope(), &def, value, &mut fields)
}

/// `new` creates a struct value.
///
/// ```lisp
/// (new 'foo :a 1 :b 2)
/// ```
fn fn_new(ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    let def = get_struct_def(&args[0])?.clone();

    let mut fields = Vec::with_capacity(args.len() / 2);
    let mut iter = args[1..].iter_mut();

    while let Some(name) = iter.next() {
        let name = get_keyword(name)?;

        let value = match iter.next() {
            Some(value) => value.take(),
            None => return Err(From::from(ExecError::OddKeywordParams))
        };

        if fields.iter().any(|&(n, _)| n == name) {
            return Err(ExecError::DuplicateField(name).into());
        }

        fields.push((name, value));
    }

    def.def().from_fields(ctx.scope(), &def, &mut fields)
}

/// `format` returns a formatted string.
fn fn_format(ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    let fmt = get_string(&args[0])?;

    let s = format_string(&ctx.scope().borrow_names(), fmt, &args[1..])?;
    Ok(s.into())
}

/// `print` prints a formatted string to `stdout`.
fn fn_print(ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    let fmt = get_string(&args[0])?;
    let scope = ctx.scope();

    let s = format_string(&scope.borrow_names(), fmt, &args[1..])?;

    scope.io().stdout.write_all(s.as_bytes())?;
    scope.io().stdout.flush()?;

    Ok(Value::Unit)
}

/// `println` prints a formatted string to `stdout`, followed by a newline.
fn fn_println(ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    let fmt = get_string(&args[0])?;
    let scope = ctx.scope();

    let mut s = format_string(&scope.borrow_names(), fmt, &args[1..])?;
    if !s.ends_with('\n') {
        s.push('\n');
    }

    scope.io().stdout.write_all(s.as_bytes())?;
    scope.io().stdout.flush()?;

    Ok(Value::Unit)
}

/// `append` append a series of elements to a given list.
///
/// ```lisp
/// (append '(1 2 3) 4 5 6)
/// ```
fn fn_append(_ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    let mut v = match args[0].take() {
        Value::Unit => Vec::new(),
        Value::List(li) => li.into_vec(),
        ref v => return Err(From::from(ExecError::expected("list", v)))
    };

    v.extend(args[1..].iter_mut().map(|v| v.take()));

    Ok(v.into())
}

/// `elt` returns an element from a list, starting at zero index.
///
/// ```lisp
/// (elt '(1 2 3) 0)
/// ```
fn fn_elt(_ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    let li = &args[0];
    let idx = &args[1];

    let idx = usize::from_value_ref(idx)?;

    match *li {
        Value::List(ref li) => li.get(idx).cloned()
            .ok_or_else(|| From::from(ExecError::OutOfBounds(idx))),
        Value::Bytes(ref b) => b.get(idx).cloned()
            .map(|b| b.into())
            .ok_or_else(|| From::from(ExecError::OutOfBounds(idx))),
        ref v => Err(From::from(ExecError::expected("indexable sequence", v)))
    }
}

/// `concat` concatenates a series of lists or strings and chars.
///
/// ```lisp
/// (concat '(1 2 3) () '(4 5 6))
/// (concat "foo" "bar")
/// (concat "foo" #'/' "bar")
/// ```
fn fn_concat(_ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    match args[0] {
        Value::Unit | Value::List(_) => concat_list(args),
        Value::Char(_) | Value::String(_) => concat_string(args),
        Value::Bytes(_) => concat_bytes(args),
        Value::Path(_) => concat_path(args),
        ref v => Err(From::from(ExecError::expected("list or string", v)))
    }
}

fn concat_list(args: &mut [Value]) -> Result<Value, Error> {
    if args.len() == 1 {
        return Ok(args[0].take());
    }

    let mut v = Vec::new();

    for arg in args {
        match arg.take() {
            Value::Unit => (),
            Value::List(li) => v.extend(li.into_vec()),
            ref v => return Err(From::from(ExecError::expected("list", v)))
        }
    }

    Ok(v.into())
}

fn concat_string(args: &mut [Value]) -> Result<Value, Error> {
    if args.len() == 1 {
        return Ok(args[0].take());
    }

    let mut res = String::new();

    for arg in args {
        match *arg {
            Value::Char(ch) => res.push(ch),
            Value::String(ref s) => res.push_str(s),
            ref v => return Err(From::from(ExecError::expected("char or string", v)))
        }
    }

    Ok(res.into())
}

fn concat_bytes(args: &mut [Value]) -> Result<Value, Error> {
    if args.len() == 1 {
        return Ok(args[0].take());
    }

    let mut res = Vec::new();

    for arg in args {
        let b = <&[u8]>::from_value_ref(arg)?;
        res.extend(b);
    }

    Ok(Bytes::new(res).into())
}

fn concat_path(args: &mut [Value]) -> Result<Value, Error> {
    if args.len() == 1 {
        return Ok(args[0].take());
    }

    let mut res = PathBuf::new();

    for arg in args {
        let p = <&Path>::from_value_ref(arg)?;

        res.push(p);
    }

    Ok(res.into())
}

/// `join` joins a series of lists or strings and chars using a separator value.
///
/// ```lisp
/// (join '(0) '(1 2 3) '(4 5 6))
/// (join ":" "foo" "bar")
/// ```
fn fn_join(_ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    let (first, rest) = args.split_first_mut().unwrap();

    match *first {
        Value::Unit => concat_list(rest),
        Value::List(ref li) => join_list(li, rest),
        Value::Char(ch) => {
            let mut s = String::new();
            s.push(ch);
            join_string(&s, rest)
        }
        Value::String(ref s) if s.is_empty() => concat_string(rest),
        Value::String(ref s) => join_string(s, rest),
        Value::Bytes(ref s) => join_bytes(s, rest),
        ref v => Err(From::from(ExecError::expected("list or string", v)))
    }
}

fn join_list(sep: &[Value], args: &mut [Value]) -> Result<Value, Error> {
    let mut v = Vec::new();

    if let Some((first, rest)) = args.split_first_mut() {
        match first.take() {
            Value::Unit => (),
            Value::List(li) => v.extend(li.into_vec()),
            ref v => return Err(From::from(ExecError::expected("list", v)))
        }

        for arg in rest {
            v.extend(sep.iter().cloned());

            match arg.take() {
                Value::Unit => (),
                Value::List(li) => v.extend(li.into_vec()),
                ref v => return Err(From::from(ExecError::expected("list", v)))
            }
        }
    }

    Ok(v.into())
}

fn join_string(sep: &str, args: &mut [Value]) -> Result<Value, Error> {
    let mut res = String::new();

    if let Some(value) = args.first() {
        match *value {
            Value::Char(ch) => res.push(ch),
            Value::String(ref s) => res.push_str(s),
            ref v => return Err(From::from(ExecError::expected("char or string", v)))
        }

        for arg in &args[1..] {
            res.push_str(sep);
            match *arg {
                Value::Char(ch) => res.push(ch),
                Value::String(ref s) => res.push_str(s),
                ref v => return Err(From::from(ExecError::expected("char or string", v)))
            }
        }
    }

    Ok(res.into())
}

fn join_bytes(sep: &Bytes, args: &mut [Value]) -> Result<Value, Error> {
    let mut res = Vec::new();
    let sep: &[u8] = sep;

    if let Some(arg) = args.first() {
        let b = <&[u8]>::from_value_ref(arg)?;

        res.extend(b);

        for arg in &args[1..] {
            res.extend(sep);
            let b = <&[u8]>::from_value_ref(arg)?;
            res.extend(b);
        }
    }

    Ok(Bytes::from(res).into())
}

/// `len` returns the length of the given list or string.
fn fn_len(_ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    let n = match args[0] {
        Value::Unit => 0,
        Value::List(ref li) => li.len(),
        Value::String(ref s) => s.len(),
        Value::Bytes(ref b) => b.len(),
        ref v => return Err(From::from(ExecError::expected("sequence", v)))
    };

    Ok(n.into())
}

/// `slice` returns a subsequence of a list or string.
fn fn_slice(_ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    let begin = usize::from_value_ref(&args[1])?;

    if args.len() == 2 {
        match args[0] {
            Value::Unit => {
                if begin > 0 {
                    Err(From::from(ExecError::OutOfBounds(begin)))
                } else {
                    Ok(Value::Unit)
                }
            }
            Value::List(ref li) => {
                let n = li.len();
                if begin > n {
                    Err(From::from(ExecError::OutOfBounds(begin)))
                } else {
                    Ok(li.slice(begin..).into())
                }
            }
            Value::String(ref s) => {
                let n = s.len();
                if begin > n {
                    Err(From::from(ExecError::OutOfBounds(begin)))
                } else if !s.is_char_boundary(begin) {
                    Err(From::from(ExecError::NotCharBoundary(begin)))
                } else {
                    Ok(s.slice(begin..).into())
                }
            }
            Value::Bytes(ref b) => {
                let n = b.len();
                if begin > n {
                    Err(From::from(ExecError::OutOfBounds(begin)))
                } else {
                    Ok(b.slice(begin..).into())
                }
            }
            ref v => Err(From::from(ExecError::expected("list or string", v)))
        }
    } else {
        let end = usize::from_value_ref(&args[2])?;

        if end < begin {
            return Err(From::from(ExecError::InvalidSlice(begin, end)));
        }

        match args[0] {
            Value::Unit => {
                if begin > 0 {
                    Err(From::from(ExecError::OutOfBounds(begin)))
                } else if end > 0 {
                    Err(From::from(ExecError::OutOfBounds(end)))
                } else {
                    Ok(Value::Unit)
                }
            }
            Value::List(ref li) => {
                let n = li.len();
                if begin > n {
                    Err(From::from(ExecError::OutOfBounds(begin)))
                } else if end > n {
                    Err(From::from(ExecError::OutOfBounds(end)))
                } else {
                    Ok(li.slice(begin..end).into())
                }
            }
            Value::String(ref s) => {
                let n = s.len();
                if begin > n {
                    Err(From::from(ExecError::OutOfBounds(begin)))
                } else if end > n {
                    Err(From::from(ExecError::OutOfBounds(end)))
                } else if !s.is_char_boundary(begin) {
                    Err(From::from(ExecError::NotCharBoundary(begin)))
                } else if !s.is_char_boundary(end) {
                    Err(From::from(ExecError::NotCharBoundary(end)))
                } else {
                    Ok(s.slice(begin..end).into())
                }
            }
            Value::Bytes(ref b) => {
                let n = b.len();
                if begin > n {
                    Err(From::from(ExecError::OutOfBounds(begin)))
                } else if end > n {
                    Err(From::from(ExecError::OutOfBounds(end)))
                } else {
                    Ok(b.slice(begin..end).into())
                }
            }
            ref v => Err(From::from(ExecError::expected("list or string", v)))
        }
    }
}

/// `first` returns the first element of the given list or string.
fn fn_first(_ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    first(&args[0])
}

/// `second` returns the second element of the given list.
fn fn_second(_ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    match args[0] {
        Value::List(ref mut li) => li.get(1).cloned()
            .ok_or_else(|| From::from(ExecError::OutOfBounds(1))),
        ref v => Err(From::from(ExecError::expected("list", v)))
    }
}

/// `last` returns the last element of the given list or string.
fn fn_last(_ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    last(&args[0])
}

/// `init` returns all but the last element of the given list or string.
fn fn_init(_ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    init(&args[0])
}

/// `tail` returns all but the first element of the given list or string.
fn fn_tail(_ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    tail(&args[0])
}

/// Returns the first element of a list or string.
///
/// Returns an error in case of an empty list or string.
pub fn first(v: &Value) -> Result<Value, Error> {
    match *v {
        // There can't be an empty list, so this should never panic.
        Value::List(ref li) => Ok(li[0].clone()),
        Value::String(ref s) => match s.chars().next() {
            Some(ch) => Ok(ch.into()),
            None => Err(From::from(ExecError::OutOfBounds(0)))
        },
        Value::Bytes(ref b) => match b.iter().next() {
            Some(&b) => Ok(b.into()),
            None => Err(From::from(ExecError::OutOfBounds(0)))
        },
        ref v => Err(From::from(ExecError::expected("sequence", v)))
    }
}

/// Returns the last element of a list or string.
///
/// Returns an error in case of an empty list or string.
pub fn last(v: &Value) -> Result<Value, Error> {
    match *v {
        Value::List(ref li) => Ok(li.last().cloned().unwrap()),
        Value::String(ref s) => match s.chars().next_back() {
            Some(ch) => Ok(ch.into()),
            None => Err(From::from(ExecError::OutOfBounds(0)))
        },
        Value::Bytes(ref b) => match b.iter().next_back() {
            Some(&b) => Ok(b.into()),
            None => Err(From::from(ExecError::OutOfBounds(0)))
        },
        ref v => Err(From::from(ExecError::expected("sequence", v)))
    }
}

/// Returns all but the last element of a list or string.
///
/// Returns an error in case of an empty list or string.
pub fn init(v: &Value) -> Result<Value, Error> {
    match *v {
        Value::List(ref li) => {
            let len = li.len();
            Ok(li.slice(..len - 1).into())
        }
        Value::String(ref s) => {
            let mut chars = s.char_indices();

            match chars.next_back() {
                Some((idx, _)) => Ok(s.slice(..idx).into()),
                None => Err(From::from(ExecError::OutOfBounds(0)))
            }
        }
        Value::Bytes(ref b) => {
            if b.is_empty() {
                Err(From::from(ExecError::OutOfBounds(0)))
            } else {
                let len = b.len();
                Ok(b.slice(..len - 1).into())
            }
        }
        ref v => Err(From::from(ExecError::expected("sequence", v)))
    }
}

/// Returns all but the first element of a list or string.
///
/// Returns an error in case of an empty list or string.
pub fn tail(v: &Value) -> Result<Value, Error> {
    match *v {
        Value::List(ref li) => {
            Ok(li.slice(1..).into())
        }
        Value::String(ref s) => {
            let mut chars = s.chars();

            match chars.next() {
                Some(ch) => Ok(s.slice(ch.len_utf8()..).into()),
                None => Err(From::from(ExecError::OutOfBounds(0)))
            }
        }
        Value::Bytes(ref b) => {
            if b.is_empty() {
                Err(From::from(ExecError::OutOfBounds(0)))
            } else {
                Ok(b.slice(1..).into())
            }
        }
        ref v => Err(From::from(ExecError::expected("sequence", v)))
    }
}

/// `list` returns a list of values. In contrast with the `'(a b c ...)` list
/// construction syntax, this function will evaluate each of its arguments.
///
/// ```lisp
/// (list 1 2 3)
/// (list (foo) (+ 1 2 3))
/// ```
fn fn_list(_ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    Ok(args.iter_mut().map(|v| v.take())
        .collect::<Vec<_>>().into())
}

/// `reverse` returns a list in reverse order.
fn fn_reverse(_ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    match args[0].take() {
        Value::Unit => Ok(Value::Unit),
        Value::List(li) => {
            let mut li = li.into_vec();
            li.reverse();
            Ok(li.into())
        }
        ref v => Err(From::from(ExecError::expected("list", v)))
    }
}

/// `abs` returns the absolute value of the given numerical value.
fn fn_abs(_ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    match args[0] {
        Value::Float(f) => Ok(f.abs().into()),
        Value::Integer(ref i) => Ok(i.abs().into()),
        Value::Ratio(ref r) => Ok(r.abs().into()),
        ref v => Err(From::from(ExecError::expected("number", v)))
    }
}

/// `ceil` returns a number value rounded toward positive infinity.
fn fn_ceil(_ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    match args[0].take() {
        Value::Float(f) => Ok(f.ceil().into()),
        Value::Integer(i) => Ok(i.into()),
        Value::Ratio(ref r) => Ok(r.ceil().into()),
        ref v => Err(From::from(ExecError::expected("number", v)))
    }
}

/// `floor` returns a number value rounded toward negative infinity.
fn fn_floor(_ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    floor_number(args[0].take())
}

/// Returns a value rounded toward negative infinity.
pub fn floor_number(v: Value) -> Result<Value, Error> {
    match v {
        Value::Float(f) => Ok(f.floor().into()),
        Value::Integer(i) => Ok(i.into()),
        Value::Ratio(ref r) => Ok(r.floor().into()),
        ref v => Err(From::from(ExecError::expected("number", v)))
    }
}

/// `round` returns a number rounded to the nearest integer.
/// Rounds half-way cases away from zero.
fn fn_round(_ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    match args[0].take() {
        Value::Float(f) => Ok(f.round().into()),
        Value::Integer(i) => Ok(i.into()),
        Value::Ratio(ref r) => Ok(r.round().into()),
        ref v => Err(From::from(ExecError::expected("number", v)))
    }
}

/// `trunc` returns a number rounded toward zero.
fn fn_trunc(_ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    match args[0].take() {
        Value::Float(f) => Ok(f.trunc().into()),
        Value::Integer(i) => Ok(i.into()),
        Value::Ratio(ref r) => Ok(r.trunc().into()),
        ref v => Err(From::from(ExecError::expected("number", v)))
    }
}

/// `int` truncates a float or ratio value and returns its whole portion as an integer.
///
/// If the given value is infinite or `NaN`, an error will result.
fn fn_int(_ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    match args[0].take() {
        Value::Float(f) => match f {
            f if f.is_infinite() || f.is_nan() => Err(From::from(ExecError::Overflow)),
            f => Integer::from_f64(f)
                .map(Value::Integer).ok_or_else(|| From::from(ExecError::Overflow)),
        },
        Value::Integer(i) => Ok(i.into()),
        Value::Ratio(ref r) => Ok(r.to_integer().into()),
        ref v => Err(From::from(ExecError::expected("number", v)))
    }
}

/// `float` returns the given value as a floating point value.
fn fn_float(_ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    match args[0] {
        Value::Float(f) => Ok(f.into()),
        Value::Integer(ref i) => Ok(i.to_f64().ok_or(ExecError::Overflow)?.into()),
        Value::Ratio(ref r) => Ok(r.to_f64().ok_or(ExecError::Overflow)?.into()),
        ref v => Err(From::from(ExecError::expected("number", v)))
    }
}

/// `inf` returns whether all given arguments are equal to positive or negative infinity.
/// Given no arguments, returns the value of positive infinity.
fn fn_inf(_ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    if args.is_empty() {
        Ok(f64::INFINITY.into())
    } else {
        let mut r = true;

        for arg in args {
            if get_float(arg)?.is_finite() {
                r = false;
                break;
            }
        }

        Ok(r.into())
    }
}

/// `nan` returns whether all given arguments are equal to `NaN`.
/// Given no arguments, returns the value of `NaN`.
fn fn_nan(_ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    if args.is_empty() {
        Ok(f64::nan().into())
    } else {
        let mut r = true;

        for arg in args {
            if !get_float(arg)?.is_nan() {
                r = false;
                break;
            }
        }

        Ok(r.into())
    }
}

/// `denom` returns the denominator of a ratio.
fn fn_denom(_ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    match args[0] {
        Value::Integer(_) => Ok(Integer::one().into()),
        Value::Ratio(ref r) => Ok(r.denom().clone().into()),
        ref v => Err(From::from(ExecError::expected("integer or ratio", v)))
    }
}

/// `fract` returns the fractional portion of a float or ratio.
fn fn_fract(_ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    match args[0] {
        Value::Float(f) => Ok(f.fract().into()),
        Value::Ratio(ref r) => Ok(r.fract().into()),
        ref v => Err(From::from(ExecError::expected("float or ratio", v)))
    }
}

/// `numer` returns the numerator of a ratio.
fn fn_numer(_ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    match args[0].take() {
        i @ Value::Integer(_) => Ok(i),
        Value::Ratio(r) => Ok(r.numer().clone().into()),
        ref v => Err(From::from(ExecError::expected("integer or ratio", v)))
    }
}

/// `rat` returns the given numerical value as a ratio.
fn fn_rat(_ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    if args.len() == 1 {
        match args[0].take() {
            Value::Float(f) => Ratio::from_f64(f)
                .map(Value::Ratio).ok_or_else(|| From::from(ExecError::Overflow)),
            Value::Integer(a) =>
                Ok(Ratio::from_integer(a).into()),
            Value::Ratio(r) => Ok(r.into()),
            ref v => Err(From::from(ExecError::expected("number", v)))
        }
    } else { // args.len() == 2
        let a = args[0].take();
        let b = args[1].take();

        match (a, b) {
            (Value::Integer(a), Value::Integer(b)) => {
                test_zero(&b)?;
                Ok(Ratio::new(a, b).into())
            }
            (Value::Integer(_), ref b) => Err(From::from(ExecError::expected("integer", b))),
            (ref a, _) => Err(From::from(ExecError::expected("integer", a)))
        }
    }
}

/// `recip` returns the reciprocal of the given numeric value.
/// If the value is of type integer, the value returned will be a ratio.
fn fn_recip(_ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    recip_number(args[0].take())
}

fn recip_number(v: Value) -> Result<Value, Error> {
    match v {
        Value::Float(f) => Ok(f.recip().into()),
        Value::Integer(a) => {
            test_zero(&a)?;
            Ok(Ratio::new(Integer::one(), a).into())
        }
        Value::Ratio(ref a) => {
            test_zero(a.numer())?;
            Ok(a.recip().into())
        }
        ref v => Err(From::from(ExecError::expected("number", v)))
    }
}

/// `chars` returns a string transformed into a list of characters.
fn fn_chars(_ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    let s = get_string(&args[0])?;
    Ok(s.chars().collect::<Vec<_>>().into())
}

/// `string` returns an argument converted into a string.
fn fn_string(ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    match args[0].take() {
        Value::Char(ch) => {
            let mut s = String::new();
            s.push(ch);
            Ok(s.into())
        }
        Value::Name(name) => Ok(ctx.scope().with_name(name, |s| s.into())),
        v @ Value::String(_) => Ok(v),
        ref v => Err(From::from(ExecError::expected("char or string or name", v)))
    }
}

/// `path` returns an argument converted into a path.
fn fn_path(_ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    match args[0].take() {
        Value::String(s) => Ok(PathBuf::from(s.into_string()).into()),
        v @ Value::Path(_) => Ok(v),
        ref v => Err(From::from(ExecError::expected("string or path", v)))
    }
}

/// `bytes` returns an argument converted into a byte string.
fn fn_bytes(_ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    match args[0].take() {
        Value::Unit => Ok(Bytes::from(Vec::new()).into()),
        li @ Value::List(_) => <Vec<u8>>::from_value_ref(&li)
            .map(|b| Bytes::from(b).into()).map_err(From::from),
        Value::String(s) => Ok(Bytes::from(s.into_string()).into()),
        v @ Value::Bytes(_) => Ok(v),
        ref v => Err(From::from(ExecError::expected("bytes or string", v)))
    }
}

/// `max` returns the greatest value of given arguments.
fn fn_max(_ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    let mut v = args[0].take();

    for arg in &mut args[1..] {
        if v.compare(arg)? == Ordering::Less {
            v = arg.take();
        }
    }

    Ok(v)
}

/// `min` returns the least value of given arguments.
fn fn_min(_ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    let mut v = args[0].take();

    for arg in &mut args[1..] {
        if v.compare(arg)? == Ordering::Greater {
            v = arg.take();
        }
    }

    Ok(v)
}

/// `panic` immediately interrupts execution upon evaluation.
/// It accepts an optional parameter describing the reason for the panic.
fn fn_panic(_ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    Err(From::from(ExecError::Panic(args.get_mut(0).map(|v| v.take()))))
}
