//! Implements constant folding for arithmetic functions.

use error::Error;
use exec::{Context, ExecError};
use function::{
    add_number, div_number, floor_div_number_step,
    floor_number, sub_number, mul_number,
    bit_and_integer, bit_or_integer, bit_xor_integer,
};
use value::Value;

/// Describes an operation that can be constant-folded.
///
/// This only applies to functions that can accept an unbounded series of values.
pub trait FoldOp {
    /// Type checks an input value.
    /// Returns an error if the value is not accepted by the operator.
    fn type_check(v: &Value) -> Result<(), ExecError> {
        check_number(v)
    }

    /// Returns whether a value is equal to an identity value.
    fn is_identity(_: &Value) -> bool { false }

    /// Folds the two constant values, returning the resulting value.
    fn fold(ctx: &Context, lhs: Value, rhs: &Value) -> Result<Value, Error>;

    /// Inverse fold operation; used for anticommutative operators.
    fn fold_inv(ctx: &Context, lhs: Value, rhs: &Value) -> Result<Value, Error> {
        Self::fold(ctx, lhs, rhs)
    }

    /// Finalizes a constant value when all arguments have been constant
    /// expressions.
    fn finish(value: Value) -> Result<Value, Error> { Ok(value) }
}

pub enum FoldAdd {}
pub enum FoldSub {}
pub enum FoldMul {}
pub enum FoldDiv {}
pub enum FoldFloorDiv {}
pub enum FoldBitAnd {}
pub enum FoldBitOr {}
pub enum FoldBitXor {}

impl FoldOp for FoldAdd {
    fn is_identity(v: &Value) -> bool { is_zero(v) }
    fn fold(ctx: &Context, lhs: Value, rhs: &Value) -> Result<Value, Error> {
        add_number(ctx, lhs, rhs)
    }
}

impl FoldOp for FoldSub {
    fn is_identity(v: &Value) -> bool { is_zero(v) }
    fn fold(ctx: &Context, lhs: Value, rhs: &Value) -> Result<Value, Error> {
        sub_number(ctx, lhs, rhs)
    }
    fn fold_inv(ctx: &Context, lhs: Value, rhs: &Value) -> Result<Value, Error> {
        add_number(ctx, lhs, rhs)
    }
}

impl FoldOp for FoldMul {
    fn is_identity(v: &Value) -> bool { is_one(v) }
    fn fold(ctx: &Context, lhs: Value, rhs: &Value) -> Result<Value, Error> {
        mul_number(ctx, lhs, rhs)
    }
}

impl FoldOp for FoldDiv {
    fn is_identity(v: &Value) -> bool { is_one(v) }
    fn fold(ctx: &Context, lhs: Value, rhs: &Value) -> Result<Value, Error> {
        div_number(ctx, lhs, rhs)
    }
    fn fold_inv(ctx: &Context, lhs: Value, rhs: &Value) -> Result<Value, Error> {
        mul_number(ctx, lhs, rhs)
    }
}

impl FoldOp for FoldFloorDiv {
    fn is_identity(v: &Value) -> bool { is_one(v) }

    fn fold(ctx: &Context, lhs: Value, rhs: &Value) -> Result<Value, Error> {
        floor_div_number_step(ctx, lhs, rhs)
    }

    fn fold_inv(ctx: &Context, lhs: Value, rhs: &Value) -> Result<Value, Error> {
        mul_number(ctx, lhs, rhs)
    }

    fn finish(value: Value) -> Result<Value, Error> {
        floor_number(value)
    }
}

impl FoldOp for FoldBitAnd {
    fn is_identity(v: &Value) -> bool { is_negative_one(v) }
    fn fold(_ctx: &Context, lhs: Value, rhs: &Value) -> Result<Value, Error> {
        bit_and_integer(lhs, rhs)
    }
}

impl FoldOp for FoldBitOr {
    fn is_identity(v: &Value) -> bool { is_zero(v) }
    fn fold(_ctx: &Context, lhs: Value, rhs: &Value) -> Result<Value, Error> {
        bit_or_integer(lhs, rhs)
    }
}

impl FoldOp for FoldBitXor {
    fn is_identity(v: &Value) -> bool { is_zero(v) }
    fn fold(_ctx: &Context, lhs: Value, rhs: &Value) -> Result<Value, Error> {
        bit_xor_integer(lhs, rhs)
    }
}

fn check_number(v: &Value) -> Result<(), ExecError> {
    match *v {
        Value::Float(_) | Value::Integer(_) | Value::Ratio(_) => Ok(()),
        ref v => Err(ExecError::expected("number", v))
    }
}

// Because of numeric coercion rules, only integer values can truly be
// "identity" values. That is, `(+ foo 0.0)` may result in transforming `foo`
// into a float value.

pub fn is_zero(v: &Value) -> bool {
    match *v {
        Value::Integer(ref i) => i.is_zero(),
        _ => false
    }
}

pub fn is_negative_one(v: &Value) -> bool {
    match *v {
        Value::Integer(ref i) => i.to_i32() == Some(-1),
        _ => false
    }
}

pub fn is_one(v: &Value) -> bool {
    match *v {
        Value::Integer(ref i) => i.is_one(),
        _ => false
    }
}
