//! Implements builtin `math` module.

use std::f64::consts;

use error::Error;
use exec::{Context, ExecError};
use function::Arity::Exact;
use module::{Module, ModuleBuilder};
use scope::Scope;
use value::Value;

/// Loads the `math` module into the given scope.
pub fn load(scope: Scope) -> Module {
    ModuleBuilder::new("math", scope)
        .add_constant("e",          consts::E)
        .add_doc     ("e",  "Euler's number")
        .add_constant("pi",         consts::PI)
        .add_doc     ("pi", "The ratio of a circle's circumference to its diameter")
        .add_function("acos",       fn_acos,    Exact(1), Some("\
Computes the arctangent of a number.
Return value is in radians in the range `[-pi/2, pi/2]`."))
        .add_function("acosh",      fn_acosh,   Exact(1),
            Some("Inverse hyperbolic cosine function."))
        .add_function("asin",       fn_asin,    Exact(1), Some("\
Computes the arcsine of a number.
Return value is in radians in the range `[-pi/2, pi/2]` or `NaN`
if the number is outside the range `[-1, 1]`."))
        .add_function("asinh",      fn_asinh,   Exact(1),
            Some("Inverse hyperbolic sine function"))
        .add_function("atan",       fn_atan,    Exact(1), Some("\
Computes the arctangent of a number.
Return value is in radians in the range `[-pi/2, pi/2]`."))
        .add_function("atanh",      fn_atanh,   Exact(1),
            Some("Inverse hyperbolic tangent function."))
        .add_function("atan2",      fn_atan2,   Exact(2), Some("\
    (atan2 y x)

Computes the four quadrant arctangent of `y` and `x`.

* `x = 0`, `y = 0`: `0`
* `x >= 0`: `arctan(y/x)` -> `[-pi/2, pi/2]`
* `y >= 0`: `arctan(y/x) + pi` -> `(pi/2, pi]`
* `y < 0`: `arctan(y/x) - pi` -> `(-pi, -pi/2)`"))
        .add_function("cos",        fn_cos,     Exact(1),
            Some("Computes the cosine of a number, in radians."))
        .add_function("cosh",       fn_cosh,    Exact(1),
            Some("Hyperbolic cosine function."))
        .add_function("degrees",    fn_degrees, Exact(1),
            Some("Converts a value in radians to degrees."))
        .add_function("ln",         fn_ln,      Exact(1),
            Some("Returns the natural logarithm of a number."))
        .add_function("log",        fn_log,     Exact(2), Some("\
    (log n base)

Returns the logarithm of a number with respect to an arbitrary base."))
        .add_function("log2",       fn_log2,    Exact(1), Some("\
Returns the base 2 logarithm of a number."))
        .add_function("log10",      fn_log10,   Exact(1), Some("\
Returns the base 10 logarithm of a number."))
        .add_function("radians",    fn_radians, Exact(1),
            Some("Converts a value in degrees to radians."))
        .add_function("sin",        fn_sin,     Exact(1),
            Some("Computes the sine of a number, in radians."))
        .add_function("sinh",       fn_sinh,    Exact(1),
            Some("Hyperbolic sine function."))
        .add_function("sqrt",       fn_sqrt,    Exact(1), Some("\
Returns the square root of a number.
Returns `NaN` if the number is negative."))
        .add_function("tan",        fn_tan,     Exact(1),
            Some("Computes the tangent of a number, in radians."))
        .add_function("tanh",       fn_tanh,    Exact(1),
            Some("Hyperbolic tangent function"))
        .finish()
}

/// `acos` returns the arccosine of a number. Return value is in radians
/// in the range `[0, pi]` or `NaN` if the number is outside the range `[-1, 1]`.
fn fn_acos(_ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    let f = get_float(&args[0])?;
    Ok(f.acos().into())
}

/// `acosh` is the inverse hyperbolic cosine.
fn fn_acosh(_ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    let f = get_float(&args[0])?;
    Ok(f.acosh().into())
}

/// `asin` returns the arcsine of a number. Return value is in radians
/// in the range `[-pi/2, pi/2]` or `NaN` if the number is outside the range
/// `[-1, 1]`.
fn fn_asin(_ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    let f = get_float(&args[0])?;
    Ok(f.asin().into())
}

/// `asinh` is the inverse hyperbolic sine function.
fn fn_asinh(_ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    let f = get_float(&args[0])?;
    Ok(f.asinh().into())
}

/// `atan` returns the arctangent of a number. Return value is in the range
/// `[-pi/2, pi/2]`.
fn fn_atan(_ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    let f = get_float(&args[0])?;
    Ok(f.atan().into())
}

/// `atanh` is the inverse hyperbolic tangent function.
fn fn_atanh(_ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    let f = get_float(&args[0])?;
    Ok(f.atanh().into())
}

/// `atan2` computes the four quadrant arctangent of `y` and `x`.
fn fn_atan2(_ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    let fa = get_float(&args[0])?;
    let fb = get_float(&args[1])?;
    Ok(fa.atan2(fb).into())
}

/// `cos` computes the cosine of a number, in radians.
fn fn_cos(_ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    let f = get_float(&args[0])?;
    Ok(f.cos().into())
}

/// `cosh` is the hyperbolic cosine function.
fn fn_cosh(_ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    let f = get_float(&args[0])?;
    Ok(f.cosh().into())
}

/// `degrees` converts a value in radians to the equivalent value in degrees.
fn fn_degrees(_ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    let f = get_float(&args[0])?;
    Ok(f.to_degrees().into())
}

/// `ln` returns the natural logarithm of a number.
fn fn_ln(_ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    let f = get_float(&args[0])?;
    Ok(f.ln().into())
}

/// `log` returns the logarithm of a number with respect to an arbitrary base.
fn fn_log(_ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    let f = get_float(&args[0])?;
    let base = get_float(&args[1])?;
    Ok(f.log(base).into())
}

/// `log2` returns the base 2 logarithm of a number.
fn fn_log2(_ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    let f = get_float(&args[0])?;
    Ok(f.log2().into())
}

/// `log10` returns the base 10 logarithm of a number.
fn fn_log10(_ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    let f = get_float(&args[0])?;
    Ok(f.log10().into())
}

/// `radians` converts a value in degrees to the equivalent value in radians.
fn fn_radians(_ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    let f = get_float(&args[0])?;
    Ok(f.to_radians().into())
}

/// `sin` computes the sine of a number, in radians.
fn fn_sin(_ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    let f = get_float(&args[0])?;
    Ok(f.sin().into())
}

/// `sinh` is the hyperbolic sine function.
fn fn_sinh(_ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    let f = get_float(&args[0])?;
    Ok(f.sinh().into())
}

/// `sqrt` returns the square root of the given value.
fn fn_sqrt(_ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    let f = get_float(&args[0])?;
    Ok(f.sqrt().into())
}

/// `tan` computes the tangent of a number, in radians.
fn fn_tan(_ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    let f = get_float(&args[0])?;
    Ok(f.tan().into())
}

/// `tanh` is the hyperbolic tangent function.
fn fn_tanh(_ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    let f = get_float(&args[0])?;
    Ok(f.tanh().into())
}

fn get_float(v: &Value) -> Result<f64, ExecError> {
    match *v {
        Value::Float(f) => Ok(f),
        Value::Integer(ref i) => i.to_f64().ok_or(ExecError::Overflow),
        Value::Ratio(ref r) => r.to_f64().ok_or(ExecError::Overflow),
        ref v => Err(ExecError::expected("number", v))
    }
}
