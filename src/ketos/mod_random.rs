//! Implements builtin `random` module.

use rand::{seq::SliceRandom, thread_rng, Rng};

use crate::error::Error;
use crate::exec::{Context, ExecError};
use crate::function::Arity::Exact;
use crate::module::{Module, ModuleBuilder};
use crate::scope::Scope;
use crate::value::Value;

/// Loads the `random` module into the given scope.
pub fn load(scope: Scope) -> Module {
    ModuleBuilder::new("random", scope)
        .add_function("random",  fn_random,  Exact(0),
            Some("Returns a random float value in the range `[0.0, 1.0)`."))
        .add_function("shuffle", fn_shuffle, Exact(1),
            Some("Given a list, returns a new list with the elements shuffled."))
        .finish()
}

/// `random` returns a random float value in the range `[0.0, 1.0)`.
fn fn_random(_ctx: &Context, _args: &mut [Value]) -> Result<Value, Error> {
    let value: f64 = thread_rng().gen();
    Ok(value.into())
}

/// `shuffle` shuffles the values of a list.
fn fn_shuffle(_ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    let mut v = args[0].take();

    match v {
        Value::Unit => (),
        Value::List(ref mut li) => li.shuffle(&mut thread_rng()),
        ref v => return Err(From::from(ExecError::expected("list", v)))
    }

    Ok(v)
}
