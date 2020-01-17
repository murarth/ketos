//! Implements builtin `random` module.

use chrono::offset::{Utc, Local};

use crate::error::Error;
use crate::exec::Context;
use crate::function::Arity::Exact;
use crate::module::{Module, ModuleBuilder};
use crate::scope::Scope;
use crate::value::Value;

/// Loads the `random` module into the given scope.
pub fn load(scope: Scope) -> Module {
    ModuleBuilder::new("time", scope)
        .add_function("utc-timestamp",  fn_utc_timestamp,  Exact(0),
            Some("Returns the number of non-leap seconds observed in the UTC timezone since January 1st 1970."))
        .add_function("local-timestamp",  fn_local_timestamp,  Exact(0),
            Some("Returns the number of non-leap seconds observed in the local timezone since January 1st 1970."))
        .finish()
}

/// `utc-timestamp` the number of non-leap seconds observed in the UTC timezone since January 1st 1970.
fn fn_utc_timestamp(_ctx: &Context, _args: &mut [Value]) -> Result<Value, Error> {
    let time = Utc::now().timestamp();
    Ok(time.into())
}

/// `utc-timestamp` the number of non-leap seconds observed in the local timezone since January 1st 1970.
fn fn_local_timestamp(_ctx: &Context, _args: &mut [Value]) -> Result<Value, Error> {
    let time = Local::now().timestamp();
    Ok(time.into())
}
