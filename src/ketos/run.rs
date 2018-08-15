//! Provides a facility for running code within an existing scope.

use std::rc::Rc;

use compile::compile;
use error::Error;
use exec::{Context, execute};
use lexer::Lexer;
use parser::Parser;
use value::Value;

/// Parses, compiles, and executes the given code within a context.
pub fn run_code(ctx: &Context, input: &str) -> Result<Value, Error> {
    let offset = ctx.scope().borrow_codemap_mut().add_source(input, None);

    let exprs = {
        let mut p = Parser::new(ctx, Lexer::new(input, offset));

        p.parse_exprs()?
    };

    let code = exprs.iter()
        .map(|v| compile(ctx, v))
        .collect::<Result<Vec<_>, _>>()?;

    let mut r = Value::Unit;

    for c in code {
        r = execute(ctx, Rc::new(c))?;
    }

    Ok(r)
}

#[cfg(test)]
mod test {
    use interpreter::Interpreter;
    use value::Value;

    use super::run_code;

    #[test]
    fn test_run() {
        let interp = Interpreter::new();

        run_code(interp.context(), "(define foo ())").unwrap();

        assert_matches!(interp.get_value("foo"), Some(Value::Unit));
    }
}
