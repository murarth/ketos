//! Provides a facility for running code within an existing scope.

use std::rc::Rc;

use compile::compile;
use error::Error;
use exec::execute;
use lexer::Lexer;
use parser::Parser;
use scope::Scope;
use value::Value;

/// Parses, compiles, and executes the given code within a `Scope`.
pub fn run_code_in_scope(scope: &Scope, input: &str) -> Result<Value, Error> {
    let offset = scope.borrow_codemap_mut().add_source(input, None);

    let exprs = {
        let mut ns = scope.borrow_names_mut();
        let mut p = Parser::new(&mut ns, Lexer::new(input, offset));

        try!(p.parse_exprs())
    };

    let code: Vec<_> = try!(exprs.iter()
        .map(|v| compile(scope, v)).collect());

    let mut r = Value::Unit;

    for c in code {
        r = try!(execute(scope, Rc::new(c)));
    }

    Ok(r)
}

#[cfg(test)]
mod test {
    use interpreter::Interpreter;
    use value::Value;

    use super::run_code_in_scope;

    #[test]
    fn test_run_in_scope() {
        let interp = Interpreter::new();

        run_code_in_scope(interp.get_scope(), "(define foo ())").unwrap();

        assert_matches!(interp.get_value("foo"), Some(Value::Unit));
    }
}
