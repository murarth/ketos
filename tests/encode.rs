#[macro_use] extern crate assert_matches;
extern crate ketos;

use std::path::{Path, PathBuf};
use std::rc::Rc;

use ketos::{Error, Interpreter, Scope, Value, run_code_in_scope};
use ketos::encode::{read_bytecode, write_bytecode};
use ketos::module::ModuleCode;

// Runs `F` twice; first, after compiling and executing input;
// then, after encoding and decoding and loading the resulting ModuleCode.
fn run<F>(input: &str, mut f: F) -> Result<(), Error>
        where F: FnMut(&Scope) {
    let interp = Interpreter::with_search_paths(vec![PathBuf::from("lib")]);

    let code: Vec<_> = try!(interp.compile_exprs(input))
        .into_iter().map(Rc::new).collect();

    for code in &code {
        try!(interp.execute_code(code.clone()));
    }

    f(interp.get_scope());

    let mut buf = Vec::new();
    let path = Path::new("<buffer>");

    {
        let mcode = ModuleCode::new(code, interp.get_scope());
        let scope = interp.get_scope();
        let names = scope.borrow_names();
        try!(write_bytecode(&mut buf, path, &mcode, &names));
    }

    let sec_interp = Interpreter::with_search_paths(vec![PathBuf::from("lib")]);
    let mcode = try!(read_bytecode(&mut &buf[..], path, sec_interp.get_scope()));

    try!(mcode.load_in_scope(sec_interp.get_scope()));

    f(sec_interp.get_scope());

    Ok(())
}

#[test]
fn test_encode() {
    run(r#"
        (const foo 1)
        (define bar 2)
        "#, |scope| {
            assert_matches!(scope.get_named_constant("foo"),
                Some(Value::Integer(ref i)) if i.to_u32() == Some(1));
            assert_matches!(scope.get_named_value("bar"),
                Some(Value::Integer(ref i)) if i.to_u32() == Some(2));
        }).unwrap();
}

#[test]
fn test_docs() {
    run(r#"
        (const foo
            "foo doc"
            1)
        (define bar
            "bar doc"
            2)
        (define (baz)
            "baz doc"
            3)
        (macro (mac)
            "mac doc"
            ())
        (struct struc
            "struc doc"
            ())
        "#, |scope| {
            run_code_in_scope(scope,
                r#"
                (use code (documentation))
                (use test (assert-eq))

                (assert-eq (documentation 'foo) "foo doc")
                (assert-eq (documentation 'bar) "bar doc")
                (assert-eq (documentation 'baz) "baz doc")
                (assert-eq (documentation 'mac) "mac doc")
                (assert-eq (documentation 'struc) "struc doc")
                "#).unwrap();
        }).unwrap();
}
