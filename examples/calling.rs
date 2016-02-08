//! Basic demonstration of calling `ketos` functions from Rust.

extern crate ketos;

use ketos::{Interpreter, FromValueRef};

fn main() {
    // First, create an interpreter.
    let interp = Interpreter::new();

    // Run some code that defines a function.
    // This will insert the newly defined function into the interpreter scope.
    interp.run_code(r#"
        (define (factorial n)
          (cond
            ((< n 0) (panic "factorial got negative integer"))
            ((<= n 1) 1)
            (else (* n (factorial (- n 1))))))
        "#, None).unwrap();

    // Call the function by name, converting Rust values using the Into trait.
    let v = interp.call("factorial", vec![5.into()]).unwrap();

    // Convert back into a Rust value using the FromValueRef trait.
    let i = i32::from_value_ref(&v).unwrap();

    assert_eq!(i, 120);
    println!("(factorial 5) = {}", i);
}
