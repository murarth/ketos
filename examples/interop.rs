//! Demonstrates interoperation -- calling methods on Rust values from Ketos

#[macro_use] extern crate ketos;

use std::cell::Cell;
use std::rc::Rc;

use ketos::{Error, ForeignValue, Interpreter, Value};

/// A simple structure that says "Hello."
#[derive(Debug)]
pub struct Hello {
    who: String,
}

impl Hello {
    /// Creates a new `Hello` to say "Hello" to `who`.
    pub fn new(who: String) -> Hello {
        Hello{who: who}
    }

    /// Returns a string saying "Hello" to someone.
    pub fn say_hello(&self) -> String {
        format!("Hello, {}!", self.who)
    }
}

impl ForeignValue for Hello {
    fn type_name(&self) -> &'static str { "Hello" }
}

// Implements `FromValueRef` for Hello.
// This implementation is used by the `ketos_fn!` generated wrappers.
foreign_type_conversions!{Hello => "Hello"}

/// Contains an internal counter
#[derive(Debug)]
pub struct Counter {
    // Sharing a value with Ketos means we can only access it through `&self`.
    // Mutation of values is possible through internally mutable containers,
    // such as `Cell` and `RefCell`.
    count: Cell<u32>,
}

impl Counter {
    /// Creates a new `Counter` with counter value `0`.
    pub fn new() -> Counter {
        Counter{count: Cell::new(0)}
    }

    /// Increments the internal counter and returns the previous value.
    pub fn count(&self) -> u32 {
        let old = self.count.get();
        self.count.set(old + 1);
        old
    }
}

impl ForeignValue for Counter {
    fn type_name(&self) -> &'static str { "Counter" }
}

foreign_type_conversions!{Counter => "Counter"}

// Ketos wrapper for `Hello::say_hello`
fn say_hello(hello: &Hello) -> Result<String, Error> {
    Ok(hello.say_hello())
}

// Ketos wrapper for `Counter::count`
fn count(counter: &Counter) -> Result<u32, Error> {
    Ok(counter.count())
}

fn main() {
    // First, create an interpreter.
    let interp = Interpreter::new();

    // Create a shared `Hello` value.
    let hello = Rc::new(Hello::new("world".into()));

    // Create a shared `Counter` value.
    let counter = Rc::new(Counter::new());

    // Inserts wrapper functions into the global scope.
    ketos_fn!{ interp.scope() => "count" =>
        fn count(counter: &Counter) -> u32 }
    ketos_fn!{ interp.scope() => "say-hello" =>
        fn say_hello(hello: &Hello) -> String }

    // Defines a `main` function within the global scope to accept our values.
    interp.run_code(r#"
        (define (main hello counter)
          (do
            (println "Hello from Ketos: ~a" (say-hello hello))
            (println "Count from Ketos: ~a" (count counter))))
        "#, None).unwrap();

    interp.call("main", vec![
        Value::Foreign(hello.clone()),
        Value::Foreign(counter.clone()),
    ]).unwrap();

    println!("Hello from Rust: {}", hello.say_hello());
    println!("Count from Rust: {}", counter.count());
}
