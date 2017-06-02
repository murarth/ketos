//! Defining a struct that can be constructed in Ketos

extern crate ketos;
#[macro_use] extern crate ketos_derive;

use ketos::{Interpreter, FromValue};

// Define a struct with necessary conversion traits
#[derive(Clone, Debug, ForeignValue, FromValueClone, StructValue)]
struct Thing {
    // Any type that implements `FromValue` can be a field.
    name: String,
    // A name containing underscores will appear with hyphens instead in Ketos.
    // This one would be `thing-count`.
    thing_count: u32,
    // Names can be explicitly specified using an attribute.
    #[ketos(rename = "type")]
    typ: String,
}

fn main() {
    // First, create the interpreter.
    let interp = Interpreter::new();

    // Before Ketos code can construct a Thing value, it needs to know about it.
    interp.scope().register_struct_value::<Thing>();

    // These structs are created just like Ketos-defined struct types,
    // using the `new` function.
    let value = interp.run_code(r#"
        (new Thing
            :name "thing-1"
            :thing-count 9000
            :type "thing")
        "#, None).unwrap();

    // Extract the `Thing` from the Ketos value.
    let thing = Thing::from_value(value).unwrap();

    println!("{:?}", thing);
}
