//! Example module construction

extern crate ketos;

use ketos::{
    Arity,
    Error,
    Interpreter,
    BuiltinModuleLoader, Module, ModuleBuilder, ModuleLoader,
    Name,
    GlobalScope, Scope,
    FromValue, FromValueRef, Value
};

fn main() {
    // Create an interpreter using our custom loader
    let interp = Interpreter::with_loader(Box::new(CustomModuleLoader));

    // Import our custom module and run the imported function
    let v = interp.run_code(r#"
        (use custom (hello))
        (hello "world")
        "#, None).unwrap();

    // Pull a String value out of the result
    let s = String::from_value(v).unwrap();

    assert_eq!(s, "Hello, world!");
    println!("{}", s);
}

#[derive(Debug)]
struct CustomModuleLoader;

impl ModuleLoader for CustomModuleLoader {
    fn load_module(&self, name: Name, scope: &Scope) -> Result<Module, Error> {
        let load_custom = scope.with_name(name, |name| name == "custom");

        if load_custom {
            Ok(load_mod(GlobalScope::new_using(scope)))
        } else {
            BuiltinModuleLoader.load_module(name, scope)
        }
    }
}

fn load_mod(scope: Scope) -> Module {
    ModuleBuilder::new("custom", scope)
        .add_function("hello", fn_hello, Arity::Exact(1))
        .finish()
}

fn fn_hello(_scope: &Scope, args: &mut [Value]) -> Result<Value, Error> {
    let a: &str = try!(FromValueRef::from_value_ref(&args[0]));

    Ok(format!("Hello, {}!", a).into())
}
