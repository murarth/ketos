//! Example module construction

#[macro_use] extern crate ketos;

use ketos::{
    CompileError,
    Context,
    Error,
    Interpreter,
    BuiltinModuleLoader, Module, ModuleLoader,
    Name,
    Scope,
    FromValue,
};

fn main() {
    // Create an interpreter using our custom loader
    let interp = Interpreter::with_loader(
        Box::new(CustomModuleLoader.chain(BuiltinModuleLoader)));

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
    fn load_module(&self, name: Name, ctx: Context) -> Result<Module, Error> {
        let load_custom = ctx.scope().with_name(name, |name| name == "custom");

        if load_custom {
            Ok(load_mod(ctx.scope()))
        } else {
            Err(From::from(CompileError::ModuleError(name)))
        }
    }
}

fn load_mod(scope: &Scope) -> Module {
    ketos_fn!{ scope => "hello" => fn hello(what: &str) -> String }

    Module::new("custom", scope.clone())
}

fn hello(what: &str) -> Result<String, Error> {
    Ok(format!("Hello, {}!", what))
}
