//! Implements loading named values from code modules.

use std::cell::RefCell;
use std::fs::{File, Metadata};
use std::io::{stderr, Read, Write};
use std::path::{Path, PathBuf};
use std::rc::Rc;

use compile::{compile, CompileError};
use encode::{DecodeError, ModuleCode, read_bytecode_file, write_bytecode_file};
use error::Error;
use exec::execute;
use function::{Arity, Function, FunctionImpl, Lambda, SystemFn};
use io::{IoError, IoMode};
use lexer::Lexer;
use name::{Name, NameMap};
use parser::Parser;
use scope::{GlobalScope, ImportSet, Scope};
use value::Value;

use mod_code;
use mod_math;
use mod_random;

/// Contains the values in a loaded module's namespace.
#[derive(Clone)]
pub struct Module {
    /// Module name
    pub name: Name,
    /// Module scope
    pub scope: Scope,
}

impl Module {
    /// Creates a new module using the given scope.
    pub fn new(name: &str, scope: Scope) -> Module {
        let name = scope.add_name(name);
        Module{
            name: name,
            scope: scope,
        }
    }
}

/// Helper to build modules in Rust code.
#[must_use]
pub struct ModuleBuilder {
    name: Name,
    scope: Scope,
}

impl ModuleBuilder {
    /// Creates a new `ModuleBuilder` for the given scope.
    pub fn new(name: &str, scope: Scope) -> ModuleBuilder {
        let mod_name = scope.borrow_names_mut().add(name);

        ModuleBuilder{
            name: mod_name,
            scope: scope.clone(),
        }
    }

    /// Adds a function to the module.
    pub fn add_function(self, name: &str,
            callback: FunctionImpl, arity: Arity) -> Self {
        self.add_value_with_name(name, |name| Value::Function(Function{
                name: name,
                sys_fn: SystemFn{
                    arity: arity,
                    callback: callback,
                },
            }))
    }

    /// Adds a value to the module.
    pub fn add_value(self, name: &str, value: Value) -> Self {
        self.scope.add_named_value(name, value);
        self
    }

    /// Adds a value to the module using the generated name value.
    pub fn add_value_with_name<F>(self, name: &str, f: F) -> Self
            where F: FnOnce(Name) -> Value {
        self.scope.add_value_with_name(name, f);
        self
    }

    /// Consumes the builder and returns the new `Module`.
    pub fn finish(self) -> Module {
        let exports = self.scope.with_values(
            |v| v.iter().map(|&(name, _)| name).collect());

        self.scope.set_exports(exports);

        Module{
            name: self.name,
            scope: self.scope,
        }
    }
}

/// Loads modules into the running program and caches previously loaded modules
pub struct ModuleRegistry {
    loader: Box<ModuleLoader>,
    modules: RefCell<NameMap<Module>>,
}

impl ModuleRegistry {
    /// Creates a new `ModuleRegistry` using the given `ModuleLoader`
    /// to load new modules.
    pub fn new(loader: Box<ModuleLoader>) -> ModuleRegistry {
        ModuleRegistry{
            loader: loader,
            modules: RefCell::new(NameMap::new()),
        }
    }

    /// Returns a loaded module. If the module has not been loaded in this
    /// registry; the contained `ModuleLoader` instance will be used to load it.
    pub fn get_module(&self, name: Name, scope: &Scope) -> Result<Module, Error> {
        // It's not necessary to borrow_mut here, but it means that this
        // function has consistent behavior with respect to existing borrows.
        if let Some(m) = self.modules.borrow_mut().get(name).cloned() {
            return Ok(m);
        }

        // ... And the borrow_mut must be dropped before load_module is called.

        let m = try!(self.loader.load_module(name, scope));
        self.modules.borrow_mut().insert(name, m.clone());

        Ok(m)
    }
}

/// Loads modules into separate namespaces
pub trait ModuleLoader {
    /// Loads the named module.
    /// A new `Scope` should be created for the new module.
    fn load_module(&self, name: Name, scope: &Scope) -> Result<Module, Error>;

    /// Creates a `ChainModuleLoader` using this loader and another.
    fn chain<T>(self, second: T) -> ChainModuleLoader<Self, T>
            where Self: Sized {
        ChainModuleLoader{
            first: self,
            second: second,
        }
    }
}

/// Loads no modules.
pub struct NullModuleLoader;

impl ModuleLoader for NullModuleLoader {
    fn load_module(&self, name: Name, _scope: &Scope) -> Result<Module, Error> {
        Err(From::from(CompileError::ModuleError(name)))
    }
}

/// A chained module loader contains two `ModuleLoader` implementations.
///
/// It will attempt to load a module from the first loader and, if the loader
/// fails to find a module, it will attempt to load the module from the second
/// loader.
///
/// If the first module loader encounters an error while loading the desired
/// module (e.g. a compile error in a file), the chain loader will return the
/// error immediately, without attempting the second loader.
pub struct ChainModuleLoader<A, B> {
    first: A,
    second: B,
}

impl<A, B> ModuleLoader for ChainModuleLoader<A, B>
        where A: ModuleLoader, B: ModuleLoader {
    fn load_module(&self, name: Name, scope: &Scope) -> Result<Module, Error> {
        match self.first.load_module(name, scope) {
            // Check that the names match so we know that this module lookup
            // failed and not another contained module being imported.
            Err(Error::CompileError(CompileError::ModuleError(mname)))
                if mname == name => self.second.load_module(name, scope),
            res => res
        }
    }
}

/// Loads builtin modules.
pub struct BuiltinModuleLoader;

impl ModuleLoader for BuiltinModuleLoader {
    fn load_module(&self, name: Name, scope: &Scope) -> Result<Module, Error> {
        load_builtin_module(name, GlobalScope::new_using(scope))
    }
}

fn get_loader(name: &str) -> Option<fn(Scope) -> Module> {
    match name {
        "code" => Some(mod_code::load),
        "math" => Some(mod_math::load),
        "random" => Some(mod_random::load),
        _ => None
    }
}

fn load_builtin_module(name: Name, scope: Scope) -> Result<Module, Error> {
    let loader = scope.with_name(name, |name| get_loader(name));

    match loader {
        Some(l) => Ok(l(scope)),
        None => Err(From::from(CompileError::ModuleError(name)))
    }
}

/// Loads modules from a file.
///
/// If a module file is not found, it falls back to loading built-in modules.
pub struct FileModuleLoader {
    /// Tracks import chains to prevent infinite recursion
    chain: RefCell<Vec<PathBuf>>,
    /// Directories to search for files
    paths: Vec<PathBuf>,
}

/// File extension for `ketos` source files.
pub const FILE_EXTENSION: &'static str = "kts";

/// File extension for `ketos` compiled bytecode files.
pub const COMPILED_FILE_EXTENSION: &'static str = "ktsc";

impl FileModuleLoader {
    /// Creates a new `FileModuleLoader` that will search the current
    /// directory for modules.
    pub fn new() -> FileModuleLoader {
        FileModuleLoader::with_search_paths(vec![PathBuf::new()])
    }

    /// Creates a new `FileModuleLoader` that will search the given series
    /// of directories to load modules.
    pub fn with_search_paths(paths: Vec<PathBuf>) -> FileModuleLoader {
        FileModuleLoader{
            chain: RefCell::new(Vec::new()),
            paths: paths,
        }
    }

    /// Adds a directory to search for module files.
    pub fn add_search_path(&mut self, path: PathBuf) {
        self.paths.push(path);
    }

    fn guard_import<F, T>(&self, name: Name, path: &Path, f: F) -> Result<T, Error>
            where F: FnOnce() -> Result<T, Error> {
        if self.chain.borrow().iter().any(|p| p == path) {
            return Err(From::from(CompileError::ImportCycle(name)));
        }

        self.chain.borrow_mut().push(path.to_owned());
        let r = f();
        self.chain.borrow_mut().pop();

        r
    }
}

impl ModuleLoader for FileModuleLoader {
    fn load_module(&self, name: Name, scope: &Scope) -> Result<Module, Error> {
        let (src_fname, code_fname) = try!(scope.with_name(name, |name_str| {
            if name_str.chars().any(|c| c == '.' || c == '/' || c == '\\') {
                Err(CompileError::InvalidModuleName(name))
            } else {
                Ok((PathBuf::from(format!("{}.{}", name_str, FILE_EXTENSION)),
                    PathBuf::from(format!("{}.{}", name_str, COMPILED_FILE_EXTENSION))))
            }
        }));

        for base in &self.paths {
            let src_path = base.join(&src_fname);
            let code_path = base.join(&code_fname);

            match try!(find_module_file(&code_path, &src_path)) {
                ModuleFileResult::UseCode => {
                    let new_scope = GlobalScope::new_using(scope);

                    return self.guard_import(name, &src_path, || {
                        match read_bytecode_file(&code_path, &new_scope) {
                            Ok(m) => {
                                for &(name, ref code) in &m.macros {
                                    let mac = Lambda::new(code.clone(), &new_scope);
                                    new_scope.add_macro(name, mac);
                                }
                                try!(process_imports(&new_scope, &m.imports));
                                run_module_code(name, new_scope, m)
                            }
                            Err(Error::DecodeError(DecodeError::IncorrectVersion(_)))
                                    if src_path.exists() => {
                                load_module_from_file(new_scope, name, &src_path, &code_path)
                            }
                            Err(e) => Err(e)
                        }
                    });
                }
                ModuleFileResult::UseSource => {
                    let new_scope = GlobalScope::new_using(scope);

                    return self.guard_import(name, &src_path,
                        || load_module_from_file(new_scope, name, &src_path, &code_path))
                }
                ModuleFileResult::NotFound => ()
            }
        }

        let new_scope = GlobalScope::new_using(scope);

        load_builtin_module(name, new_scope)
    }
}

#[derive(Copy, Clone)]
enum ModuleFileResult {
    NotFound,
    UseCode,
    UseSource,
}

fn find_module_file(code_path: &Path, src_path: &Path) -> Result<ModuleFileResult, Error> {
    match (code_path.exists(), src_path.exists()) {
        (true, true) if try!(is_younger(code_path, src_path)) =>
            Ok(ModuleFileResult::UseCode),
        (_, true) => Ok(ModuleFileResult::UseSource),
        (true, false) => Ok(ModuleFileResult::UseCode),
        (false, false) => Ok(ModuleFileResult::NotFound)
    }
}

fn is_younger(a: &Path, b: &Path) -> Result<bool, Error> {
    let ma = try!(a.metadata()
        .map_err(|e| IoError::new(IoMode::Stat, a, e)));
    let mb = try!(b.metadata()
        .map_err(|e| IoError::new(IoMode::Stat, b, e)));

    Ok(is_younger_impl(&ma, &mb))
}

#[cfg(unix)]
fn is_younger_impl(ma: &Metadata, mb: &Metadata) -> bool {
    use std::os::unix::fs::MetadataExt;
    (ma.mtime(), ma.mtime_nsec()) > (mb.mtime(), mb.mtime_nsec())
}

#[cfg(windows)]
fn is_younger_impl(ma: &Metadata, mb: &Metadata) -> bool {
    use std::os::windows::fs::MetadataExt;
    ma.last_write_time() > mb.last_write_time()
}

fn load_module_from_file(scope: Scope, name: Name,
        src_path: &Path, code_path: &Path) -> Result<Module, Error> {
    let mut file = try!(File::open(src_path)
        .map_err(|e| IoError::new(IoMode::Open, src_path, e)));
    let mut buf = String::new();

    try!(file.read_to_string(&mut buf)
        .map_err(|e| IoError::new(IoMode::Read, src_path, e)));

    let exprs = {
        let mut names = scope.borrow_names_mut();
        let offset = scope.borrow_codemap_mut().add_source(&buf,
            Some(src_path.to_string_lossy().into_owned()));

        try!(Parser::new(&mut names, Lexer::new(&buf, offset)).parse_exprs())
    };

    let code = try!(exprs.iter()
        .map(|e| compile(&scope, e).map(Rc::new)).collect::<Result<Vec<_>, _>>());

    for code in &code {
        try!(execute(&scope, code.clone()));
    }

    try!(check_exports(&scope, name));

    let mcode = ModuleCode{
        code: code.clone(),
        macros: scope.with_macros(
            |macros| macros.iter()
                .map(|&(name, ref l)| (name, l.code.clone())).collect()),
        exports: scope.with_exports(|e| e.cloned().unwrap()),
        imports: scope.with_imports(|i| i.to_vec()),
    };

    let r = {
        let names = scope.borrow_names();
        write_bytecode_file(code_path, &mcode, &names)
    };

    if let Err(e) = r {
        let _ = writeln!(stderr(), "failed to write compiled bytecode: {}", e);
    }

    Ok(Module{
        name: name,
        scope: scope,
    })
}

fn process_imports(scope: &Scope, imports: &[ImportSet]) -> Result<(), Error> {
    let mods = scope.get_modules();

    for imp in imports {
        let m = try!(mods.get_module(imp.module_name, scope));

        for &(src, dest) in &imp.macros {
            let mac = try!(m.scope.get_macro(src)
                .ok_or(CompileError::ImportError{
                    module: imp.module_name,
                    name: src,
                }));

            scope.add_macro(dest, mac);
        }

        for &(src, dest) in &imp.values {
            let v = try!(m.scope.get_value(src)
                .ok_or(CompileError::ImportError{
                    module: imp.module_name,
                    name: src,
                }));

            scope.add_value(dest, v);
        }
    }

    Ok(())
}

fn run_module_code(name: Name, scope: Scope, mcode: ModuleCode) -> Result<Module, Error> {
    scope.set_exports(mcode.exports);

    for code in mcode.code {
        try!(execute(&scope, code));
    }

    Ok(Module{
        name: name,
        scope: scope,
    })
}

fn check_exports(scope: &Scope, mod_name: Name) -> Result<(), CompileError> {
    scope.with_exports(|exports| {
        if let Some(exports) = exports {
            for name in exports {
                if !(scope.contains_value(name) || scope.contains_macro(name)) {
                    return Err(CompileError::ExportError{
                        module: mod_name,
                        name: name,
                    });
                }
            }

            Ok(())
        } else {
            Err(CompileError::MissingExport)
        }
    })
}

#[cfg(test)]
mod test {
    use super::{ModuleLoader, BuiltinModuleLoader, NullModuleLoader};

    #[test]
    fn test_chain_loader() {
        let a = NullModuleLoader;
        let b = BuiltinModuleLoader;
        let _ = a.chain(b);
    }
}
