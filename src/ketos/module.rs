//! Implements loading named values from code modules.

use std::cell::RefCell;
use std::fs::{File, Metadata};
use std::io::{stderr, Read, Write};
use std::path::{Path, PathBuf};
use std::rc::Rc;

use bytecode::Code;
use compile::{compile, CompileError};
use encode::{DecodeError, read_bytecode_file, write_bytecode_file};
use error::Error;
use exec::{Context, execute};
use function::{Arity, Function, FunctionImpl, Lambda, SystemFn};
use io::{IoError, IoMode};
use lexer::Lexer;
use name::{Name, NameMap, NameSetSlice};
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
        Module{ name, scope }
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

    /// Adds a constant value to the module.
    pub fn add_constant<T: Into<Value>>(self, name: &str, value: T) -> Self {
        let name = self.scope.add_name(name);
        self.scope.add_constant(name, value.into());
        self
    }

    /// Adds a documentation string for the given name.
    pub fn add_doc(self, name: &str, doc: &str) -> Self {
        let name = self.scope.add_name(name);
        self.scope.add_doc_string(name, doc.to_owned());
        self
    }

    /// Adds a function to the module.
    pub fn add_function(self, name: &str,
            callback: FunctionImpl, arity: Arity, doc: Option<&'static str>) -> Self {
        self.add_value_with_name(name, |name| Value::Function(Function{
                name,
                sys_fn: SystemFn{
                    arity,
                    callback,
                    doc,
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
        let mut exports = Vec::new();

        self.scope.with_constants(
            |v| exports.extend(v.iter().map(|&(name, _)| name)));
        self.scope.with_macros(
            |v| exports.extend(v.iter().map(|&(name, _)| name)));
        self.scope.with_values(
            |v| exports.extend(v.iter().map(|&(name, _)| name)));

        self.scope.set_exports(exports.into_iter().collect());

        Module{
            name: self.name,
            scope: self.scope,
        }
    }
}

/// Contains code and data representing a compiled module
#[derive(Clone, Default)]
pub struct ModuleCode {
    /// Decoded `Code` objects
    pub code: Vec<Rc<Code>>,
    /// Exported names
    pub exports: NameSetSlice,
    /// Imported names
    pub imports: Vec<ImportSet>,
    /// Decoded constant values
    pub constants: Vec<(Name, Value)>,
    /// Decoded macro objects
    pub macros: Vec<(Name, Rc<Code>)>,
    /// Global values generated at compile time
    pub values: Vec<(Name, Value)>,
    /// Module doc strings
    pub module_doc: Option<String>,
    /// Doc strings
    pub docs: Vec<(Name, String)>,
}

impl ModuleCode {
    /// Creates a `ModuleCode` from a series of code objects and a `Scope`.
    ///
    /// Trivial code objects will be removed.
    pub fn new(mut code: Vec<Rc<Code>>, scope: &Scope) -> ModuleCode {
        fn is_lambda(v: &Value) -> bool {
            match *v {
                Value::Lambda(_) => true,
                _ => false
            }
        }

        code.retain(|code| !code.is_trivial());

        ModuleCode{
            code,
            constants: scope.with_constants(
                |consts| consts.iter().cloned().collect()),
            macros: scope.with_macros(
                |macros| macros.iter()
                    .map(|&(name, ref l)| (name, l.code.clone())).collect()),
            values: scope.with_values(
                |values| values.iter()
                    .filter(|&&(_, ref v)| is_lambda(v))
                    .filter(|&&(name, _)| !scope.is_imported(name))
                    .cloned().collect()),
            exports: scope.with_exports(|e| e.clone())
                .unwrap_or_else(NameSetSlice::default),
            imports: scope.with_imports(|i| i.to_vec()),
            module_doc: scope.with_module_doc(|d| d.to_owned()),
            docs: scope.with_docs(
                |d| d.iter().filter(|&&(name, _)| !scope.is_imported(name))
                    .cloned().collect()),
        }
    }

    /// Loads contained values into the given scope, which should be empty,
    /// and sequentially executes all contained code objects within the scope.
    pub fn load_in_context(self, ctx: &Context) -> Result<(), Error> {
        for (name, value) in self.constants {
            ctx.scope().add_constant(name, value);
        }

        for (name, code) in self.macros {
            let mac = Lambda::new(code, ctx.scope());
            ctx.scope().add_macro(name, mac);
        }

        for (name, value) in self.values {
            ctx.scope().add_value(name, value);
        }

        process_imports(ctx, &self.imports)?;

        ctx.scope().set_exports(self.exports);

        let mdoc = self.module_doc;
        ctx.scope().with_module_doc_mut(|d| *d = mdoc);
        let docs = self.docs;
        ctx.scope().with_docs_mut(|d| *d = docs.into_iter().collect());

        for code in self.code {
            execute(ctx, code)?;
        }

        Ok(())
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
            loader,
            modules: RefCell::new(NameMap::new()),
        }
    }

    /// Inserts a named module into the registry.
    pub fn add_module(&self, name: Name, module: Module) -> Option<Module> {
        self.modules.borrow_mut().insert(name, module)
    }

    /// Returns the named module, only if it is already loaded.
    pub fn get_module(&self, name: Name) -> Option<Module> {
        self.modules.borrow().get(name).cloned()
    }

    /// Returns a loaded module. If the module has not been loaded in this
    /// registry; the contained `ModuleLoader` instance will be used to load it.
    pub fn load_module(&self, name: Name, ctx: &Context) -> Result<Module, Error> {
        // It's not necessary to borrow_mut here, but it means that this
        // function has consistent behavior with respect to existing borrows.
        if let Some(m) = self.modules.borrow_mut().get(name).cloned() {
            return Ok(m);
        }

        // ... And the borrow_mut must be dropped before load_module is called.

        let new_scope = GlobalScope::new_using(name, ctx.scope());
        let new_ctx = ctx.with_scope(new_scope);

        let m = self.loader.load_module(name, new_ctx)?;
        self.modules.borrow_mut().insert(name, m.clone());

        Ok(m)
    }
}

/// Provides a method for loading modules into a running interpreter.
pub trait ModuleLoader {
    /// Loads the named module, supplying a new execution context.
    ///
    /// If the loader cannot load the named module, an error value should be
    /// returned of `Err(Error::CompileError(CompileError::ModuleError(name)))`.
    fn load_module(&self, name: Name, ctx: Context) -> Result<Module, Error>;

    /// Creates a `ChainModuleLoader` using this loader and another.
    ///
    /// The `ChainModuleLoader` will attempt to load a module first from `self`,
    /// falling back on the supplied `ModuleLoader` if it unable to find a
    /// module.
    fn chain<T: ModuleLoader>(self, second: T) -> ChainModuleLoader<Self, T>
            where Self: Sized {
        ChainModuleLoader{
            first: self,
            second,
        }
    }
}

/// Loads no modules.
pub struct NullModuleLoader;

impl ModuleLoader for NullModuleLoader {
    fn load_module(&self, name: Name, _ctx: Context) -> Result<Module, Error> {
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
    fn load_module(&self, name: Name, ctx: Context) -> Result<Module, Error> {
        match self.first.load_module(name, ctx.clone()) {
            // Check that the names match so we know that this module lookup
            // failed and not another contained module being imported.
            Err(Error::CompileError(CompileError::ModuleError(mname)))
                if mname == name => self.second.load_module(name, ctx),
            res => res
        }
    }
}

/// Loads builtin modules.
pub struct BuiltinModuleLoader;

impl ModuleLoader for BuiltinModuleLoader {
    fn load_module(&self, name: Name, ctx: Context) -> Result<Module, Error> {
        load_builtin_module(name, ctx.scope())
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

fn load_builtin_module(name: Name, scope: &Scope) -> Result<Module, Error> {
    let loader = scope.with_name(name, |name| get_loader(name));

    match loader {
        Some(l) => Ok(l(scope.clone())),
        None => Err(From::from(CompileError::ModuleError(name)))
    }
}

/// Loads modules from source files and compiled bytecode files.
pub struct FileModuleLoader {
    /// Tracks import chains to prevent infinite recursion
    chain: RefCell<Vec<PathBuf>>,
    /// Directories to search for files
    paths: Vec<PathBuf>,
    /// Whether to read bytecode files
    read_bytecode: bool,
    /// Whether to write out bytecode files
    write_bytecode: bool,
}

/// File extension for `ketos` source files.
pub const FILE_EXTENSION: &str = "ket";

/// File extension for `ketos` compiled bytecode files.
pub const COMPILED_FILE_EXTENSION: &str = "ketc";

impl Default for FileModuleLoader {
    /// Creates a new `FileModuleLoader` that will search the current
    /// directory for modules.
    fn default() -> FileModuleLoader {
        FileModuleLoader::with_search_paths(vec![PathBuf::new()])
    }
}

impl FileModuleLoader {
    /// Creates a new `FileModuleLoader` that will search the given series
    /// of directories to load modules.
    pub fn with_search_paths(paths: Vec<PathBuf>) -> FileModuleLoader {
        FileModuleLoader{
            chain: RefCell::new(Vec::new()),
            paths,
            read_bytecode: true,
            write_bytecode: true,
        }
    }

    /// Adds a directory to search for module files.
    pub fn add_search_path(&mut self, path: PathBuf) {
        self.paths.push(path);
    }

    /// Sets whether the `FileModuleLoader` will search for compiled bytecode
    /// files when loading modules. The default is `true`.
    pub fn set_read_bytecode(&mut self, set: bool) {
        self.read_bytecode = set;
    }

    /// Sets whether the `FileModuleLoader` will write compiled bytecode
    /// files after loading a module from source. The default is `true`.
    pub fn set_write_bytecode(&mut self, set: bool) {
        self.write_bytecode = set;
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
    fn load_module(&self, name: Name, ctx: Context) -> Result<Module, Error> {
        let (src_fname, code_fname) = ctx.scope().with_name(name, |name_str| {
            if name_str.chars().any(|c| c == '.' || c == '/' || c == '\\') {
                Err(CompileError::InvalidModuleName(name))
            } else {
                Ok((PathBuf::from(format!("{}.{}", name_str, FILE_EXTENSION)),
                    PathBuf::from(format!("{}.{}", name_str, COMPILED_FILE_EXTENSION))))
            }
        })?;

        for base in &self.paths {
            let src_path = base.join(&src_fname);
            let code_path = base.join(&code_fname);

            let load = if self.read_bytecode {
                find_module_file(&src_path, &code_path)?
            } else {
                find_source_file(&src_path)
            };

            match load {
                ModuleFileResult::UseCode => {
                    return self.guard_import(name, &src_path, || {
                        match read_bytecode_file(&code_path, &ctx) {
                            Ok(m) => {
                                m.load_in_context(&ctx)?;

                                Ok(Module{
                                    name,
                                    scope: ctx.scope().clone(),
                                })
                            }
                            Err(Error::DecodeError(DecodeError::IncorrectVersion(_)))
                                    if src_path.exists() => {
                                let code_path = if self.write_bytecode {
                                    Some(code_path.as_path())
                                } else {
                                    None
                                };

                                load_module_from_file(ctx, name,
                                    &src_path, code_path)
                            }
                            Err(e) => Err(e)
                        }
                    });
                }
                ModuleFileResult::UseSource => {
                    let code_path = if self.write_bytecode {
                        Some(code_path.as_path())
                    } else {
                        None
                    };

                    return self.guard_import(name, &src_path,
                        || load_module_from_file(ctx, name, &src_path, code_path))
                }
                ModuleFileResult::NotFound => ()
            }
        }

        Err(From::from(CompileError::ModuleError(name)))
    }
}

#[derive(Copy, Clone)]
enum ModuleFileResult {
    NotFound,
    UseCode,
    UseSource,
}

fn find_module_file(src_path: &Path, code_path: &Path) -> Result<ModuleFileResult, Error> {
    match (code_path.exists(), src_path.exists()) {
        (true, true) if is_younger(code_path, src_path)? =>
            Ok(ModuleFileResult::UseCode),
        (_, true) => Ok(ModuleFileResult::UseSource),
        (true, false) => Ok(ModuleFileResult::UseCode),
        (false, false) => Ok(ModuleFileResult::NotFound)
    }
}

fn find_source_file(src_path: &Path) -> ModuleFileResult {
    if src_path.exists() {
        ModuleFileResult::UseSource
    } else {
        ModuleFileResult::NotFound
    }
}

fn is_younger(a: &Path, b: &Path) -> Result<bool, Error> {
    let ma = a.metadata()
        .map_err(|e| IoError::new(IoMode::Stat, a, e))?;
    let mb = b.metadata()
        .map_err(|e| IoError::new(IoMode::Stat, b, e))?;

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

fn load_module_from_file(ctx: Context, name: Name,
        src_path: &Path, code_path: Option<&Path>) -> Result<Module, Error> {
    let mut file = File::open(src_path)
        .map_err(|e| IoError::new(IoMode::Open, src_path, e))?;
    let mut buf = String::new();

    file.read_to_string(&mut buf)
        .map_err(|e| IoError::new(IoMode::Read, src_path, e))?;

    let exprs = {
        let offset = ctx.scope().borrow_codemap_mut().add_source(&buf,
            Some(src_path.to_string_lossy().into_owned()));

        Parser::new(&ctx, Lexer::new(&buf, offset)).parse_exprs()?
    };

    let code = exprs.iter()
        .map(|e| compile(&ctx, e).map(Rc::new)).collect::<Result<Vec<_>, _>>()?;

    if let Some(code_path) = code_path {
        // Grab compile-time values before executing code
        let mcode = ModuleCode::new(code.clone(), ctx.scope());

        for code in &code {
            execute(&ctx, code.clone())?;
        }

        check_exports(ctx.scope(), name)?;

        let r = {
            let names = ctx.scope().borrow_names();
            write_bytecode_file(code_path, &mcode, &names)
        };

        if let Err(e) = r {
            let _ = writeln!(stderr(), "failed to write compiled bytecode: {}", e);
        }
    } else {
        for code in &code {
            execute(&ctx, code.clone())?;
        }

        check_exports(ctx.scope(), name)?;
    }

    Ok(Module{
        name,
        scope: ctx.scope().clone(),
    })
}

fn process_imports(ctx: &Context, imports: &[ImportSet]) -> Result<(), Error> {
    let mods = ctx.scope().modules();

    for imp in imports {
        let m = mods.load_module(imp.module_name, ctx)?;

        for &(src, dest) in &imp.names {
            if !m.scope.contains_name(src) {
                return Err(From::from(CompileError::ImportError{
                    module: imp.module_name,
                    name: src,
                }));
            } else if !m.scope.is_exported(src) {
                return Err(From::from(CompileError::PrivacyError{
                    module: imp.module_name,
                    name: src,
                }));
            }

            if let Some(v) = m.scope.get_constant(src) {
                // Store the remote constant as a runtime value in local scope.
                // The remote module may be changed without recompiling this
                // module; therefore, the value is not truly constant.
                ctx.scope().add_value(dest, v);
            }

            if let Some(v) = m.scope.get_macro(src) {
                ctx.scope().add_macro(dest, v);
            }

            if let Some(v) = m.scope.get_value(src) {
                ctx.scope().add_value(dest, v);
            }

            m.scope.with_doc(src, |d| ctx.scope().add_doc_string(dest, d.to_owned()));
        }
    }

    Ok(())
}

fn check_exports(scope: &Scope, mod_name: Name) -> Result<(), CompileError> {
    scope.with_exports(|exports| {
        for name in exports {
            if !scope.contains_name(name) {
                return Err(CompileError::ExportError{
                    module: mod_name,
                    name,
                });
            }
        }

        Ok(())
    }).ok_or(CompileError::MissingExport)
        .and_then(|r| r)
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
