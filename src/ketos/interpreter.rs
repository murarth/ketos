//! Provides a context in which to compile and execute code.

use std::cell::RefCell;
use std::fs::File;
use std::io::{stderr, Read, Write};
use std::path::{Path, PathBuf};
use std::rc::Rc;

use crate::bytecode::Code;
use crate::compile::compile;
use crate::error::Error;
use crate::exec::{call_function, execute, Context, ExecError};
use crate::io::{GlobalIo, IoError, IoMode};
use crate::lexer::{CodeMap, Lexer};
use crate::module::{BuiltinModuleLoader, FileModuleLoader, ModuleLoader, ModuleRegistry};
use crate::name::{debug_names, display_names, NameStore};
use crate::parser::{ParseError, Parser};
use crate::restrict::RestrictConfig;
use crate::scope::{GlobalScope, Scope};
use crate::structs::{StructDefMap};
use crate::trace::{get_traceback, take_traceback, Trace};
use crate::value::Value;

/// Builds an `Interpreter` with configured parameters.
///
/// Some methods are mutually exclusive. For example, a `Scope` contains a
/// `ModuleLoader` instance. Therefore, the builder will panic if both
/// a `Scope` and a `ModuleLoader` are supplied.
///
/// # Example
///
/// ```
/// # use ketos::Builder;
///
/// let interp = Builder::new()
///     .name("foo")
///     // ...
///     .finish();
///
/// # let _ = interp;
/// // ...
/// ```
pub struct Builder {
    name: Option<&'static str>,
    context: Option<Context>,
    scope: Option<Scope>,
    restrict: Option<RestrictConfig>,
    io: Option<Rc<GlobalIo>>,
    struct_defs: Option<Rc<RefCell<StructDefMap>>>,
    module_loader: Option<Box<dyn ModuleLoader>>,
    search_paths: Option<Vec<PathBuf>>,
}

macro_rules! exclude {
    ( $field:expr , $this:expr , $that:expr ) => {
        assert!($field.is_none(),
            concat!("`Builder::", $this, "` and `Builder::", $that,
                "` are mutually exclusive"))
    }
}

impl Builder {
    /// Creates a new `Builder`.
    pub fn new() -> Builder {
        Builder{
            name: None,
            context: None,
            scope: None,
            restrict: None,
            io: None,
            struct_defs: None,
            module_loader: None,
            search_paths: None,
        }
    }

    /// Sets the name of the new scope.
    pub fn name(mut self, name: &'static str) -> Self {
        exclude!(self.context, "name", "context");
        exclude!(self.scope, "name", "scope");

        self.name = Some(name);
        self
    }

    /// Sets the context of the new interpreter.
    pub fn context(mut self, ctx: Context) -> Self {
        exclude!(self.name, "context", "name");
        exclude!(self.scope, "context", "scope");
        exclude!(self.restrict, "context", "restrict");
        exclude!(self.io, "context", "io");
        exclude!(self.module_loader, "context", "module_loader");
        exclude!(self.search_paths, "context", "search_paths");

        self.context = Some(ctx);
        self
    }

    /// Sets the restriction configuration in the new context.
    pub fn restrict(mut self, restrict: RestrictConfig) -> Self {
        exclude!(self.context, "restrict", "context");

        self.restrict = Some(restrict);
        self
    }

    /// Sets the scope in the new context.
    pub fn scope(mut self, scope: Scope) -> Self {
        exclude!(self.name, "scope", "name");
        exclude!(self.context, "scope", "context");
        exclude!(self.io, "scope", "io");
        exclude!(self.module_loader, "scope", "module_loader");
        exclude!(self.search_paths, "scope", "search_paths");

        self.scope = Some(scope);
        self
    }

    /// Sets the struct definitions in the new context.
    pub fn struct_defs(mut self, defs: Rc<RefCell<StructDefMap>>) -> Self {
        exclude!(self.context, "struct_defs", "context");
        exclude!(self.scope, "struct_defs", "scope");

        self.struct_defs = Some(defs);
        self
    }

    /// Sets the I/O handles in the new scope.
    pub fn io(mut self, io: Rc<GlobalIo>) -> Self {
        exclude!(self.context, "io", "context");
        exclude!(self.scope, "io", "scope");

        self.io = Some(io);
        self
    }

    /// Sets the module loader in the new scope.
    pub fn module_loader(mut self, loader: Box<dyn ModuleLoader>) -> Self {
        exclude!(self.context, "module_loader", "context");
        exclude!(self.scope, "module_loader", "scope");
        exclude!(self.search_paths, "module_loader", "search_paths");

        self.module_loader = Some(loader);
        self
    }

    /// Sets the search paths for a new `FileModuleLoader`.
    pub fn search_paths(mut self, paths: Vec<PathBuf>) -> Self {
        exclude!(self.context, "search_paths", "context");
        exclude!(self.scope, "search_paths", "scope");
        exclude!(self.module_loader, "search_paths", "module_loader");

        self.search_paths = Some(paths);
        self
    }

    /// Consumes the `Builder` and creates an `Interpreter`.
    pub fn finish(self) -> Interpreter {
        Interpreter::with_context(self.build_context())
    }

    fn build_context(mut self) -> Context {
        match self {
            Builder{context: Some(ctx), ..} => ctx,
            Builder{scope: Some(scope), ..} =>
                Context::new(scope,
                    self.restrict.unwrap_or_else(RestrictConfig::permissive)),
            _ => Context::new(self.build_scope(),
                self.restrict.unwrap_or_else(RestrictConfig::permissive))
        }
    }

    fn build_scope(&mut self) -> Scope {
        let loader = self.build_loader();

        let mut names = NameStore::new();
        let name = names.add(self.name.unwrap_or("main"));

        let names = Rc::new(RefCell::new(names));
        let codemap = Rc::new(RefCell::new(CodeMap::new()));
        let modules = Rc::new(ModuleRegistry::new(loader));
        let io = self.io.take().unwrap_or_else(|| Rc::new(GlobalIo::default()));
        let defs = self.struct_defs.take().unwrap_or_else(
            || Rc::new(RefCell::new(StructDefMap::new())));

        Rc::new(GlobalScope::new(name, names, codemap, modules, io, defs))
    }

    fn build_loader(&mut self) -> Box<dyn ModuleLoader> {
        match (self.module_loader.take(), self.search_paths.take()) {
            (Some(loader), _) => loader,
            (None, Some(paths)) =>
                Box::new(BuiltinModuleLoader.chain(
                    FileModuleLoader::with_search_paths(paths))),
            (None, None) => Box::new(BuiltinModuleLoader)
        }
    }
}

/// Provides a context in which to compile and execute code.
///
/// Values created by one interpreter are exclusive to that interpreter.
/// They should not be passed directly into another interpreter.
/// Specifically, unexpected behavior or a panic may occur if another
/// interpreter attempts to operate on `Name`/`Keyword` values created by
/// another interpreter or any values which may contain arbitrary values
/// (`Struct`, `StructDef`, `List`, `Lambda`, `Quote`, etc.).
#[derive(Clone)]
pub struct Interpreter {
    context: Context,
}

impl Interpreter {
    /// Creates a new `Interpreter`.
    pub fn new() -> Interpreter {
        Interpreter::with_loader(Box::new(BuiltinModuleLoader))
    }

    /// Creates a new `Interpreter` using the given `ModuleLoader` instance.
    pub fn with_loader(loader: Box<dyn ModuleLoader>) -> Interpreter {
        let mut names = NameStore::new();
        let name = names.add("main");

        let names = Rc::new(RefCell::new(names));
        let codemap = Rc::new(RefCell::new(CodeMap::new()));
        let modules = Rc::new(ModuleRegistry::new(loader));
        let io = Rc::new(GlobalIo::default());
        let defs = Rc::new(RefCell::new(StructDefMap::new()));

        Interpreter::with_scope(
            Rc::new(GlobalScope::new(
                name,
                names.clone(),
                codemap.clone(),
                modules,
                io,
                defs)))
    }

    /// Creates a new `Interpreter` using the given `Context` instance.
    pub fn with_context(context: Context) -> Interpreter {
        Interpreter{ context }
    }

    /// Creates a new `Interpreter` using the given `Scope` instance.
    pub fn with_scope(scope: Scope) -> Interpreter {
        Interpreter::with_context(Context::new(
            scope, RestrictConfig::permissive()))
    }

    /// Creates a new `Interpreter` that searches for module files in a given
    /// series of directories.
    pub fn with_search_paths(paths: Vec<PathBuf>) -> Interpreter {
        Interpreter::with_loader(Box::new(
            BuiltinModuleLoader.chain(FileModuleLoader::with_search_paths(paths))))
    }

    /// Clears cached source from the contained `CodeMap`.
    ///
    /// # Note
    ///
    /// This will invalidate any previously created `ParseError` values.
    pub fn clear_codemap(&self) {
        self.scope().borrow_codemap_mut().clear();
    }

    /// Prints an error to `stderr`.
    pub fn display_error(&self, e: &Error) {
        let s = self.format_error(e);
        let _ = writeln!(stderr(), "{}", s);
    }

    /// Prints traceback information to `stderr`.
    pub fn display_trace(&self, trace: &Trace) {
        let _ = writeln!(stderr(), "Traceback:\n\n{}",
            display_names(&self.scope().borrow_names(), trace));
    }

    fn format_parse_error(&self, e: &ParseError) -> String {
        use std::fmt::Write;

        let codemap = self.scope().borrow_codemap();
        let hi = codemap.highlight_span(e.span);

        let mut res = String::with_capacity(32);

        let _ = writeln!(res, "{}:{}:{}:parse error: {}",
            hi.filename.unwrap_or("<input>"), hi.line, hi.col, e.kind);
        let _ = writeln!(res, "    {}", hi.source);
        let _ = write!  (res, "    {}", hi.highlight);

        res
    }

    /// Prints a string representation of a value to `stdout`.
    pub fn display_value(&self, value: &Value) {
        println!("{}", debug_names(&self.scope().borrow_names(), value));
    }

    /// Formats an error into a `String`.
    pub fn format_error(&self, e: &Error) -> String {
        match *e {
            Error::ParseError(ref e) => self.format_parse_error(e),
            ref e => format!("{}: {}", e.description(),
                display_names(&self.scope().borrow_names(), e))
        }
    }

    /// Formats a `Trace` into a `String`.
    ///
    /// The result does *not* include the `"Traceback:"` preamble.
    pub fn format_trace(&self, trace: &Trace) -> String {
        display_names(&self.scope().borrow_names(), trace).to_string()
    }

    /// Returns the traceback from the most recent error.
    ///
    /// The traceback will remain stored for future calls to `get_traceback`.
    pub fn get_traceback(&self) -> Option<Trace> {
        get_traceback()
    }

    /// Removes and returns the traceback from the most recent error.
    pub fn take_traceback(&self) -> Option<Trace> {
        take_traceback()
    }

    /// Formats a value into a string.
    pub fn format_value(&self, value: &Value) -> String {
        debug_names(&self.scope().borrow_names(), value).to_string()
    }

    /// Executes a bare `Code` object taking no parameters.
    pub fn execute(&self, code: Code) -> Result<Value, Error> {
        self.execute_code(Rc::new(code))
    }

    /// Executes a `Rc<Code>` object taking no parameters.
    pub fn execute_code(&self, code: Rc<Code>) -> Result<Value, Error> {
        let v = execute(&self.context, code)?;
        Ok(v)
    }

    /// Executes a series of code objects sequentially and returns the value
    /// of the final expression. If `code` is empty, the value `()` is returned.
    pub fn execute_program(&self, code: Vec<Code>) -> Result<Value, Error> {
        let mut last_v = Value::Unit;

        for c in code {
            last_v = self.execute(c)?;
        }

        Ok(last_v)
    }

    /// Calls a named function with the given arguments.
    pub fn call(&self, name: &str, args: Vec<Value>) -> Result<Value, Error> {
        let name = self.scope().borrow_names_mut().add(name);

        let v = self.scope().get_value(name).ok_or_else(|| ExecError::NameError(name))?;
        self.call_value(v, args)
    }

    /// Calls a function with the given arguments.
    pub fn call_value(&self, value: Value, args: Vec<Value>) -> Result<Value, Error> {
        let v = call_function(&self.context, value, args)?;
        Ok(v)
    }

    fn call_main(&self) -> Result<(), Error> {
        if let Some(v) = self.get_value("main") {
            self.call_value(v, Vec::new())?;
        }
        Ok(())
    }

    /// Returns a value, if present, in the interpreter scope.
    pub fn get_value(&self, name: &str) -> Option<Value> {
        self.scope().get_named_value(name)
    }

    /// Returns a borrowed reference to the contained context.
    pub fn context(&self) -> &Context {
        &self.context
    }

    /// Returns a borrowed reference to the contained scope.
    pub fn scope(&self) -> &Scope {
        self.context.scope()
    }

    /// Sets the value of `argv` within the execution scope.
    pub fn set_args<T: AsRef<str>>(&self, args: &[T]) {
        let args = args.iter()
            .map(|s| s.as_ref().into())
            .collect::<Vec<Value>>();

        self.scope().add_named_value("argv", args.into());
    }

    /// Compiles and executes the contents of a file.
    pub fn run_file(&self, path: &Path) -> Result<(), Error> {
        let mut f = File::open(path)
            .map_err(|e| IoError::new(IoMode::Open, path, e))?;

        let mut buf = String::new();

        f.read_to_string(&mut buf)
            .map_err(|e| IoError::new(IoMode::Read, path, e))?;

        self.run_main(&buf, path.to_string_lossy().into_owned())
    }

    /// Compiles and executes an input expression.
    pub fn run_single_expr(&self, input: &str, path: Option<String>) -> Result<Value, Error> {
        let c = self.compile_single_expr(input, path)?;
        self.execute(c)
    }

    /// Parses and executes a series of expressions and return the last value.
    pub fn run_code(&self, input: &str, path: Option<String>) -> Result<Value, Error> {
        let code = self.compile_code(input, path)?;
        self.execute_program(code)
    }

    /// Compiles and compiles a single expression and returns a code object.
    /// If the input string contains more than one expression, an error is returned.
    pub fn compile_single_expr(&self, input: &str, path: Option<String>) -> Result<Code, Error> {
        let v = self.parse_single_expr(input, path)?;

        let code = compile(&self.context, &v)?;
        Ok(code)
    }

    /// Compiles and compiles a series of expressions.
    pub fn compile_exprs(&self, input: &str) -> Result<Vec<Code>, Error> {
        self.compile_code(input, None)
    }

    /// Parses a single expression and returns it as a `Value`.
    /// If `input` contains more than one expression, an error is returned.
    pub fn parse_single_expr(&self, input: &str, path: Option<String>) -> Result<Value, Error> {
        let offset = self.scope().borrow_codemap_mut().add_source(input, path);

        let mut p = Parser::new(&self.context, Lexer::new(input, offset));
        let v = p.parse_single_expr()?;

        Ok(v)
    }

    /// Parses a series of expressions and returns them as `Value`s.
    pub fn parse_exprs(&self, input: &str, path: Option<String>) -> Result<Vec<Value>, Error> {
        let offset = self.scope().borrow_codemap_mut().add_source(input, path);

        let mut p = Parser::new(&self.context, Lexer::new(input, offset));

        let v = p.parse_exprs()?;

        Ok(v)
    }

    /// Parses a series of expressions from the contents of a file and
    /// returns them as `Value`s.
    pub fn parse_file(&self, input: &str, path: Option<String>) -> Result<Vec<Value>, Error> {
        let offset = self.scope().borrow_codemap_mut().add_source(input, path);

        let mut p = Parser::new(&self.context, Lexer::new(input, offset));
        p.skip_shebang();

        let v = p.parse_exprs()?;

        Ok(v)
    }

    fn compile_code(&self, input: &str, path: Option<String>) -> Result<Vec<Code>, Error> {
        let v = self.parse_exprs(input, path)?;

        v.iter().map(|v| compile(&self.context, v)).collect()
    }

    fn run_main(&self, input: &str, path: String) -> Result<(), Error> {
        let exprs = self.parse_file(input, Some(path))?;
        let code = exprs.iter()
            .map(|v| compile(&self.context, v))
            .collect::<Result<Vec<_>, _>>()?;
        self.execute_program(code)?;
        self.call_main()
    }
}
