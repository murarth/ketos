//! Implements a virtual machine which interprets bytecode functions.
//!
//! The virtual machine consists of:
//!
//!  * A value stack, containing values stored or passed into functions
//!  * A single value register into which values can be loaded from the stack
//!    and from which values can be pushed onto the stack.
//!  * A call stack, containing for each successive function:
//!    * an index into the bytecode ("instruction pointer")
//!    * an index into the value stack ("stack pointer")
//!    * any constant values referenced by bytecode instructions
//!    * any enclosed values referenced by bytecode instructions
//!
//! Bytecode instructions may modify or consume the value register, push values
//! onto the stack, modify the instruction pointer, add a function call to the
//! call stack, or return from the function currently being executed.
//!
//! When a bytecode function is added to the stack, its stack pointer will be set
//! to the position of the first argument which is passed to the function. It may
//! load or modify these values. When the function returns, all values after the
//! stack pointer will be automatically removed from the stack before
//! returning control to the previous function execution. Every function
//! returns a value, which is available to the calling function through the
//! value register.

use std::cell::Cell;
use std::error::Error as StdError;
use std::fmt;
use std::mem::replace;
use std::rc::Rc;
use std::time::Instant;
use std::vec::Drain;

use bytecode::{Code, CodeReader};
use error::Error;
use function::{Arity, Function, Lambda, SystemFn, first, last, init, tail};
use integer::{Integer, Ratio};
use lexer::{highlight_span, Span};
use restrict::{RestrictConfig, RestrictError};
use scope::{MasterScope, Scope};
use string_fmt::FormatError;
use name::{debug_names, display_names, get_standard_name, get_system_fn,
    Name, NameDisplay, NameStore};
use trace::{Trace, TraceItem, set_traceback};
use value::{FromValueRef, Value};

/// Interval, in instructions run, between checking time limit
const TIME_CHECK_INTERVAL: u32 = 100;

/// Represents an execution context
#[derive(Clone)]
pub struct Context {
    scope: Scope,
    restrict: RestrictConfig,
    // In limited circumstances, a Machine may be created during execution
    // to execute a program within a program. Therefore, start time must be
    // carried along with the context rather than attached to a particular
    // Machine.
    //
    // These values are copied when a Context is cloned, but that doesn't
    // create a problem because updates need not be carried back into
    // prior existing Machines.
    run_start: Cell<Option<Instant>>,
    run_level: Cell<u32>,
    memory_held: Cell<usize>,
}

impl Context {
    /// Creates a new execution context.
    pub fn new(scope: Scope, restrict: RestrictConfig) -> Context {
        Context{
            scope: scope,
            restrict: restrict,
            run_start: Cell::new(None),
            run_level: Cell::new(0),
            memory_held: Cell::new(0),
        }
    }

    /// Returns a reference to the contained scope.
    pub fn scope(&self) -> &Scope { &self.scope }

    /// Creates a new execution context with the given scope.
    pub fn with_scope(&self, scope: Scope) -> Context {
        Context::new(scope, self.restrict.clone())
    }

    /// Returns a reference to the contained restriction configuration.
    pub fn restrict(&self) -> &RestrictConfig { &self.restrict }

    fn dec_run_level(&self) {
        let n = self.run_level.get() - 1;
        self.run_level.set(n);
        if n == 0 {
            self.run_start.set(None);
        }
    }

    fn inc_run_level(&self) {
        let n = self.run_level.get();
        self.run_level.set(n + 1);
        if n == 0 {
            self.run_start.set(Some(Instant::now()));
        }
    }

    fn start_time(&self) -> Instant {
        self.run_start.get().expect("context missing start time")
    }

    fn set_memory<F>(&self, f: F) -> usize
            where F: FnOnce(usize) -> usize {
        let old = self.memory_held.get();
        let new = f(old);
        self.memory_held.set(new);
        new
    }
}

/// Represents an error generated while executing bytecode.
#[derive(Debug)]
pub enum ExecError {
    /// Error in arity to function call
    ArityError{
        /// Name of function, if available
        name: Option<Name>,
        /// Expected count or range of arguments
        expected: Arity,
        /// Number of arguments present
        found: u32,
    },
    /// Attempt to compare with a `NaN` `Float` value.
    CompareNaN,
    /// Type does not support ordered comparison
    CannotCompare(&'static str),
    /// Attempt to redefine a name in master scope
    CannotDefine(Name),
    /// Attempt to divide by a number equal to zero.
    DivideByZero,
    /// Duplicate field name in struct definition
    DuplicateField(Name),
    /// Duplicate keyword argument to function
    DuplicateKeyword(Name),
    /// Duplicate struct definition
    DuplicateStructDef(Name),
    /// No such field name in struct
    FieldError{
        /// Name of struct type
        struct_name: Name,
        /// Field name
        field: Name,
    },
    /// Type error assigning value to field
    FieldTypeError{
        /// Name of struct type
        struct_name: Name,
        /// Name of field
        field: Name,
        /// Expected type name
        expected: Name,
        /// Name of type received
        found: &'static str,
        /// Value received
        value: Option<Value>,
    },
    /// Error in `format` call
    FormatError{
        /// Supplied format string
        fmt: Box<str>,
        /// Span within format string
        span: Span,
        /// Formatting error produced
        err: FormatError,
    },
    /// Invalid index into closure values
    InvalidClosureValue(u32),
    /// Invalid const index
    InvalidConst(u32),
    /// Invalid (zero) depth value to `Quote`, `Quasiquote`, or `Comma` instruction
    InvalidDepth,
    /// Invalid jump label
    InvalidJump(u32),
    /// Slice indices out of order
    InvalidSlice(usize, usize),
    /// Invalid stack index
    InvalidStack(u32),
    /// Invalid system function
    InvalidSystemFn(u32),
    /// `CallSys` instruction for system function which requires argument count
    MissingArgCount(Name),
    /// Attempt to construct a `Struct` without the given field
    MissingField{
        /// Struct type name
        struct_name: Name,
        /// Field name
        field: Name,
    },
    /// Attempt to lookup a name that did not exist in scope.
    NameError(Name),
    /// Attempt to slice a string not along UTF-8 code point boundaries.
    NotCharBoundary(usize),
    /// Odd number of parameters when keyword-value pairs expected
    OddKeywordParams,
    /// Attempt to access an element in a list that is out of bounds.
    OutOfBounds(usize),
    /// Integer overflow during certain arithmetic operations.
    Overflow,
    /// Code called `panic`
    Panic(Option<Value>),
    /// Struct definition not found
    StructDefError(Name),
    /// Operation performed on unexpected type
    TypeError{
        /// Name of the type expected
        expected: &'static str,
        /// Name of the type received
        found: &'static str,
        /// Value received
        value: Option<Value>,
    },
    /// Function received a value of incorrect type
    StructMismatch{
        /// Type of left-hand side value
        lhs: Name,
        /// Type of right-hand side value
        rhs: Name,
    },
    /// Attempt to operate on two values of incompatible types
    TypeMismatch{
        /// Type of left-hand side value
        lhs: &'static str,
        /// Type of right-hand side value
        rhs: &'static str,
    },
    /// Unexpected end in bytecode
    UnexpectedEnd,
    /// Unrecognized keyword passed to function
    UnrecognizedKeyword(Name),
    /// Unrecognized opcode
    UnrecognizedOpCode(u8),
}

impl StdError for ExecError {
    fn description(&self) -> &str { "execution error" }
}

/// Returns a `Panic` error with the given value.
///
/// This is equivalent to `(panic value)`.
pub fn panic<T, E>(value: T) -> E
        where T: Into<Value>, E: From<ExecError> {
    From::from(ExecError::Panic(Some(value.into())))
}

/// Returns a `Panic` error with no value.
///
/// This is equivalent to `(panic)`.
pub fn panic_none<E>() -> E
        where E: From<ExecError> {
    From::from(ExecError::Panic(None))
}

impl ExecError {
    /// Convenience function to return a `TypeError` value when `expected`
    /// type is expected, but some other type of value is found.
    pub fn expected(expected: &'static str, v: &Value) -> ExecError {
        ExecError::TypeError{
            expected: expected,
            found: v.type_name(),
            value: Some(v.clone()),
        }
    }

    /// Convenience function to return a `FieldTypeError` value when a struct
    /// field of the incorrect type is received.
    pub fn expected_field(struct_name: Name, field: Name,
            expected: Name, v: &Value) -> ExecError {
        ExecError::FieldTypeError{
            struct_name: struct_name,
            field: field,
            expected: expected,
            found: v.type_name(),
            value: Some(v.clone()),
        }
    }
}

impl fmt::Display for ExecError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::ExecError::*;

        match *self {
            ArityError{expected, found, ..} =>
                write!(f, "expected {}; found {}", expected, found),
            CannotCompare(ty) => write!(f, "cannot compare values of type {}", ty),
            CannotDefine(_) =>
                f.write_str("cannot define name of standard value or operator"),
            CompareNaN => f.write_str("attempt to compare NaN value"),
            DivideByZero => f.write_str("attempt to divide by zero"),
            DuplicateField(_) => f.write_str("duplicate field"),
            DuplicateKeyword(_) => f.write_str("duplicate keyword"),
            DuplicateStructDef(_) => f.write_str("duplicate struct definition"),
            FieldError{..} => f.write_str("no such field in struct"),
            FieldTypeError{..} => f.write_str("incorrect field type"),
            FormatError{ref err, ..} =>
                write!(f, "error in string formatting: {}", err),
            InvalidClosureValue(n) => write!(f, "invalid closure value: {}", n),
            InvalidConst(n) => write!(f, "invalid const: {}", n),
            InvalidDepth => f.write_str("invalid depth operand"),
            InvalidJump(label) => write!(f, "invalid jump label: {}", label),
            InvalidSlice(begin, end) => write!(f, "invalid slice {}..{}", begin, end),
            InvalidStack(n) => write!(f, "invalid stack index: {}", n),
            InvalidSystemFn(n) => write!(f, "invalid system function: {}", n),
            MissingArgCount(_) =>
                write!(f, "system function requires argument count"),
            MissingField{..} => f.write_str("missing field in struct"),
            NameError(_) => f.write_str("name not found in global scope"),
            StructDefError(_) => f.write_str("struct definition not found"),
            NotCharBoundary(n) => write!(f, "index not on char boundary: {}", n),
            OddKeywordParams => f.write_str("expected keyword-value pairs"),
            OutOfBounds(n) => write!(f, "index out of bounds: {}", n),
            Overflow => f.write_str("integer overflow"),
            Panic(_) => f.write_str("panic"),
            TypeError{expected, found, ..} =>
                write!(f, "type error: expected {}; found {}", expected, found),
            StructMismatch{..} => f.write_str("incorrect struct type"),
            TypeMismatch{lhs, rhs} =>
                write!(f, "type mismatch; {} and {}", lhs, rhs),
            UnexpectedEnd => f.write_str("unexpected end of bytecode"),
            UnrecognizedKeyword(_) => f.write_str("unrecognized keyword argument"),
            UnrecognizedOpCode(n) => write!(f, "unrecognized opcode {} ({:x})", n, n),
        }
    }
}

impl NameDisplay for ExecError {
    fn fmt(&self, names: &NameStore, f: &mut fmt::Formatter) -> fmt::Result {
        use self::ExecError::*;

        match *self {
            ArityError{name: Some(name), ..} =>
                write!(f, "`{}` {}", names.get(name), self),
            CannotDefine(name) |
            DuplicateField(name) |
            DuplicateKeyword(name) |
            DuplicateStructDef(name) |
            NameError(name) |
            StructDefError(name) |
            UnrecognizedKeyword(name) =>
                write!(f, "{}: {}", self, names.get(name)),
            FieldError{struct_name, field} =>
                write!(f, "no such field `{}` in struct `{}`",
                    names.get(field),
                    names.get(struct_name)),
            FieldTypeError{struct_name, field, expected, found, ref value} => {
                if let Some(ref value) = *value {
                    write!(f, "type error for field `{}` of struct `{}`: \
                            expected {}; found {}: {}",
                        names.get(field),
                        names.get(struct_name),
                        names.get(expected),
                        found,
                        debug_names(names, value))
                } else {
                    write!(f, "type error for field `{}` of struct `{}`: \
                            expected {}; found {}",
                        names.get(field),
                        names.get(struct_name),
                        names.get(expected),
                        found)
                }
            }
            FormatError{ref fmt, span, ref err} => {
                let hi = highlight_span(fmt, span);

                f.write_str("error in string formatting:\n")?;
                writeln!(f, "{}:{}:error: {}", hi.line, hi.col, err)?;
                writeln!(f, "    {}", hi.source)?;
                writeln!(f, "    {}", hi.highlight)?;
                Ok(())
            }
            MissingArgCount(name) =>
                write!(f, "system function `{}` requires argument count",
                    names.get(name)),
            MissingField{struct_name, field} =>
                write!(f, "missing field `{}` in struct `{}`",
                    names.get(field),
                    names.get(struct_name)),
            Panic(ref value) => match *value {
                Some(ref v) => write!(f, "panic: {}", display_names(names, v)),
                None => f.write_str("explicit panic"),
            },
            StructMismatch{lhs, rhs} =>
                write!(f, "struct type mismatch: `{}` and `{}`",
                    names.get(lhs),
                    names.get(rhs)),
            TypeError{expected, found, ref value} => {
                if let Some(ref value) = *value {
                    write!(f, "type error: expected {}; found {}: {}",
                        expected, found, debug_names(names, value))
                } else {
                    write!(f, "type error: expected {}; found {}",
                        expected, found)
                }
            }
            _ => fmt::Display::fmt(self, f)
        }
    }
}

/// Executes a code object and returns the value.
pub fn execute(ctx: &Context, code: Rc<Code>) -> Result<Value, Error> {
    let mut mach = Machine::new(ctx);

    mach.execute(ctx.scope(), code)
        .map_err(|e| { set_traceback(mach.build_trace()); e })
}

/// Calls a function or lambda in the given scope with the given arguments.
pub fn call_function(ctx: &Context, fun: Value, args: Vec<Value>) -> Result<Value, Error> {
    match fun {
        Value::Function(fun) => execute_function(ctx, fun, args)
            .map_err(|e| { set_traceback(
                Trace::single(TraceItem::CallSys(fun.name), None)); e }),
        Value::Lambda(l) => execute_lambda(ctx, l, args),
        ref v => Err(From::from(ExecError::expected("function", v)))
    }
}

/// Executes a `Function` in the given scope and returns the value.
pub fn execute_function(ctx: &Context, fun: Function, mut args: Vec<Value>)
        -> Result<Value, Error> {
    let n_args = args.len() as u32;

    if !fun.sys_fn.arity.accepts(n_args) {
        Err(From::from(ExecError::ArityError{
            name: Some(fun.name),
            expected: fun.sys_fn.arity,
            found: n_args,
        }))
    } else {
        (fun.sys_fn.callback)(ctx, &mut args)
    }
}

/// Executes a `Lambda` in the given scope and returns the value.
pub fn execute_lambda(ctx: &Context, lambda: Lambda, args: Vec<Value>) -> Result<Value, Error> {
    let mut mach = Machine::new(ctx);

    mach.execute_lambda(lambda, args)
        .map_err(|e| { set_traceback(mach.build_trace()); e })
}

struct StackFrame {
    /// Code object
    code: Rc<Code>,
    /// Code scope
    scope: Scope,
    /// Closure values
    // TODO: When Rc<[T]> is possible for non-static [T], change this.
    values: Option<Rc<Box<[Value]>>>,
    /// Instruction pointer
    iptr: u32,
    /// Stack pointer
    sptr: u32,
    /// Whether the function value was on the stack
    fn_on_stack: bool,
}

struct Machine {
    context: Context,
    stack: Vec<Value>,
    call_stack: Vec<StackFrame>,
    value: Value,
    sys_fn_call: Option<Name>,
}

impl Machine {
    fn new(ctx: &Context) -> Machine {
        Machine{
            context: ctx.clone(),
            stack: Vec::with_capacity(ctx.restrict().value_stack_size),
            call_stack: Vec::with_capacity(ctx.restrict().call_stack_size),
            value: Value::Unit,
            sys_fn_call: None,
        }
    }

    fn build_trace(&self) -> Trace {
        let mut trace = Vec::new();

        for frame in &self.call_stack {
            let mod_name = frame.scope.name();

            let item = match frame.code.name {
                Some(fn_name) => TraceItem::CallCode(mod_name, fn_name),
                None => TraceItem::CallLambda(mod_name),
            };

            trace.push(item);
        }

        if let Some(name) = self.sys_fn_call {
            trace.push(TraceItem::CallSys(name));
        }

        Trace::new(trace, None)
    }

    fn execute(&mut self, scope: &Scope, code: Rc<Code>) -> Result<Value, Error> {
        let arity = code.arity();

        if arity != Arity::Exact(0) {
            return Err(From::from(ExecError::ArityError{
                name: code.name,
                expected: arity,
                found: 0,
            }));
        }

        self.start(StackFrame{
            code: code,
            scope: scope.clone(),
            values: None,
            iptr: 0,
            sptr: 0,
            fn_on_stack: false,
        })
    }

    fn execute_lambda(&mut self, lambda: Lambda, args: Vec<Value>)
            -> Result<Value, Error> {
        let scope = lambda.scope.upgrade()
            .expect("Lambda scope has been destroyed");

        self.push_iter(args)?;

        let n_args = self.stack.len() as u32;
        let arity = lambda.code.arity();

        if !arity.accepts(n_args) {
            return Err(From::from(ExecError::ArityError{
                name: lambda.code.name,
                expected: arity,
                found: n_args,
            }));
        }

        let n_params = lambda.code.n_params;

        if n_params > n_args {
            self.push_unbound(lambda.code.n_params - n_args)?;
        }
        if !lambda.code.kw_params.is_empty() {
            self.push_unbound(lambda.code.kw_params.len() as u32)?;
        }
        if lambda.code.has_rest_params() {
            if n_params >= n_args {
                self.push(Value::Unit)?;
            } else {
                self.build_list(n_args - n_params)?;
                self.push_value()?;
            }
        }

        self.start(StackFrame{
            code: lambda.code,
            scope: scope,
            values: lambda.values,
            iptr: 0,
            sptr: 0,
            fn_on_stack: false,
        })
    }

    fn start(&mut self, mut frame: StackFrame) -> Result<Value, Error> {
        self.context.inc_run_level();

        let res = self.run(&mut frame);

        self.context.dec_run_level();

        if let Err(e) = res {
            // Save the frame for stack traces
            self.call_stack.push(frame);
            return Err(e);
        }

        Ok(self.value.take())
    }

    fn run(&mut self, frame: &mut StackFrame) -> Result<(), Error> {
        use bytecode::Instruction::*;

        let mut n_instructions = 0;

        loop {
            let instr = {
                let mut r = CodeReader::new(&frame.code.code, frame.iptr as usize);
                let instr = r.read_instruction()?;
                frame.iptr = r.offset() as u32;
                instr
            };

            n_instructions += 1;

            if n_instructions % TIME_CHECK_INTERVAL == 0 {
                self.check_time()?;
            }

            match instr {
                Load(n) => self.load(frame.sptr + n)?,
                LoadC(n) => self.load_c(frame, n)?,
                UnboundToUnit(n) => self.unbound_to_unit(frame.sptr + n)?,
                GetDef(n) => self.get_def(frame, n)?,
                Push => self.push_value()?,
                Unit => self.value = Value::Unit,
                True => self.value = Value::Bool(true),
                False => self.value = Value::Bool(false),
                Const(n) => self.load_const(&frame.code, n)?,
                Store(n) => self.store(frame.sptr + n)?,
                LoadPush(n) => self.load_push(frame.sptr + n)?,
                LoadCPush(n) => self.load_c_push(frame, n)?,
                GetDefPush(n) => self.get_def_push(frame, n)?,
                UnitPush => self.push(Value::Unit)?,
                TruePush => self.push(Value::Bool(true))?,
                FalsePush => self.push(Value::Bool(false))?,
                ConstPush(n) => self.push_const(&frame.code, n)?,
                SetDef(n) => self.set_def(frame, n)?,
                List(n) => self.build_list(n)?,
                Quote(n) => self.quote_value(n)?,
                Quasiquote(n) => self.quasiquote_value(n)?,
                Comma(n) => self.comma_value(n)?,
                CommaAt(n) => self.comma_at_value(n)?,
                BuildClosure(n_const, n_values) =>
                    self.build_closure(&frame.code, n_const, n_values)?,
                Jump(label) => self.jump(frame, label)?,
                JumpIf(label) => self.jump_if(frame, label)?,
                JumpIfBound(label, n) => {
                    let n = frame.sptr + n;
                    self.jump_if_bound(frame, label, n)?
                }
                JumpIfNot(label) => self.jump_if_not(frame, label)?,
                JumpIfEq(label) => self.jump_if_eq(frame, label)?,
                JumpIfNotEq(label) => self.jump_if_not_eq(frame, label)?,
                JumpIfNull(label) => self.jump_if_null(frame, label)?,
                JumpIfNotNull(label) => self.jump_if_not_null(frame, label)?,
                JumpIfEqConst(label, n) =>
                    self.jump_if_eq_const(frame, label, n)?,
                JumpIfNotEqConst(label, n) =>
                    self.jump_if_not_eq_const(frame, label, n)?,
                Null => self.test_is_null(),
                NotNull => self.test_is_not_null(),
                Eq => self.equal()?,
                NotEq => self.not_equal()?,
                EqConst(n) => self.equal_const(&frame.code, n)?,
                NotEqConst(n) => self.not_equal_const(&frame.code, n)?,
                Not => self.negate()?,
                Inc => self.increment()?,
                Dec => self.decrement()?,
                Append => self.append_value()?,
                First => self.first()?,
                Tail => self.tail()?,
                Init => self.init()?,
                Last => self.last()?,
                FirstPush => self.first_push()?,
                TailPush => self.tail_push()?,
                InitPush => self.init_push()?,
                LastPush => self.last_push()?,
                CallSys(n) => self.call_sys(frame, n)?,
                CallSysArgs(n, n_args) =>
                    self.call_sys_args(frame, n, n_args)?,
                CallConst(n, n_args) =>
                    self.call_const(frame, n, n_args)?,
                Call(n) => self.call_function(frame, n)?,
                Apply(n) => self.apply(frame, n)?,
                ApplyConst(n, n_args) => self.apply_const(frame, n, n_args)?,
                ApplySelf(n) => self.apply_self(frame, n)?,
                TailApplySelf(n) => self.tail_apply_self(frame, n)?,
                CallSelf(n) => self.call_self(frame, n)?,
                TailCallSelf(n) => self.tail_call(frame, n)?,
                Skip(n) => self.skip_stack(n as usize)?,
                Return => {
                    match self.call_stack.pop() {
                        None => break,
                        Some(call) => {
                            self.clean_stack(frame.sptr as usize);
                            if frame.fn_on_stack {
                                // Pop one more value for the function
                                self.pop()?;
                            }
                            *frame = call;
                        }
                    }
                }
            }
        }

        Ok(())
    }

    fn build_closure(&mut self, code: &Code, n_const: u32, n_values: u32)
            -> Result<(), ExecError> {
        let (code, scope) = match *get_const(code, n_const)? {
            Value::Lambda(ref l) => (l.code.clone(), l.scope.clone()),
            ref v => return Err(ExecError::expected("lambda", v))
        };

        let values = self.drain_stack_top(n_values)?
            .collect::<Vec<_>>().into_boxed_slice();

        self.value = Value::Lambda(Lambda::new_closure(code, scope, values));
        Ok(())
    }

    fn build_list(&mut self, n: u32) -> Result<(), ExecError> {
        let v = self.drain_stack_top(n)?.collect::<Vec<_>>().into();
        self.value = v;
        Ok(())
    }

    fn check_memory(&self, n: usize) -> Result<(), RestrictError> {
        if n > self.context.restrict().memory_limit {
            return Err(RestrictError::MemoryLimitExceeded);
        }
        Ok(())
    }

    fn check_time(&self) -> Result<(), RestrictError> {
        if let Some(time_limit) = self.context.restrict().execution_time {
            let start = self.context.start_time();

            if start.elapsed() >= time_limit {
                return Err(RestrictError::ExecutionTimeExceeded);
            }
        }

        Ok(())
    }

    fn get_sys_fn(&self, n: u32) -> Result<(Name, &'static SystemFn), ExecError> {
        get_standard_name(n).and_then(|n| get_system_fn(n).map(|f| (n, f)))
            .ok_or_else(|| ExecError::InvalidSystemFn(n))
    }

    fn call_sys(&mut self, frame: &mut StackFrame, n: u32) -> Result<(), Error> {
        let (name, sys_fn) = self.get_sys_fn(n)?;

        let n_args = match sys_fn.arity {
            Arity::Exact(n) => n,
            _ => return Err(From::from(ExecError::MissingArgCount(name)))
        };

        self.call_sys_args(frame, n, n_args)
    }

    fn call_sys_args(&mut self, frame: &mut StackFrame, sys_fn: u32, n_args: u32)
            -> Result<(), Error> {
        let (name, sys_fn) = self.get_sys_fn(sys_fn)?;
        self.call_sys_fn(frame, name, sys_fn, n_args, false)
    }

    fn call_sys_fn(&mut self, frame: &mut StackFrame, name: Name,
            sys_fn: &SystemFn, n_args: u32, fn_on_stack: bool)
            -> Result<(), Error> {
        if !sys_fn.arity.accepts(n_args) {
            Err(From::from(ExecError::ArityError{
                name: Some(name),
                expected: sys_fn.arity,
                found: n_args,
            }))
        } else {
                let mut args = self.drain_stack_top(n_args)?
                    .collect::<Vec<_>>();

                if fn_on_stack {
                    self.pop()?;
                }

                // Store the name for traceback if an error is generated
                self.sys_fn_call = Some(name);

                let ctx = self.context.with_scope(frame.scope.clone());

                let v = (sys_fn.callback)(&ctx, &mut args)?;
                self.value = v;

                self.sys_fn_call = None;

                Ok(())
        }
    }

    fn call_const(&mut self, frame: &mut StackFrame,
            n: u32, n_args: u32) -> Result<(), Error> {
        let name = get_const_name(&frame.code, n)?;
        let v = self.get_value(frame, name)?;

        self.value = Value::Unit;
        self.call_value(frame, v, n_args, false)
    }

    /// Calls a function on the stack with `n_args` arguments.
    /// The callable value must be on the stack before the given arguments.
    fn call_function(&mut self, frame: &mut StackFrame, n_args: u32)
            -> Result<(), Error> {
        let v = self.get_stack_top(n_args)?.clone();
        self.call_value(frame, v, n_args, true)
    }

    fn call_value(&mut self, frame: &mut StackFrame, value: Value,
            n_args: u32, fn_on_stack: bool) -> Result<(), Error> {
        match value {
            Value::Function(fun) =>
                self.call_sys_fn(frame, fun.name, &fun.sys_fn, n_args, fn_on_stack),
            Value::Lambda(fun) =>
                self.call_lambda(frame, fun, n_args, fn_on_stack),
            Value::Foreign(ref fv) => {
                let mut args = self.drain_stack_top(n_args)?
                    .collect::<Vec<_>>();

                if fn_on_stack {
                    self.pop()?;
                }

                let ctx = self.context.with_scope(frame.scope.clone());
                let v = fv.call_value(&ctx, &mut args)?;
                self.value = v;

                Ok(())
            }
            ref v => Err(From::from(ExecError::expected("function", v)))
        }
    }

    fn call_lambda(&mut self, frame: &mut StackFrame, lambda: Lambda,
            n_args: u32, fn_on_stack: bool) -> Result<(), Error> {
        let scope = lambda.scope.upgrade()
            .expect("Lambda scope has been destroyed");

        if self.stack.len() < n_args as usize {
            return Err(From::from(RestrictError::ValueStackExceeded));
        }

        let n_args = self.setup_call(&lambda.code, n_args)?;

        let old_frame = replace(frame, StackFrame{
            code: lambda.code,
            scope: scope,
            values: lambda.values,
            iptr: 0,
            sptr: self.stack.len() as u32 - n_args,
            fn_on_stack: fn_on_stack,
        });

        self.save_frame(old_frame)?;
        Ok(())
    }

    /// Sets up a call to a `Code` object, ensuring that the incoming argument
    /// count is valid for the given code object being called.
    /// Keyword and rest arguments are processed and `Unbound` values
    /// are pushed to the stack, if necessary.
    ///
    /// Returns the final count of stack argument values.
    fn setup_call(&mut self, code: &Code, mut n_args: u32) -> Result<u32, Error> {
        if n_args < code.req_params {
            return Err(From::from(ExecError::ArityError{
                name: code.name,
                expected: code.arity(),
                found: n_args,
            }));
        }

        if n_args < code.n_params {
            self.push_unbound(code.n_params - n_args)?;
            n_args = code.n_params;
        }

        if code.has_rest_params() {
            if n_args > code.n_params {
                self.build_list(n_args - code.n_params)?;
                self.push_value()?;
                n_args = code.n_params + 1;
            } else {
                self.push(Value::Unit)?;
                n_args += 1;
            };
        } else if code.has_kw_params() {
            let mut kw_values = vec![Value::Unbound; code.kw_params.len()];

            if n_args > code.n_params {
                let n_kw_args = n_args - code.n_params;
                let mut iter = self.drain_stack_top(n_kw_args)?;

                while let Some(kw) = iter.next() {
                    let kw = get_keyword(&kw)?;
                    let v = match iter.next() {
                        Some(v) => v,
                        None => return Err(From::from(ExecError::OddKeywordParams))
                    };

                    match code.kw_params.iter().position(|&n| n == kw) {
                        Some(pos) => {
                            if let Value::Unbound = kw_values[pos] {
                                kw_values[pos] = v;
                            } else {
                                return Err(From::from(ExecError::DuplicateKeyword(kw)));
                            }
                        }
                        None => return Err(From::from(ExecError::UnrecognizedKeyword(kw)))
                    }
                }
            }

            n_args = code.n_params + kw_values.len() as u32;
            for v in kw_values {
                self.push(v)?;
            }
        } else if n_args != code.n_params {
            return Err(From::from(ExecError::ArityError{
                name: code.name,
                expected: code.arity(),
                found: n_args,
            }));
        }

        Ok(n_args)
    }

    /// Consumes value, which must be `Unit` or `List`,
    /// and pushes each contained value to the top of the stack,
    /// returning the number of values pushed.
    fn expand_value(&mut self) -> Result<usize, Error> {
        let v = self.value.take();

        match v {
            Value::Unit => Ok(0),
            Value::List(li) => {
                let n = li.len();
                self.push_iter(li.to_vec())?;
                Ok(n)
            }
            ref v => Err(From::from(ExecError::expected("list", v))),
        }
    }

    fn apply(&mut self, frame: &mut StackFrame, n_args: u32) -> Result<(), Error> {
        let n = self.expand_value()?;

        self.call_function(frame, n_args + n as u32)
    }

    fn apply_const(&mut self, frame: &mut StackFrame, n: u32, n_args: u32) -> Result<(), Error> {
        let n_push = self.expand_value()?;

        self.call_const(frame, n, n_args + n_push as u32)
    }

    fn apply_self(&mut self, frame: &mut StackFrame, n_args: u32) -> Result<(), Error> {
        let n = self.expand_value()?;

        self.call_self(frame, n_args + n as u32)
    }

    fn tail_apply_self(&mut self, frame: &mut StackFrame, n_args: u32) -> Result<(), Error> {
        let n = self.expand_value()?;

        self.tail_call(frame, n_args + n as u32)
    }

    fn call_self(&mut self, frame: &mut StackFrame, n: u32) -> Result<(), Error> {
        let lambda = Lambda{
            code: frame.code.clone(),
            scope: Rc::downgrade(&frame.scope),
            values: frame.values.clone(),
        };

        self.call_lambda(frame, lambda, n, false)
    }

    fn tail_call(&mut self, frame: &mut StackFrame, n_args: u32) -> Result<(), Error> {
        let len = self.stack.len();

        if len < n_args as usize {
            return Err(From::from(ExecError::InvalidStack(len as u32)));
        }

        let start = frame.sptr as usize;
        let end = len - n_args as usize;

        let n = self.stack[start..end].iter()
            .map(|v| v.size()).sum();
        self.context.set_memory(|m| m.saturating_sub(n));

        let _ = self.stack.drain(start..end);
        frame.iptr = 0;

        self.setup_call(&frame.code, n_args)?;

        Ok(())
    }

    /// Cleans the stack when returning from a function.
    /// All values `stack[pos..]` are removed.
    fn clean_stack(&mut self, pos: usize) {
        let n = self.stack[pos..].iter()
            .map(|v| v.size()).sum();
        self.context.set_memory(|m| m.saturating_sub(n));

        let _ = self.stack.drain(pos..);
    }

    /// Removes the top `n` elements from the stack.
    fn skip_stack(&mut self, n: usize) -> Result<(), ExecError> {
        let len = self.stack.len();

        if n <= len {
            self.clean_stack(len - n);
            Ok(())
        } else {
            Err(ExecError::InvalidStack(len as u32))
        }
    }

    /// Saves the current call state to the call stack.
    fn save_frame(&mut self, frame: StackFrame) -> Result<(), Error> {
        if self.call_stack.len() == self.call_stack.capacity() {
            return Err(From::from(RestrictError::CallStackExceeded));
        }

        self.call_stack.push(frame);
        Ok(())
    }

    /// Load a value from the stack.
    fn load(&mut self, n: u32) -> Result<(), ExecError> {
        self.value = self.get_stack(n)?.clone();
        Ok(())
    }

    /// Load an enclosed value.
    fn load_c(&mut self, frame: &StackFrame, n: u32) -> Result<(), ExecError> {
        self.value = self.get_closure_value(frame, n)?.clone();
        Ok(())
    }

    fn quote_value(&mut self, n: u32) -> Result<(), ExecError> {
        if n == 0 {
            Err(ExecError::InvalidDepth)
        } else {
            let v = self.value.take();
            self.value = v.quote(n);
            Ok(())
        }
    }

    fn quasiquote_value(&mut self, n: u32) -> Result<(), ExecError> {
        if n == 0 {
            Err(ExecError::InvalidDepth)
        } else {
            let v = self.value.take();
            self.value = v.quasiquote(n);
            Ok(())
        }
    }

    fn comma_value(&mut self, n: u32) -> Result<(), ExecError> {
        if n == 0 {
            Err(ExecError::InvalidDepth)
        } else {
            let v = self.value.take();
            self.value = v.comma(n);
            Ok(())
        }
    }

    fn comma_at_value(&mut self, n: u32) -> Result<(), ExecError> {
        if n == 0 {
            Err(ExecError::InvalidDepth)
        } else {
            let v = self.value.take();
            self.value = v.comma_at(n);
            Ok(())
        }
    }

    /// Replace an unbound value on the stack with `()`.
    fn unbound_to_unit(&mut self, n: u32) -> Result<(), ExecError> {
        let v = self.get_stack_mut(n)?;
        if let Value::Unbound = *v {
            *v = Value::Unit;
        }
        Ok(())
    }

    /// Store value on the stack.
    fn store(&mut self, n: u32) -> Result<(), ExecError> {
        let v = self.value.take();
        let p = self.get_stack_mut(n)?;
        *p = v;
        Ok(())
    }

    /// Load a value from the global scope named by a const value.
    fn get_def(&mut self, frame: &StackFrame, n: u32) -> Result<(), ExecError> {
        let name = get_const_name(&frame.code, n)?;
        self.value = self.get_value(frame, name)?;

        Ok(())
    }

    /// Returns a named value from global or master scope.
    fn get_value(&self, frame: &StackFrame, name: Name) -> Result<Value, ExecError> {
        MasterScope::get(name)
            .or_else(|| frame.scope.get_value(name))
            .ok_or_else(|| ExecError::NameError(name))
    }

    fn get_def_push(&mut self, frame: &StackFrame, n: u32) -> Result<(), Error> {
        let name = get_const_name(&frame.code, n)?;
        let v = self.get_value(frame, name)?;
        self.push(v)
    }

    fn set_def(&mut self, frame: &StackFrame, n: u32) -> Result<(), Error> {
        let name = get_const_name(&frame.code, n)?;

        if !MasterScope::can_define(name) {
            return Err(From::from(ExecError::CannotDefine(name)));
        }

        if !frame.scope.contains_value(name)
            && frame.scope.num_values() >= self.context.restrict().namespace_size
        {
            return Err(From::from(RestrictError::NamespaceSizeExceeded));
        }

        // Resulting value is the definition name
        let v = replace(&mut self.value, Value::Name(name));

        frame.scope.add_value(name, v);
        Ok(())
    }

    /// Pop from the top of the stack and return the value.
    fn pop(&mut self) -> Result<Value, ExecError> {
        let v = self.stack.pop().ok_or(ExecError::InvalidStack(0))?;
        self.context.set_memory(|m| m.saturating_sub(v.size()));

        Ok(v)
    }

    /// Push values onto the stack from an iterator.
    ///
    /// # Note
    ///
    /// If `ExactSizeIterator::len` misrepresents the number of items in the
    /// iterator, the stack's capacity may be exceeded without causing an error.
    fn push_iter<I>(&mut self, iter: I) -> Result<(), Error>
            where I: IntoIterator<Item=Value>, I::IntoIter: ExactSizeIterator {
        let iter = iter.into_iter();

        if self.stack.len() + iter.len() > self.stack.capacity() {
            return Err(From::from(RestrictError::ValueStackExceeded));
        }

        let mut size = 0;

        self.stack.extend(iter
            .inspect(|v| size += v.size()));

        let total = self.context.set_memory(|m| m.saturating_add(size));

        self.check_memory(total)?;

        Ok(())
    }

    fn push(&mut self, v: Value) -> Result<(), Error> {
        if self.stack.len() == self.stack.capacity() {
            Err(From::from(RestrictError::ValueStackExceeded))
        } else {
            let n = v.size();
            let total = self.context.set_memory(|m| m.saturating_add(n));
            self.check_memory(total)?;

            self.stack.push(v);
            Ok(())
        }
    }

    fn push_const(&mut self, code: &Code, n: u32) -> Result<(), Error> {
        self.push(get_const(code, n)?.clone())
    }

    fn push_unbound(&mut self, n: u32) -> Result<(), Error> {
        for _ in 0..n {
            self.push(Value::Unbound)?;
        }
        Ok(())
    }

    fn push_value(&mut self) -> Result<(), Error> {
        let v = self.value.take();
        self.push(v)
    }

    fn load_const(&mut self, code: &Code, n: u32) -> Result<(), ExecError> {
        self.value = get_const(code, n)?.clone();
        Ok(())
    }

    fn drain_stack_top(&mut self, n: u32) -> Result<Drain<Value>, ExecError> {
        let len = self.stack.len();

        if n as usize <= len {
            let start = len - n as usize;

            let n = self.stack[start..].iter()
                .map(|v| v.size()).sum();
            self.context.set_memory(|m| m.saturating_sub(n));

            Ok(self.stack.drain(start..))
        } else {
            Err(ExecError::InvalidStack(len as u32))
        }
    }

    fn get_stack(&self, n: u32) -> Result<&Value, ExecError> {
        self.stack.get(n as usize).ok_or_else(|| ExecError::InvalidStack(n))
    }

    /// Returns a reference to an enclosed value.
    fn get_closure_value<'f>(&self, frame: &'f StackFrame, n: u32)
            -> Result<&'f Value, ExecError> {
        frame.values.as_ref().and_then(|v| v.get(n as usize))
            .ok_or_else(|| ExecError::InvalidClosureValue(n))
    }

    fn get_stack_mut(&mut self, n: u32) -> Result<&mut Value, ExecError> {
        self.stack.get_mut(n as usize).ok_or_else(|| ExecError::InvalidStack(n))
    }

    /// Returns a value from the stack `n` values from the top.
    /// `0` returns the top value.
    fn get_stack_top(&self, n: u32) -> Result<&Value, ExecError> {
        let len = self.stack.len();

        if n as usize <= len {
            self.stack.get(len - 1 - n as usize)
                .ok_or_else(|| ExecError::InvalidStack(len as u32))
        } else {
            Err(ExecError::InvalidStack(n))
        }
    }

    fn load_push(&mut self, n: u32) -> Result<(), Error> {
        let v = self.get_stack(n)?.clone();
        self.push(v)
    }

    fn load_c_push(&mut self, frame: &StackFrame, n: u32) -> Result<(), Error> {
        let v = self.get_closure_value(frame, n)?.clone();
        self.push(v)
    }

    fn jump(&mut self, frame: &mut StackFrame, label: u32) -> Result<(), ExecError> {
        if label as usize >= frame.code.code.len() {
            Err(ExecError::InvalidJump(label))
        } else {
            frame.iptr = label;
            Ok(())
        }
    }

    fn jump_if(&mut self, frame: &mut StackFrame, label: u32) -> Result<(), ExecError> {
        if get_bool(&self.value)? {
            self.jump(frame, label)
        } else {
            Ok(())
        }
    }

    fn jump_if_bound(&mut self, frame: &mut StackFrame, label: u32, n: u32) -> Result<(), ExecError> {
        match *self.get_stack(n)? {
            Value::Unbound => Ok(()),
            _ => self.jump(frame, label)
        }
    }

    fn jump_if_null(&mut self, frame: &mut StackFrame, label: u32) -> Result<(), ExecError> {
        match self.value {
            Value::Unit => self.jump(frame, label),
            _ => Ok(())
        }
    }

    fn jump_if_not_null(&mut self, frame: &mut StackFrame, label: u32) -> Result<(), ExecError> {
        match self.value {
            Value::Unit => Ok(()),
            _ => self.jump(frame, label)
        }
    }

    fn jump_if_not(&mut self, frame: &mut StackFrame, label: u32) -> Result<(), ExecError> {
        if get_bool(&self.value)? {
            Ok(())
        } else {
            self.jump(frame, label)
        }
    }

    fn jump_if_eq(&mut self, frame: &mut StackFrame, label: u32) -> Result<(), ExecError> {
        let v = self.pop()?;
        if self.value.is_equal(&v)? {
            self.jump(frame, label)
        } else {
            Ok(())
        }
    }

    fn jump_if_not_eq(&mut self, frame: &mut StackFrame, label: u32) -> Result<(), ExecError> {
        let v = self.pop()?;
        if self.value.is_equal(&v)? {
            Ok(())
        } else {
            self.jump(frame, label)
        }
    }

    fn jump_if_eq_const(&mut self, frame: &mut StackFrame, label: u32, n: u32) -> Result<(), ExecError> {
        let eq = get_const(&frame.code, n).and_then(|v| self.value.is_equal(v))?;

        if eq {
            self.jump(frame, label)
        } else {
            Ok(())
        }
    }

    fn jump_if_not_eq_const(&mut self, frame: &mut StackFrame, label: u32, n: u32) -> Result<(), ExecError> {
        let eq = get_const(&frame.code, n)
            .and_then(|v| self.value.is_equal(v))?;

        if !eq {
            self.jump(frame, label)
        } else {
            Ok(())
        }
    }

    fn test_is_null(&mut self) {
        let null = match self.value {
            Value::Unit => true,
            _ => false
        };

        self.value = null.into();
    }

    fn test_is_not_null(&mut self) {
        let null = match self.value {
            Value::Unit => true,
            _ => false
        };

        self.value = (!null).into();
    }

    fn equal(&mut self) -> Result<(), ExecError> {
        let v = self.pop()?;
        let r = v.is_equal(&self.value)?;
        self.value = r.into();
        Ok(())
    }

    fn not_equal(&mut self) -> Result<(), ExecError> {
        let v = self.pop()?;
        let r = v.is_equal(&self.value)?;
        self.value = (!r).into();
        Ok(())
    }

    fn equal_const(&mut self, code: &Code, n: u32) -> Result<(), ExecError> {
        let c = get_const(code, n)?;
        let r = self.value.is_equal(&c)?;
        self.value = r.into();
        Ok(())
    }

    fn not_equal_const(&mut self, code: &Code, n: u32) -> Result<(), ExecError> {
        let c = get_const(code, n)?;
        let r = self.value.is_equal(&c)?;
        self.value = (!r).into();
        Ok(())
    }

    fn negate(&mut self) -> Result<(), ExecError> {
        match self.value {
            Value::Bool(ref mut v) => *v = !*v,
            ref v => return Err(ExecError::expected("bool", v))
        }
        Ok(())
    }

    fn increment(&mut self) -> Result<(), ExecError> {
        match self.value {
            Value::Float(ref mut f) => *f += 1.0,
            Value::Integer(ref mut i) => *i = i.clone() + Integer::one(),
            Value::Ratio(ref mut r) => *r = r.clone() + Ratio::one(),
            ref v => return Err(ExecError::expected("number", v))
        }
        Ok(())
    }

    fn decrement(&mut self) -> Result<(), ExecError> {
        match self.value {
            Value::Float(ref mut f) => *f -= 1.0,
            Value::Integer(ref mut i) => *i = i.clone() - Integer::one(),
            Value::Ratio(ref mut r) => *r = r.clone() - Ratio::one(),
            ref v => return Err(ExecError::expected("number", v))
        }
        Ok(())
    }

    fn append_value(&mut self) -> Result<(), ExecError> {
        let mut li = self.pop()?;
        let v = self.value.take();

        match li {
            Value::Unit => li = vec![v].into(),
            Value::List(ref mut li) => li.push(v),
            ref v => return Err(ExecError::expected("list", v))
        }

        self.value = li;
        Ok(())
    }

    fn first(&mut self) -> Result<(), Error> {
        let v = first(&self.value)?;

        self.value = v;
        Ok(())
    }

    fn tail(&mut self) -> Result<(), Error> {
        let v = tail(&self.value)?;

        self.value = v;
        Ok(())
    }

    fn init(&mut self) -> Result<(), Error> {
        let v = init(&self.value)?;

        self.value = v;
        Ok(())
    }

    fn last(&mut self) -> Result<(), Error> {
        let v = last(&self.value)?;

        self.value = v;
        Ok(())
    }

    fn first_push(&mut self) -> Result<(), Error> {
        let v = first(&self.value)?;
        self.push(v)
    }

    fn tail_push(&mut self) -> Result<(), Error> {
        let v = tail(&self.value)?;
        self.push(v)
    }

    fn init_push(&mut self) -> Result<(), Error> {
        let v = init(&self.value)?;
        self.push(v)
    }

    fn last_push(&mut self) -> Result<(), Error> {
        let v = last(&self.value)?;
        self.push(v)
    }
}

fn get_bool(v: &Value) -> Result<bool, ExecError> {
    FromValueRef::from_value_ref(v)
}

fn get_const(code: &Code, n: u32) -> Result<&Value, ExecError> {
    code.consts.get(n as usize).ok_or_else(|| ExecError::InvalidConst(n))
}

fn get_keyword(v: &Value) -> Result<Name, ExecError> {
    match *v {
        Value::Keyword(name) => Ok(name),
        ref v => Err(ExecError::expected("keyword", v))
    }
}

fn get_const_name(code: &Code, n: u32) -> Result<Name, ExecError> {
    match *get_const(code, n)? {
        Value::Name(name) => Ok(name),
        ref v => Err(ExecError::expected("name", v))
    }
}

#[cfg(test)]
mod test {
    use super::{ExecError, panic, panic_none};
    use error::Error;
    use value::Value;

    #[test]
    fn test_panic_fn() {
        assert_matches!(panic_none(), ExecError::Panic(None));
        assert_matches!(panic_none(), Error::ExecError(ExecError::Panic(None)));

        assert_matches!(panic("foo"),
            ExecError::Panic(Some(Value::String(ref s)))
                if s == "foo");
        assert_matches!(panic("foo"),
            Error::ExecError(ExecError::Panic(Some(Value::String(ref s))))
                if s == "foo");
    }
}
