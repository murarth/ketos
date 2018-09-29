//! Compiles expressions into bytecode objects.

use std::borrow::Cow::{self, Borrowed, Owned};
use std::fmt;
use std::mem::replace;
use std::rc::Rc;

use bytecode::{
    code_flags, Code, CodeBlock,
    Instruction, JumpInstruction, MAX_SHORT_OPERAND,
};
use const_fold::{
    is_one, is_negative_one,
    FoldOp, FoldAdd, FoldSub, FoldDiv, FoldMul, FoldFloorDiv,
    FoldBitAnd, FoldBitOr, FoldBitXor,
};
use error::Error;
use exec::{Context, ExecError, execute_lambda};
use function::{Arity, Lambda};
use function::Arity::*;
use name::{
    get_system_fn, is_system_operator, standard_names,
    Name, NameDisplay, NameMap, NameSet, NameStore,
    NUM_SYSTEM_OPERATORS, SYSTEM_OPERATORS_BEGIN,
};
use scope::{GlobalScope, ImportSet, MasterScope, Scope};
use structs::{StructDef, StructValueDef};
use trace::{Trace, TraceItem, set_traceback, take_traceback};
use value::{Value, FromValueRef};

const MAX_MACRO_RECURSION: u32 = 100;

/// Represents an error generated while compiling to bytecode.
#[derive(Debug)]
pub enum CompileError {
    /// Error in arity for call to system function
    ArityError{
        /// Name of function
        name: Name,
        /// Expected count or range of arguments
        expected: Arity,
        /// Number of arguments present
        found: u32,
    },
    /// Attempt to define name of standard value or operator
    CannotDefine(Name),
    /// Attempt to define name held by `const` value
    ConstantExists(Name),
    /// Duplicate `exports` declaration
    DuplicateExports,
    /// Duplicate `module-doc` declaration
    DuplicateModuleDoc,
    /// Duplicate name in parameter list
    DuplicateParameter(Name),
    /// Attempt to export nonexistent name from module
    ExportError{
        /// Module name
        module: Name,
        /// Imported name
        name: Name,
    },
    /// Recursion in module imports
    ImportCycle(Name),
    /// Attempt to import nonexistent name from module
    ImportError{
        /// Module name
        module: Name,
        /// Imported name
        name: Name,
    },
    /// Attempt to import or define name which already exists
    ImportShadow(Name),
    /// Invalid expression to function call
    InvalidCallExpression(&'static str),
    /// `,@expr` form outside of a list
    InvalidCommaAt,
    /// Module name contains invalid characters
    InvalidModuleName(Name),
    /// Recursion limit exceeded while expanding macros
    MacroRecursionExceeded,
    /// Missing `export` declaration in loaded module
    MissingExport,
    /// Failed to load a module
    ModuleError(Name),
    /// `const` operator value is not constant
    NotConstant(Name),
    /// Operand value overflow
    OperandOverflow(u32),
    /// Attempt to import value that is not exported
    PrivacyError{
        /// Module name
        module: Name,
        /// Imported name
        name: Name,
    },
    /// Error in parsing operator syntax
    SyntaxError(&'static str),
    /// More commas than backquotes
    UnbalancedComma,
}

impl fmt::Display for CompileError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::CompileError::*;

        match *self {
            ArityError{expected, found, ..} =>
                write!(f, "expected {}; found {}", expected, found),
            CannotDefine(_) =>
                f.write_str("cannot define name of standard value or operator"),
            ConstantExists(_) =>
                f.write_str("cannot define name occupied by a constant value"),
            DuplicateExports => f.write_str("duplicate `export` declaration"),
            DuplicateModuleDoc => f.write_str("duplicate module doc comment"),
            DuplicateParameter(_) => f.write_str("duplicate parameter"),
            ExportError{..} => f.write_str("export name not found in module"),
            ImportCycle(_) => f.write_str("import cycle detected"),
            ImportError{..} => f.write_str("import name not found in module"),
            ImportShadow(_) => f.write_str("shadowing an imported name"),
            InvalidCallExpression(ty) =>
                write!(f, "invalid call expression of type `{}`", ty),
            InvalidCommaAt =>
                f.write_str("`,@expr` form is invalid outside of a list"),
            InvalidModuleName(_) => f.write_str("invalid module name"),
            MacroRecursionExceeded => f.write_str("macro recursion exceeded"),
            MissingExport => f.write_str("missing `export` declaration"),
            ModuleError(_) => f.write_str("module not found"),
            NotConstant(_) => f.write_str("value is not constant"),
            OperandOverflow(n) =>
                write!(f, "operand overflow: {}", n),
            PrivacyError{..} => f.write_str("name is private"),
            SyntaxError(e) => f.write_str(e),
            UnbalancedComma => f.write_str("unbalanced ` and ,"),
        }
    }
}

impl NameDisplay for CompileError {
    fn fmt(&self, names: &NameStore, f: &mut fmt::Formatter) -> fmt::Result {
        use self::CompileError::*;

        match *self {
            ArityError{name, ..} => write!(f, "`{}` {}", names.get(name), self),
            CannotDefine(name) |
            ConstantExists(name) |
            DuplicateParameter(name) |
            InvalidModuleName(name) |
            ModuleError(name) |
            NotConstant(name) => write!(f, "{}: {}", self, names.get(name)),
            ExportError{module, name} =>
                write!(f, "cannot export name `{}`; not found in module `{}`",
                    names.get(name), names.get(module)),
            ImportCycle(name) =>
                write!(f, "import cycle in loading module `{}`", names.get(name)),
            ImportError{module, name} =>
                write!(f, "cannot import name `{}`; not found in module `{}`",
                    names.get(name), names.get(module)),
            ImportShadow(name) =>
                write!(f, "shadowing imported name: {}",
                    names.get(name)),
            PrivacyError{module, name} =>
                write!(f, "name `{}` in module `{}` is private",
                    names.get(name), names.get(module)),
            _ => fmt::Display::fmt(self, f)
        }
    }
}

/// Compiles an expression into a code object.
pub fn compile(ctx: &Context, value: &Value) -> Result<Code, Error> {
    let mut compiler = Compiler::new(ctx);

    compiler.compile(value)
        .map_err(|e| { set_traceback(compiler.take_trace()); e })
}

fn compile_lambda(compiler: &mut Compiler,
        name: Option<Name>,
        params: Vec<(Name, Option<Value>)>,
        req_params: u32,
        kw_params: Vec<(Name, Option<Value>)>,
        rest: Option<Name>, value: &Value)
        -> Result<(Code, Vec<Name>), Error> {
    let r = {
        let outer = compiler.outer.iter().cloned()
            .chain(Some(&*compiler)).collect::<Vec<_>>();

        let mut sub = Compiler::with_outer(&compiler.ctx, name, &outer);

        sub.compile_lambda(name, params, req_params, kw_params, rest, value)
            .map_err(|e| (sub.take_trace(), e))
    };

    r.map_err(|(trace, e)| {
        compiler.extend_trace(trace);
        e
    })
}

/// Compiles a single expression or function body
struct Compiler<'a> {
    /// Compile context
    ctx: Context,
    /// Const values referenced from bytecode
    consts: Vec<Value>,
    /// Blocks of bytecode
    blocks: Vec<CodeBlock>,
    /// Current bytecode block
    cur_block: usize,
    /// Named stack values, paired with stack offset
    stack: Vec<(Name, u32)>,
    /// Current offset in stack; tracks addition and subtraction of named and
    /// unnamed stack values.
    stack_offset: u32,
    /// Set of names from outer scope captured by lambda
    captures: Vec<Name>,
    /// Names in outer scopes available to lambda
    outer: &'a [&'a Compiler<'a>],
    /// Name of lambda being compiled; used to detect tail calls
    self_name: Option<Name>,
    /// Depth of macro expansion
    macro_recursion: u32,
    /// Traces item currently being compiled; used when errors are generated
    trace: Vec<TraceItem>,
    /// Expression added to trace
    trace_expr: Option<Value>,
}

impl<'a> Compiler<'a> {
    fn new(ctx: &Context) -> Compiler<'a> {
        Compiler::with_outer(ctx, None, &[])
    }

    fn with_outer(ctx: &Context, name: Option<Name>,
            outer: &'a [&'a Compiler<'a>]) -> Compiler<'a> {
        Compiler{
            ctx: ctx.clone(),
            consts: Vec::new(),
            blocks: vec![CodeBlock::new()],
            cur_block: 0,
            stack: Vec::new(),
            stack_offset: 0,
            captures: Vec::new(),
            outer: outer,
            self_name: name,
            macro_recursion: 0,
            trace: Vec::new(),
            trace_expr: None,
        }
    }

    fn scope(&self) -> &Scope {
        self.ctx.scope()
    }

    fn is_top_level(&self) -> bool {
        self.outer.is_empty() && self.cur_block == 0
    }

    fn assemble_code(&mut self) -> Result<Box<[u8]>, CompileError> {
        let total = self.write_jumps()?;
        let mut res = Vec::with_capacity(total);

        for block in &mut self.blocks {
            res.extend(block.bytes());
        }

        assert_eq!(res.len(), total);
        Ok(res.into_boxed_slice())
    }

    /// Writes jump instructions with real offsets to each code blocks.
    /// Returns the total size, in bytes, of code blocks.
    fn write_jumps(&mut self) -> Result<usize, CompileError> {
        // If all possible offsets can be shortened, shorten them.
        let short = estimate_size(&self.blocks) <= MAX_SHORT_OPERAND as usize;

        let n_blocks = self.blocks.len();

        let mut new_blocks = Vec::with_capacity(n_blocks);
        let mut offsets = vec![!0; n_blocks];
        // Blocks which are a target of a conditional jump must be written out
        // even if they contain only a Return instruction.
        let mut must_live = vec![false; n_blocks];
        let mut off = 0;
        let mut i = 0;

        loop {
            let mut b = replace(&mut self.blocks[i], CodeBlock::empty());
            let next = b.next;
            let mut skip_block = false;

            match b.jump {
                Some((JumpInstruction::Jump, _)) => (),
                Some((_, n)) => must_live[n as usize] = true,
                _ => ()
            }

            if block_returns(&b, &self.blocks) {
                // If the block is empty and no other blocks will conditionally
                // jump to it, then the block may be pruned altogether.
                // Any blocks which would *unconditionally* jump will
                // instead themselves return.
                skip_block = !must_live[i] && b.is_mostly_empty();

                if !skip_block {
                    // If the block returns, its jump could not possibly have
                    // pointed anywhere but an empty, returning block.
                    b.jump = None;
                    b.push_instruction(Instruction::Return)?;
                }
            }

            if !skip_block {
                b.flush()?;

                // Jump block numbers refer to initial ordering
                offsets[i] = off as u32;
                off += b.calculate_size(short);
                new_blocks.push(b);
            }

            match next {
                Some(n) => i = n as usize,
                None => break
            }
        }

        replace(&mut self.blocks, new_blocks);

        for block in &mut self.blocks {
            if let Some((_, dest)) = block.jump {
                let dest_off = offsets[dest as usize];
                assert!(dest_off != !0, "jump to dead block {}", dest);
                block.write_jump(dest_off, short)?;
            }
        }

        Ok(off)
    }

    fn compile(&mut self, value: &Value) -> Result<Code, Error> {
        self.compile_value(value)?;

        let code = self.assemble_code()?;
        let consts = replace(&mut self.consts, Vec::new());

        Ok(Code{
            name: None,
            code: code,
            consts: consts.into_boxed_slice(),
            kw_params: vec![].into_boxed_slice(),
            n_params: 0,
            req_params: 0,
            flags: 0,
            doc: None,
        })
    }

    fn compile_lambda(&mut self, name: Option<Name>,
            params: Vec<(Name, Option<Value>)>,
            req_params: u32,
            kw_params: Vec<(Name, Option<Value>)>,
            rest: Option<Name>, value: &Value)
            -> Result<(Code, Vec<Name>), Error> {
        let total_params = params.len() + kw_params.len() +
            if rest.is_some() { 1 } else { 0 };

        let n_params = params.len();

        // Insert dummy names to preserve stack locations.
        // Default values for parameters may reference only previously declared
        // parameters. Additionally, the code for default parameter values may
        // push variables onto the stack (immediately ahead of parameter values)
        // and absolute stack references to these additional values must
        // account for the space occupied by inaccessible parameter values.
        //
        // For example, when a function is called such as the following:
        //
        //     (define (foo a :optional (b (bar a)) c) ...)
        //
        // At the moment when `(bar a)` is called, the stack will look like this:
        //
        //     [param-a] [param-b] [param-c] [push-a]
        //
        // `param-` values are input parameters; `push-a` is the value of `a`
        // pushed onto the stack to be accepted by the call to `bar`.
        assert!(self.stack.is_empty());
        self.stack.extend((0..total_params as u32).map(|n| (Name::dummy(), n)));
        self.stack_offset = total_params as u32;

        let mut flags = 0;

        if name.is_some() {
            flags |= code_flags::HAS_NAME;
        }

        assert!(kw_params.is_empty() || rest.is_none(),
            "keyword parameters and rest parameters are mutually exclusive");

        if !kw_params.is_empty() {
            flags |= code_flags::HAS_KW_PARAMS;
        } else if rest.is_some() {
            flags |= code_flags::HAS_REST_PARAMS;
        }

        let mut kw_names = Vec::with_capacity(kw_params.len());

        for (i, (name, default)) in params.into_iter().enumerate() {
            if (i as u32) >= req_params {
                if let Some(default) = default {
                    self.branch_if_unbound(i as u32, &default)?;
                } else {
                    self.push_instruction(
                        Instruction::UnboundToUnit(i as u32))?;
                }
            }

            self.stack[i].0 = name;
        }

        for (i, (name, default)) in kw_params.into_iter().enumerate() {
            if let Some(default) = default {
                self.branch_if_unbound((n_params + i) as u32, &default)?;
            } else {
                self.push_instruction(
                    Instruction::UnboundToUnit((n_params + i) as u32))?;
            }

            self.stack[n_params + i].0 = name;
            kw_names.push(name);
        }

        if let Some(rest) = rest {
            let n = self.stack.len();
            self.stack[n - 1].0 = rest;
        }

        self.compile_value(value)?;

        let code = self.assemble_code()?;
        let consts = replace(&mut self.consts, Vec::new());
        let captures = replace(&mut self.captures, Vec::new());

        let code = Code{
            name: name,
            code: code,
            consts: consts.into_boxed_slice(),
            kw_params: kw_names.into_boxed_slice(),
            n_params: n_params as u32,
            req_params: req_params,
            flags: flags,
            doc: None,
        };

        Ok((code, captures))
    }

    fn compile_value(&mut self, value: &Value) -> Result<(), Error> {
        let mut value = Borrowed(value);

        match self.eval_constant(&value)? {
            ConstResult::IsConstant |
            ConstResult::IsRuntime => (),
            ConstResult::Partial(v) => value = Owned(v),
            ConstResult::Constant(v) => {
                self.load_quoted_value(Owned(v))?;
                return Ok(());
            }
        }

        match *value {
            Value::Name(name) => {
                let loaded = self.load_local_name(name)?;

                if !loaded {
                    let c = self.add_const(Owned(Value::Name(name)));
                    self.push_instruction(Instruction::GetDef(c))?;
                }
            }
            Value::List(ref li) => {
                let fn_v = &li[0];

                let mut pushed_fn = false;

                match *fn_v {
                    Value::Name(name) => {
                        if self.load_local_name(name)? {
                            self.push_instruction(Instruction::Push)?;
                            pushed_fn = true;
                        } else if self.self_name == Some(name) {
                            () // This is handled later
                        } else if self.is_macro(name) {
                            self.trace.push(TraceItem::CallMacro(
                                self.ctx.scope().name(), name));

                            self.macro_recursion += 1;
                            let v = self.expand_macro(name, &li[1..], &value)?;
                            self.compile_value(&v)?;
                            self.macro_recursion -= 1;

                            self.trace.pop();

                            return Ok(());
                        } else if is_system_operator(name) {
                            return self.compile_operator(name, &li[1..], &value);
                        } else if self.specialize_call(name, &li[1..])? {
                            return Ok(());
                        }

                        self.trace.push(TraceItem::CallCode(
                            self.ctx.scope().name(), name));
                    }
                    Value::List(_) => {
                        self.compile_value(fn_v)?;
                        self.push_instruction(Instruction::Push)?;
                        pushed_fn = true;

                        self.trace.push(
                            TraceItem::CallExpr(self.ctx.scope().name()));
                    }
                    ref v => {
                        self.set_trace_expr(&value);
                        return Err(From::from(
                            CompileError::InvalidCallExpression(v.type_name())));
                    }
                }

                for v in &li[1..] {
                    self.compile_value(v)?;
                    self.push_instruction(Instruction::Push)?;
                }

                let n_args = (li.len() - 1) as u32;

                if pushed_fn {
                    self.push_instruction(Instruction::Call(n_args))?;
                } else if let Value::Name(name) = *fn_v {
                    if self.self_name == Some(name) {
                        self.push_instruction(
                            Instruction::CallSelf(n_args))?;
                    } else {
                        match get_system_fn(name) {
                            Some(sys_fn) => {
                                if !sys_fn.arity.accepts(n_args) {
                                    self.set_trace_expr(&value);
                                    return Err(From::from(CompileError::ArityError{
                                        name: name,
                                        expected: sys_fn.arity,
                                        found: n_args,
                                    }));
                                }

                                self.write_call_sys(name, sys_fn.arity, n_args)?;
                            }
                            None => {
                                let c = self.add_const(Owned(Value::Name(name)));
                                self.push_instruction(
                                    Instruction::CallConst(c, n_args))?;
                            }
                        }
                    }
                }

                self.trace.pop();
            }
            Value::Comma(_, _) | Value::CommaAt(_, _) => {
                self.set_trace_expr(&value);
                return Err(From::from(CompileError::UnbalancedComma));
            }
            Value::Quasiquote(ref v, n) =>
                self.compile_quasiquote(v, n)?,
            _ => self.load_const_value(&value)?
        }

        Ok(())
    }

    fn extend_trace(&mut self, mut trace: Trace) {
        self.trace.extend(trace.items());
        self.trace_expr = trace.take_expr();
    }

    fn extend_global_trace(&mut self) {
        if let Some(trace) = take_traceback() {
            self.extend_trace(trace);
        }
    }

    fn set_trace_expr(&mut self, e: &Value) {
        self.trace_expr = Some(e.clone());
    }

    fn take_trace(&mut self) -> Trace {
        Trace::new(replace(&mut self.trace, Vec::new()), self.trace_expr.take())
    }

    fn is_macro(&self, name: Name) -> bool {
        self.scope().contains_macro(name)
    }

    fn expand_macro(&mut self, name: Name, args: &[Value], expr: &Value)
            -> Result<Value, Error> {
        if self.macro_recursion >= MAX_MACRO_RECURSION {
            self.set_trace_expr(expr);
            return Err(From::from(CompileError::MacroRecursionExceeded));
        }

        let lambda = self.scope().get_macro(name)
            .expect("macro not found in expand_macro");

        execute_lambda(&self.ctx, lambda, args.to_vec())
            .map_err(|e| { self.extend_global_trace(); e })
    }

    fn self_name(&self) -> Option<Name> {
        self.self_name
    }

    fn add_constant(&self, name: Name, value: Value) {
        self.scope().add_constant(name, value);
    }

    fn get_constant(&self, name: Name) -> Option<Value> {
        self.scope().get_constant(name)
    }

    fn eval_constant(&mut self, value: &Value) -> Result<ConstResult, Error> {
        match *value {
            Value::Name(name) => {
                match self.get_constant(name) {
                    Some(v) => Ok(ConstResult::Constant(v)),
                    None => Ok(ConstResult::IsRuntime)
                }
            }
            Value::List(ref li) => {
                let name = match li[0] {
                    Value::Name(name) => name,
                    _ => return Ok(ConstResult::IsRuntime)
                };

                self.eval_constant_function(name, &li[1..])
                    .map_err(|e| {
                        self.set_trace_expr(value);
                        e
                    })
            }
            Value::Quasiquote(ref v, n) => self.eval_constant_quasiquote(v, n),
            Value::Comma(_, _) |
            Value::CommaAt(_, _) => {
                self.set_trace_expr(value);
                Err(From::from(CompileError::UnbalancedComma))
            }
            Value::Quote(ref v, 1) => Ok(ConstResult::Constant((**v).clone())),
            Value::Quote(ref v, n) =>
                Ok(ConstResult::Constant((**v).clone().quote(n - 1))),
            _ => Ok(ConstResult::IsConstant)
        }
    }

    fn eval_constant_function(&mut self, name: Name, args: &[Value])
            -> Result<ConstResult, Error> {
        self.trace.push(TraceItem::CallCode(
            self.ctx.scope().name(), name));
        let v = self.eval_constant_function_inner(name, args)?;
        self.trace.pop();
        Ok(v)
    }

    fn eval_constant_function_inner(&mut self, name: Name, args: &[Value])
            -> Result<ConstResult, Error> {
        let n_args = args.len();

        match name {
            standard_names::IF if n_args >= 2 && n_args <= 3 => {
                let mut cond = Borrowed(&args[0]);

                match self.eval_constant(&cond)? {
                    ConstResult::IsRuntime | ConstResult::Partial(_) =>
                        return Ok(ConstResult::IsRuntime),
                    ConstResult::IsConstant => (),
                    ConstResult::Constant(v) => {
                        cond = Owned(v);
                    }
                }

                let cond = match *cond {
                    Value::Bool(v) => v,
                    ref v => {
                        self.set_trace_expr(&cond);
                        return Err(From::from(ExecError::expected("bool", v)));
                    }
                };

                if cond {
                    match self.eval_constant(&args[1])? {
                        ConstResult::IsConstant =>
                            Ok(ConstResult::Constant(args[1].clone())),
                        ConstResult::IsRuntime =>
                            Ok(ConstResult::Partial(args[1].clone())),
                        r => Ok(r)
                    }
                } else if n_args == 2 {
                    Ok(ConstResult::Constant(().into()))
                } else {
                    match self.eval_constant(&args[2])? {
                        ConstResult::IsConstant =>
                            Ok(ConstResult::Constant(args[2].clone())),
                        ConstResult::IsRuntime =>
                            Ok(ConstResult::Partial(args[2].clone())),
                        r => Ok(r)
                    }
                }
            }
            standard_names::ADD if args.is_empty() =>
                Ok(ConstResult::Constant(0.into())),
            standard_names::ADD => fold_commutative::<FoldAdd>(self, name, args),
            standard_names::SUB if args.len() >= 2 =>
                fold_anticommutative::<FoldSub>(self, name, standard_names::ADD, args),
            standard_names::MUL if args.is_empty() =>
                Ok(ConstResult::Constant(1.into())),
            standard_names::MUL => fold_commutative::<FoldMul>(self, name, args),
            standard_names::DIV if args.len() >= 2 =>
                fold_anticommutative::<FoldDiv>(self, name, standard_names::MUL, args),
            standard_names::FLOOR_DIV if args.len() >= 2 =>
                fold_anticommutative::<FoldFloorDiv>(self, name, standard_names::FLOOR, args),
            standard_names::BIT_AND if args.is_empty() =>
                Ok(ConstResult::Constant((-1).into())),
            standard_names::BIT_AND =>
                fold_commutative::<FoldBitAnd>(self, name, args),
            standard_names::BIT_OR if args.is_empty() =>
                Ok(ConstResult::Constant(0.into())),
            standard_names::BIT_OR =>
                fold_commutative::<FoldBitOr>(self, name, args),
            standard_names::BIT_XOR if args.is_empty() =>
                Ok(ConstResult::Constant(0.into())),
            standard_names::BIT_XOR =>
                fold_commutative::<FoldBitXor>(self, name, args),
            _ if is_const_system_fn(name) =>
                eval_system_fn(self, name, args),
            _ => Ok(ConstResult::IsRuntime)
        }
    }

    fn eval_constant_quasiquote(&mut self, value: &Value, depth: u32)
            -> Result<ConstResult, Error> {
        let v = match self.eval_constant_quasi_value(value, depth)? {
            ConstResult::IsConstant => value.clone(),
            ConstResult::Constant(v) => v,
            res => return Ok(res)
        };

        match depth {
            1 => Ok(ConstResult::Constant(v)),
            _ => Ok(ConstResult::Constant(v.quasiquote(depth - 1)))
        }
    }

    /// Evaluates a quasiquote value into a constant expression.
    fn eval_constant_quasi_value(&mut self, value: &Value, depth: u32)
            -> Result<ConstResult, Error> {
        match *value {
            Value::List(ref li) =>
                self.eval_constant_quasiquote_list(li, depth),
            Value::Comma(_, n) if n > depth => {
                self.set_trace_expr(value);
                Err(From::from(CompileError::UnbalancedComma))
            }
            Value::Comma(ref v, n) if n == depth => {
                match self.eval_constant(v)? {
                    ConstResult::IsConstant => Ok(ConstResult::Constant((&**v).clone())),
                    res => Ok(res)
                }
            }
            Value::Comma(ref v, n) => {
                match self.eval_constant_quasi_value(v, depth - n)? {
                    ConstResult::Constant(v) =>
                        Ok(ConstResult::Constant(v.comma(n))),
                    res => Ok(res)
                }
            }
            Value::CommaAt(_, _) => {
                self.set_trace_expr(value);
                Err(From::from(CompileError::InvalidCommaAt))
            }
            Value::Quote(ref v, n) => {
                match self.eval_constant_quasi_value(v, depth)? {
                    ConstResult::Constant(v) =>
                        Ok(ConstResult::Constant(v.quote(n))),
                    res => Ok(res)
                }
            }
            Value::Quasiquote(ref v, n) => {
                match self.eval_constant_quasi_value(v, depth + n)? {
                    ConstResult::Constant(v) =>
                        Ok(ConstResult::Constant(v.quasiquote(n))),
                    res => Ok(res)
                }
            }
            _ => Ok(ConstResult::IsConstant)
        }
    }

    fn eval_constant_quasiquote_list(&mut self, li: &[Value], depth: u32)
            -> Result<ConstResult, Error> {
        let mut new_constant = false;
        let mut values = Vec::new();

        for (i, v) in li.iter().enumerate() {
            match *v {
                Value::CommaAt(_, n) if n > depth => {
                    self.set_trace_expr(v);
                    return Err(From::from(CompileError::InvalidCommaAt));
                }
                Value::CommaAt(ref v, n) if n == depth => {
                    let v = match self.eval_constant(v)? {
                        ConstResult::IsConstant => (**v).clone(),
                        ConstResult::Constant(v) => v,
                        res => return Ok(res)
                    };

                    if !new_constant {
                        values.extend(li[..i].iter().cloned());
                    }

                    new_constant = true;

                    match v {
                        Value::Unit => (),
                        Value::List(li) => values.extend(li.into_vec()),
                        ref v => {
                            self.set_trace_expr(v);
                            return Err(From::from(ExecError::expected("list", v)));
                        }
                    }
                }
                Value::CommaAt(ref v, n) => {
                    match self.eval_constant_quasi_value(v, depth - n)? {
                        ConstResult::IsConstant => {
                            if new_constant {
                                values.push((**v).clone());
                            }
                        }
                        ConstResult::Constant(v) => {
                            if !new_constant {
                                values.extend(li[..i].iter().cloned());
                            }
                            new_constant = true;
                            values.push(v);
                        }
                        res => return Ok(res)
                    }
                }
                _ => {
                    match self.eval_constant_quasi_value(v, depth)? {
                        ConstResult::IsConstant => {
                            if new_constant {
                                values.push(v.clone());
                            }
                        }
                        ConstResult::Constant(v) => {
                            if !new_constant {
                                values.extend(li[..i].iter().cloned());
                            }
                            new_constant = true;
                            values.push(v);
                        }
                        res => return Ok(res)
                    }
                }
            }
        }

        if new_constant {
            Ok(ConstResult::Constant(values.into()))
        } else {
            Ok(ConstResult::IsConstant)
        }
    }

    fn compile_operator(&mut self, name: Name, args: &[Value], expr: &Value)
            -> Result<(), Error> {
        let op = get_system_operator(name);
        let n_args = args.len() as u32;

        self.trace.push(TraceItem::CallOperator(
            self.ctx.scope().name(), name));

        if !op.arity.accepts(n_args) {
            self.set_trace_expr(expr);
            Err(From::from(CompileError::ArityError{
                name: name,
                expected: op.arity,
                found: n_args,
            }))
        } else {
            (op.callback)(self, args)?;
            self.trace.pop();
            Ok(())
        }
    }

    /// Compiles the expression `Quasiquote(value, depth)`
    fn compile_quasiquote(&mut self, value: &Value, depth: u32) -> Result<(), Error> {
        if self.check_quasi_const(value, depth)? {
            match depth {
                1 => self.load_quoted_value(Borrowed(value))?,
                _ => self.load_quoted_value(Owned(
                    value.clone().quasiquote(depth - 1)))?
            }
        } else {
            self.compile_quasi_value(value, depth)?;
            if depth != 1 {
                self.push_instruction(Instruction::Quasiquote(depth - 1))?;
            }
        }

        Ok(())
    }

    /// Compiles a value found within a quasiquoted expression
    fn compile_quasi_value(&mut self, value: &Value, depth: u32) -> Result<(), Error> {
        if self.check_quasi_const(value, depth)? {
            self.load_quoted_value(Borrowed(value))?;
            return Ok(());
        }

        match *value {
            Value::Comma(ref v, n) if n == depth =>
                self.compile_value(v),
            Value::Comma(_, n) | Value::CommaAt(_, n) if n > depth => {
                self.set_trace_expr(value);
                Err(From::from(CompileError::UnbalancedComma))
            }
            Value::Comma(ref v, n) => {
                self.compile_quasi_value(v, depth - n)?;
                self.push_instruction(Instruction::Comma(n))?;
                Ok(())
            }
            Value::CommaAt(_, n) if n == depth => {
                self.set_trace_expr(value);
                Err(From::from(CompileError::InvalidCommaAt))
            }
            Value::List(ref li) =>
                self.compile_quasiquote_list(li, depth),
            Value::Quote(ref v, n) => {
                self.compile_quasi_value(v, depth)?;
                self.push_instruction(Instruction::Quote(n))?;
                Ok(())
            }
            Value::Quasiquote(ref v, n) => {
                if self.check_quasi_const(v, n)? {
                    match n {
                        1 => self.load_const_value(v)?,
                        _ => {
                            let c = self.add_const(Owned(
                                Value::Quasiquote(v.clone(), n - 1)));
                            self.push_instruction(Instruction::Const(c))?;
                        }
                    }

                    Ok(())
                } else {
                    self.compile_quasi_value(v, depth + n)?;
                    if depth == 0 {
                        if n != 1 {
                            self.push_instruction(Instruction::Quasiquote(n - 1))?;
                        }
                    } else {
                        self.push_instruction(Instruction::Quasiquote(n))?;
                    }
                    Ok(())
                }
            }
            // Handled by `if check_quasi_const { ... }` above
            _ => unreachable!()
        }
    }

    fn compile_quasiquote_list(&mut self, li: &[Value], depth: u32) -> Result<(), Error> {
        let mut n_items = 0;
        let mut n_lists = 0;

        for v in li {
            if n_items == 0 && n_lists == 1 {
                self.push_instruction(Instruction::Push)?;
            }

            match *v {
                Value::CommaAt(ref v, n) if n == depth => {
                    if n_items != 0 {
                        self.push_instruction(Instruction::List(n_items))?;
                        self.push_instruction(Instruction::Push)?;
                        n_lists += 1;
                        n_items = 0;
                    }
                    self.compile_value(v)?;
                    if n_lists != 0 {
                        self.push_instruction(Instruction::Push)?;
                    }
                    n_lists += 1;
                }
                Value::CommaAt(_, n) if n > depth => {
                    self.set_trace_expr(v);
                    return Err(From::from(CompileError::UnbalancedComma));
                }
                Value::CommaAt(ref v, n) => {
                    n_items += 1;
                    self.compile_quasi_value(v, depth - n)?;
                    self.push_instruction(
                        Instruction::CommaAt(depth - n))?;
                    self.push_instruction(Instruction::Push)?;
                }
                _ => {
                    n_items += 1;
                    self.compile_quasi_value(v, depth)?;
                    self.push_instruction(Instruction::Push)?;
                }
            }
        }

        if n_items != 0 {
            self.push_instruction(Instruction::List(n_items))?;

            if n_lists != 0 {
                self.push_instruction(Instruction::Push)?;
                n_lists += 1;
            }
        }

        if n_lists > 1 {
            self.push_instruction(Instruction::CallSysArgs(
                standard_names::CONCAT.get(), n_lists))?;
        }

        Ok(())
    }

    /// Returns true if a value found within a quasiquoted value does not
    /// contain any expressions to be evaluated.
    fn check_quasi_const(&mut self, value: &Value, depth: u32) -> Result<bool, Error> {
        match *value {
            Value::List(ref li) => {
                for v in li {
                    if !self.check_quasi_const(v, depth)? {
                        return Ok(false);
                    }
                }

                Ok(true)
            }
            Value::Quasiquote(ref v, n) => self.check_quasi_const(v, depth + n),
            Value::Quote(ref v, _) => self.check_quasi_const(v, depth),
            Value::Comma(_, n)
            | Value::CommaAt(_, n) if n > depth => {
                self.set_trace_expr(value);
                Err(From::from(CompileError::UnbalancedComma))
            }
            Value::Comma(_, n)
            | Value::CommaAt(_, n) if n == depth => Ok(false),
            Value::Comma(ref v, n)
            | Value::CommaAt(ref v, n) =>
                self.check_quasi_const(v, depth - n),
            _ => Ok(true)
        }
    }

    /// Attempt to compile a function call into a more efficient series of
    /// instructions; e.g. `(= a b)` into the `Eq` instruction.
    ///
    /// If specialized instructions cannot be generated, returns `Ok(false)`.
    fn specialize_call(&mut self, name: Name, args: &[Value]) -> Result<bool, Error> {
        let n_args = args.len();

        match name {
            standard_names::ADD if n_args == 2 => {
                let lhs = &args[0];
                let rhs = &args[1];

                return self.specialize_add(lhs, rhs);
            }
            standard_names::SUB if n_args == 2 => {
                let lhs = &args[0];
                let rhs = &args[1];

                return self.specialize_sub(lhs, rhs);
            }
            standard_names::NULL if n_args == 1 => {
                self.compile_value(&args[0])?;
                self.push_instruction(Instruction::Null)?;
            }
            standard_names::EQ if n_args == 2 => {
                let lhs = &args[0];
                let rhs = &args[1];

                self.specialize_eq(lhs, rhs)?;
            }
            standard_names::NOT_EQ if n_args == 2 => {
                let lhs = &args[0];
                let rhs = &args[1];

                self.specialize_ne(lhs, rhs)?;
            }
            standard_names::NOT if n_args == 1 => {
                self.compile_value(&args[0])?;
                self.push_instruction(Instruction::Not)?;
            }
            standard_names::APPEND if n_args == 2 => {
                self.compile_value(&args[0])?;
                self.push_instruction(Instruction::Push)?;
                self.compile_value(&args[1])?;
                self.push_instruction(Instruction::Append)?;
            }
            standard_names::FIRST if n_args == 1 => {
                self.compile_value(&args[0])?;
                self.push_instruction(Instruction::First)?;
            }
            standard_names::TAIL if n_args == 1 => {
                self.compile_value(&args[0])?;
                self.push_instruction(Instruction::Tail)?;
            }
            standard_names::INIT if n_args == 1 => {
                self.compile_value(&args[0])?;
                self.push_instruction(Instruction::Init)?;
            }
            standard_names::LAST if n_args == 1 => {
                self.compile_value(&args[0])?;
                self.push_instruction(Instruction::Last)?;
            }
            standard_names::LIST => {
                self.specialize_list(args)?;
            }
            standard_names::ID if n_args == 1 => {
                self.compile_value(&args[0])?;
            }
            _ => return Ok(false)
        }

        Ok(true)
    }

    fn specialize_add(&mut self, lhs: &Value, rhs: &Value) -> Result<bool, Error> {
        if is_one(lhs) {
            self.compile_value(rhs)?;
            self.push_instruction(Instruction::Inc)?;
        } else if is_one(rhs) {
            self.compile_value(lhs)?;
            self.push_instruction(Instruction::Inc)?;
        } else if is_negative_one(lhs) {
            self.compile_value(rhs)?;
            self.push_instruction(Instruction::Dec)?;
        } else if is_negative_one(rhs) {
            self.compile_value(lhs)?;
            self.push_instruction(Instruction::Dec)?;
        } else {
            return Ok(false);
        }

        Ok(true)
    }

    fn specialize_sub(&mut self, lhs: &Value, rhs: &Value) -> Result<bool, Error> {
        if is_one(rhs) {
            self.compile_value(lhs)?;
            self.push_instruction(Instruction::Dec)?;
        } else if is_negative_one(rhs) {
            self.compile_value(lhs)?;
            self.push_instruction(Instruction::Inc)?;
        } else {
            return Ok(false);
        }

        Ok(true)
    }

    fn specialize_eq(&mut self, lhs: &Value, rhs: &Value) -> Result<(), Error> {
        let lhs_const = match self.eval_constant(lhs)? {
            ConstResult::IsConstant => Some(Borrowed(lhs)),
            ConstResult::Constant(v) => Some(Owned(v)),
            _ => None
        };

        let rhs_const = match self.eval_constant(rhs)? {
            ConstResult::IsConstant => Some(Borrowed(rhs)),
            ConstResult::Constant(v) => Some(Owned(v)),
            _ => None
        };

        if let Some(rhs) = rhs_const {
            self.compile_value(lhs)?;
            let c = self.add_const(rhs);
            self.push_instruction(Instruction::EqConst(c))?;
        } else if let Some(lhs) = lhs_const {
            let c = self.add_const(lhs);
            self.compile_value(rhs)?;
            self.push_instruction(Instruction::EqConst(c))?;
        } else {
            self.compile_value(lhs)?;
            self.push_instruction(Instruction::Push)?;
            self.compile_value(rhs)?;
            self.push_instruction(Instruction::Eq)?;
        }

        Ok(())
    }

    fn specialize_ne(&mut self, lhs: &Value, rhs: &Value) -> Result<(), Error> {
        let lhs_const = match self.eval_constant(lhs)? {
            ConstResult::IsConstant => Some(Borrowed(lhs)),
            ConstResult::Constant(v) => Some(Owned(v)),
            _ => None
        };

        let rhs_const = match self.eval_constant(rhs)? {
            ConstResult::IsConstant => Some(Borrowed(rhs)),
            ConstResult::Constant(v) => Some(Owned(v)),
            _ => None
        };

        if let Some(rhs) = rhs_const {
            self.compile_value(lhs)?;
            let c = self.add_const(rhs);
            self.push_instruction(Instruction::NotEqConst(c))?;
        } else if let Some(lhs) = lhs_const {
            let c = self.add_const(lhs);
            self.compile_value(rhs)?;
            self.push_instruction(Instruction::NotEqConst(c))?;
        } else {
            self.compile_value(lhs)?;
            self.push_instruction(Instruction::Push)?;
            self.compile_value(rhs)?;
            self.push_instruction(Instruction::NotEq)?;
        }

        Ok(())
    }

    fn specialize_list(&mut self, args: &[Value]) -> Result<(), Error> {
        if args.is_empty() {
            self.push_instruction(Instruction::Unit)?;
        } else {
            for arg in args {
                self.compile_value(arg)?;
                self.push_instruction(Instruction::Push)?;
            }
            self.push_instruction(
                Instruction::List(args.len() as u32))?;
        }

        Ok(())
    }

    fn add_const(&mut self, value: Cow<Value>) -> u32 {
        match self.consts.iter().position(|v| v.is_identical(&value)) {
            Some(pos) => pos as u32,
            None => {
                let n = self.consts.len() as u32;
                self.consts.push(value.into_owned());
                n
            }
        }
    }

    fn branch_if_unbound(&mut self, pos: u32, value: &Value) -> Result<(), Error> {
        let bind_block = self.new_block();
        let final_block = self.new_block();

        self.current_block().jump_to(JumpInstruction::JumpIfBound(pos), final_block);

        self.use_next(bind_block);
        self.compile_value(value)?;
        self.push_instruction(Instruction::Store(pos))?;
        self.use_next(final_block);
        Ok(())
    }

    fn load_lambda(&mut self, n: u32, captures: &[Name]) -> Result<(), CompileError> {
        if captures.is_empty() {
            self.push_instruction(Instruction::Const(n))
        } else {
            for &name in captures {
                let _loaded = self.load_local_name(name)?;
                assert!(_loaded);
                self.push_instruction(Instruction::Push)?;
            }

            self.push_instruction(
                Instruction::BuildClosure(n, captures.len() as u32))
        }
    }

    /// Emits code to load a local value from the stack or closure values.
    /// Returns `Ok(true)` if a named value was found and loaded.
    fn load_local_name(&mut self, name: Name) -> Result<bool, CompileError> {
        if let Some(&(_, pos)) = self.stack.iter().rev().find(|&&(n, _)| n == name) {
            self.push_instruction(Instruction::Load(pos))?;
            return Ok(true);
        }

        // self name is more local than enclosed values
        if self.self_name == Some(name) {
            return Ok(false);
        }

        match self.closure_value(name) {
            Some(n) => {
                self.push_instruction(Instruction::LoadC(n))?;
                Ok(true)
            }
            None => Ok(false)
        }
    }

    /// Searches for a named value from enclosing scope.
    /// The name will be added to the set of captures if not already present.
    /// If the name is found, returns value index for use in `LoadC` instruction.
    fn closure_value(&mut self, name: Name) -> Option<u32> {
        match self.captures.iter().position(|&n| n == name) {
            Some(pos) => Some(pos as u32),
            None => {
                for o in self.outer {
                    if o.stack.iter().any(|&(n, _)| n == name) {
                        let n = self.captures.len() as u32;
                        self.captures.push(name);
                        return Some(n);
                    }
                }

                None
            }
        }
    }

    /// Generates instructions to load a constant value.
    fn load_const_value(&mut self, value: &Value) -> Result<(), CompileError> {
        match *value {
            Value::Unit => self.push_instruction(Instruction::Unit),
            Value::Bool(true) => self.push_instruction(Instruction::True),
            Value::Bool(false) => self.push_instruction(Instruction::False),
            Value::Quote(ref v, 1) => {
                self.load_quoted_value(Borrowed(v))
            }
            Value::Quote(ref v, n) => {
                let v = Value::Quote(v.clone(), n - 1);
                self.load_quoted_value(Owned(v))
            }
            ref v => {
                let c = self.add_const(Borrowed(v));
                self.push_instruction(Instruction::Const(c))
            }
        }
    }

    fn load_quoted_value(&mut self, value: Cow<Value>) -> Result<(), CompileError> {
        match *value {
            Value::Unit => self.push_instruction(Instruction::Unit),
            Value::Bool(true) => self.push_instruction(Instruction::True),
            Value::Bool(false) => self.push_instruction(Instruction::False),
            _ => {
                let c = self.add_const(value);
                self.push_instruction(Instruction::Const(c))
            }
        }
    }

    /// Adds a named value to the list of stack values.
    /// Should be followed by a `Push` instruction to adjust `stack_offset`.
    fn push_var(&mut self, name: Name) {
        self.stack.push((name, self.stack_offset));
    }

    /// Remove `n` named values from the list of stack values.
    /// Should be followed by a `Skip` instruction to adjust `stack_offset`.
    fn pop_vars(&mut self, n: u32) {
        let n = self.stack.len() - n as usize;
        let _ = self.stack.drain(n..);
    }

    fn write_call_sys(&mut self, name: Name, arity: Arity, n_args: u32) -> Result<(), CompileError> {
        match arity {
            Arity::Exact(n) => {
                // The only stack_offset adjustment that's done manually.
                self.stack_offset -= n;
                self.push_instruction(Instruction::CallSys(name.get()))
            }
            _ => self.push_instruction(
                Instruction::CallSysArgs(name.get(), n_args))
        }
    }

    fn current_block(&mut self) -> &mut CodeBlock {
        self.blocks.get_mut(self.cur_block).expect("invalid cur_block")
    }

    fn new_block(&mut self) -> u32 {
        let n = self.blocks.len() as u32;
        self.blocks.push(CodeBlock::new());
        n
    }

    fn use_block(&mut self, block: u32) {
        self.cur_block = block as usize;
    }

    fn use_next(&mut self, block: u32) {
        self.current_block().set_next(block);
        self.use_block(block);
    }

    fn flush_instructions(&mut self) -> Result<(), CompileError> {
        self.current_block().flush()
    }

    fn push_instruction(&mut self, instr: Instruction) -> Result<(), CompileError> {
        match instr {
            Instruction::Push => {
                self.stack_offset += 1;
            }
            Instruction::BuildClosure(_, n) |
            Instruction::List(n) |
            Instruction::Skip(n) => {
                self.stack_offset -= n;
            }
            // CallSys is handled at the push site
            // to avoid duplicate get_system_fn call
            Instruction::CallSysArgs(_, n) |
            Instruction::CallSelf(n) |
            Instruction::CallConst(_, n) |
            Instruction::ApplyConst(_, n) |
            Instruction::ApplySelf(n) => {
                self.stack_offset -= n;
            }
            Instruction::Call(n) |
            Instruction::Apply(n) => {
                self.stack_offset -= n + 1;
            }
            Instruction::Append => {
                self.stack_offset -= 1;
            }
            Instruction::Eq |
            Instruction::NotEq => {
                self.stack_offset -= 1;
            }
            _ => ()
        }

        self.current_block().push_instruction(instr)
    }
}

fn is_const_system_fn(name: Name) -> bool {
    use name::standard_names::*;

    match name {
        ADD | SUB | MUL | POW | DIV | FLOOR_DIV |
        REM | SHL | SHR | BIT_AND | BIT_OR | BIT_XOR | BIT_NOT |
        EQ | NOT_EQ | WEAK_EQ | WEAK_NE | LT | GT | LE | GE |
        ZERO | MIN | MAX |
        APPEND | ELT | CONCAT | JOIN | LEN | SLICE |
        FIRST | SECOND | LAST | INIT | TAIL | LIST | REVERSE |
        ABS | CEIL | FLOOR | ROUND | TRUNC | INT |
        FLOAT | INF | NAN | DENOM | FRACT | NUMER | RAT | RECIP |
        CHARS | STRING | PATH | BYTES |
        ID | IS | IS_INSTANCE | NULL | TYPE_OF |
        XOR | NOT
            => true,
        _ => false
    }
}

/// Fold constants for an anticommutative operation.
/// There are two strategies for partial constant evaluation, depending on
/// whether the first value is constant.
///
/// `(- foo 1 2 3)` -> `(- foo 6)`
///
/// `(- 1 foo 2 3)` -> `(- -4 foo)`
///
/// `solo_name` is used in the case of `(foo value identity)`.
fn fold_anticommutative<F: FoldOp>(compiler: &mut Compiler,
        name: Name, solo_name: Name, args: &[Value])
        -> Result<ConstResult, Error> {
    let mut args = args.iter();
    let mut new_args = Vec::new();
    let mut value = None;

    let first = args.next().unwrap();

    let first_const = match compiler.eval_constant(first)? {
        ConstResult::IsRuntime => {
            new_args.push(first.clone());
            false
        }
        ConstResult::Partial(v) => {
            new_args.push(v);
            false
        }
        ConstResult::IsConstant => {
            F::type_check(first)?;
            value = Some(first.clone());
            true
        }
        ConstResult::Constant(v) => {
            F::type_check(&v)?;
            value = Some(v);
            true
        }
    };

    for v in args {
        let mut rhs = Borrowed(v);

        match compiler.eval_constant(v)? {
            ConstResult::IsRuntime => {
                new_args.push(v.clone());
                continue;
            }
            ConstResult::Partial(v) => {
                new_args.push(v);
                continue;
            }
            ConstResult::IsConstant => {
                F::type_check(v)?;
            }
            ConstResult::Constant(v) => {
                F::type_check(&v)?;
                rhs = Owned(v);
            }
        }

        match value {
            Some(lhs) => {
                value = if first_const {
                    Some(F::fold(&compiler.ctx, lhs, &rhs)?)
                } else {
                    Some(F::fold_inv(&compiler.ctx, lhs, &rhs)?)
                };
            }
            None => value = Some(rhs.into_owned())
        }
    }

    match value {
        None => Ok(ConstResult::IsRuntime),
        Some(v) => {
            if new_args.is_empty() {
                Ok(ConstResult::Constant(F::finish(v)?))
            } else {
                if F::is_identity(&v) {
                    if first_const {
                        new_args.insert(0, Value::Name(name));
                    } else {
                        new_args.insert(0, Value::Name(solo_name));
                    }
                } else {
                    new_args.insert(0, Value::Name(name));
                    if first_const {
                        new_args.insert(1, v);
                    } else {
                        new_args.push(v);
                    }
                }
                Ok(ConstResult::Partial(new_args.into()))
            }
        }
    }
}

/// Fold constants for a commutative operation.
///
/// e.g. `(+ 1 foo 2 3)` -> `(+ foo 6)`
fn fold_commutative<F: FoldOp>(compiler: &mut Compiler, name: Name, args: &[Value])
        -> Result<ConstResult, Error> {
    let mut new_args = Vec::new();
    let mut value = None;

    for v in args {
        let mut rhs = Borrowed(v);

        match compiler.eval_constant(v)? {
            ConstResult::IsRuntime => {
                new_args.push(v.clone());
                continue;
            }
            ConstResult::Partial(v) => {
                new_args.push(v);
                continue;
            }
            ConstResult::IsConstant => {
                F::type_check(v)?;
            }
            ConstResult::Constant(v) => {
                F::type_check(&v)?;
                rhs = Owned(v);
            }
        }

        match value {
            Some(lhs) => value = Some(F::fold(&compiler.ctx, lhs, &rhs)?),
            None => value = Some(rhs.into_owned())
        }
    }

    match value {
        None => Ok(ConstResult::IsRuntime),
        Some(v) => {
            if new_args.is_empty() {
                Ok(ConstResult::Constant(F::finish(v)?))
            } else {
                new_args.insert(0, Value::Name(name));
                if !F::is_identity(&v) {
                    new_args.push(v);
                }
                Ok(ConstResult::Partial(new_args.into()))
            }
        }
    }
}

/// Evaluates the named system function by calling it directly,
/// if and only if all arguments are constant values.
fn eval_system_fn(compiler: &mut Compiler, name: Name, args: &[Value])
        -> Result<ConstResult, Error> {
    let sys_fn = get_system_fn(name)
        .expect("eval_system_fn got invalid name");

    let n_args = args.len() as u32;

    if !sys_fn.arity.accepts(n_args) {
        return Err(From::from(CompileError::ArityError{
            name: name,
            expected: sys_fn.arity,
            found: n_args,
        }));
    }

    let mut values = Vec::new();

    for v in args {
        match compiler.eval_constant(v)? {
            ConstResult::IsRuntime |
            ConstResult::Partial(_) => return Ok(ConstResult::IsRuntime),
            ConstResult::IsConstant => {
                values.push(v.clone());
            }
            ConstResult::Constant(v) => {
                values.push(v);
            }
        }
    }

    let v = (sys_fn.callback)(&compiler.ctx, &mut values)?;

    Ok(ConstResult::Constant(v))
}

/// Result of an attempt to evaluate a constant expression
#[derive(Debug)]
enum ConstResult {
    /// Expression is already constant
    IsConstant,
    /// Expression could not be const-evaluated
    IsRuntime,
    /// Expression was partially const-evaluated
    Partial(Value),
    /// Expression is fully constant
    Constant(Value),
}

fn block_returns<'a>(mut b: &'a CodeBlock, blocks: &'a [CodeBlock]) -> bool {
    loop {
        match (b.jump, b.next) {
            (_, None) => return true,
            // This assumes that jumps cannot be cyclical.
            // Currently, the compiler does not emit cyclical jumps.
            (Some((JumpInstruction::Jump, n)), _) |
            (_, Some(n)) if blocks[n as usize].is_mostly_empty() => {
                b = &blocks[n as usize];
            }
            _ => return false
        }
    }
}

fn estimate_size(blocks: &[CodeBlock]) -> usize {
    blocks.iter().map(|b| b.calculate_size(false)).sum::<usize>() + 1usize // Plus one for final Return
}

struct Operator {
    arity: Arity,
    callback: OperatorCallback,
}

type OperatorCallback = fn(&mut Compiler, args: &[Value]) -> Result<(), Error>;

macro_rules! sys_op {
    ( $callback:ident, $arity:expr ) => {
        Operator{
            arity: $arity,
            callback: $callback,
        }
    }
}

fn get_system_operator(name: Name) -> &'static Operator {
    &SYSTEM_OPERATORS[(name.get() - SYSTEM_OPERATORS_BEGIN) as usize]
}

/// System operator implementations.
///
/// These must correspond exactly to names `SYSTEM_OPERATORS_BEGIN` to
/// `SYSTEM_OPERATORS_END` in `name.rs`.
static SYSTEM_OPERATORS: [Operator; NUM_SYSTEM_OPERATORS] = [
    sys_op!(op_apply, Min(2)),
    sys_op!(op_do, Min(1)),
    sys_op!(op_let, Exact(2)),
    sys_op!(op_define, Range(2, 3)),
    sys_op!(op_macro, Range(2, 3)),
    sys_op!(op_struct, Range(2, 3)),
    sys_op!(op_if, Range(2, 3)),
    sys_op!(op_and, Min(1)),
    sys_op!(op_or, Min(1)),
    sys_op!(op_case, Min(2)),
    sys_op!(op_cond, Min(1)),
    sys_op!(op_lambda, Range(2, 3)),
    sys_op!(op_export, Exact(1)),
    sys_op!(op_use, Exact(2)),
    sys_op!(op_const, Range(2, 3)),
    sys_op!(op_set_module_doc, Exact(1)),
];

/// `apply` calls a function or lambda with a series of arguments.
/// Arguments to `apply` other than the last argument are passed directly
/// to the function; the last argument to `apply` is a list whose elements
/// will be passed to the function.
///
/// ```lisp
/// ; Calls (foo 1 2 3 4 5)
/// (apply foo 1 2 '(3 4 5))
/// ```
fn op_apply(compiler: &mut Compiler, args: &[Value]) -> Result<(), Error> {
    let last = args.len() - 1;
    let n_args = last as u32 - 1;
    let mut iter = args[..last].iter();
    let mut apply_const = None;
    let mut apply_self = false;

    if let Value::Name(name) = args[0] {
        // Skip the first value when pushing args to the stack
        iter.next();

        if compiler.self_name() == Some(name) {
            apply_self = true;
        } else if compiler.load_local_name(name)? {
            compiler.push_instruction(Instruction::Push)?;
        } else {
            let c = compiler.add_const(Owned(Value::Name(name)));
            apply_const = Some(c);
        }
    }

    for arg in iter {
        compiler.compile_value(arg)?;
        compiler.push_instruction(Instruction::Push)?;
    }

    compiler.compile_value(&args[last])?;

    if let Some(c) = apply_const {
        compiler.push_instruction(Instruction::ApplyConst(c, n_args))?;
    } else if apply_self {
        compiler.push_instruction(Instruction::ApplySelf(n_args))?;
    } else {
        compiler.push_instruction(Instruction::Apply(n_args))?;
    }

    Ok(())
}

/// `do` evaluates a series of expressions, yielding the value of the last
/// expression.
fn op_do(compiler: &mut Compiler, args: &[Value]) -> Result<(), Error> {
    for arg in args {
        compiler.compile_value(arg)?;
    }
    Ok(())
}

/// `let` defines a series of named value bindings.
///
/// ```lisp
/// (let ((a (foo))
///       (b (bar)))
///   (baz a b))
/// ```
fn op_let(compiler: &mut Compiler, args: &[Value]) -> Result<(), Error> {
    let mut n_vars = 0;

    match args[0] {
        Value::Unit => (),
        Value::List(ref li) => {
            n_vars = li.len() as u32;
            for v in li {
                match *v {
                    Value::List(ref li) if li.len() == 2 => {
                        let name = get_name(compiler, &li[0])?;

                        compiler.compile_value(&li[1])?;
                        compiler.push_var(name);
                        compiler.push_instruction(Instruction::Push)?;
                    }
                    _ => {
                        compiler.set_trace_expr(v);
                        return Err(From::from(CompileError::SyntaxError(
                            "expected list of 2 elements")))
                    }
                }
            }
        }
        ref v => {
            compiler.set_trace_expr(v);
            return Err(From::from(CompileError::SyntaxError("expected list")))
        }
    }

    compiler.compile_value(&args[1])?;

    // Create a new block containing the Skip.
    // This helps to optimize out unnecessary instructions in the assembly phase.
    let next_block = compiler.new_block();
    compiler.use_next(next_block);

    compiler.push_instruction(Instruction::Skip(n_vars))?;
    compiler.pop_vars(n_vars);

    Ok(())
}

/// `define` declares a value binding or function binding in global scope.
///
/// ```lisp
/// (define foo 123)
///
/// (define (bar a) (+ a foo))
/// ```
fn op_define(compiler: &mut Compiler, args: &[Value]) -> Result<(), Error> {
    match args[0] {
        Value::Name(name) => {
            // Replace operator item with more specific item
            compiler.trace.pop();
            compiler.trace.push(TraceItem::Define(compiler.ctx.scope().name(), name));

            let (doc, body) = extract_doc_string(args)?;
            test_define_name(compiler.scope(), name)?;
            compiler.compile_value(&body)?;

            if let Some(doc) = doc {
                compiler.scope().add_doc_string(name, doc.to_owned());
            }

            let c = compiler.add_const(Owned(Value::Name(name)));
            compiler.push_instruction(Instruction::SetDef(c))?;
            Ok(())
        }
        Value::List(ref li) => {
            let name = get_name(compiler, &li[0])?;

            // Replace operator item with more specific item
            compiler.trace.pop();
            compiler.trace.push(TraceItem::Define(compiler.ctx.scope().name(), name));

            test_define_name(compiler.scope(), name)?;
            let (doc, body) = extract_doc_string(args)?;

            let c = compiler.add_const(Owned(Value::Name(name)));

            let (lambda, captures) = make_lambda(
                compiler, Some(name), &li[1..], body, doc)?;

            if compiler.is_top_level() && captures.is_empty() {
                // Add top-level, non-capturing lambdas to global scope immediately.
                compiler.scope().add_value(name, Value::Lambda(lambda));
                let c = compiler.add_const(Owned(Value::Name(name)));
                compiler.push_instruction(Instruction::Const(c))?;
            } else {
                let code_c = compiler.add_const(Owned(Value::Lambda(lambda)));
                compiler.load_lambda(code_c, &captures)?;
                compiler.push_instruction(Instruction::SetDef(c))?;
            }

            Ok(())
        }
        ref v => {
            compiler.set_trace_expr(v);
            Err(From::from(CompileError::SyntaxError("expected name or list")))
        }
    }
}

/// `macro` defines a compile-time macro function in global scope.
fn op_macro(compiler: &mut Compiler, args: &[Value]) -> Result<(), Error> {
    let (name, params) = match args[0] {
        Value::List(ref li) => {
            let name = get_name(compiler, &li[0])?;
            (name, &li[1..])
        }
        ref v => {
            compiler.set_trace_expr(v);
            return Err(From::from(CompileError::SyntaxError("expected list")));
        }
    };

    // Replace operator item with more specific item
    compiler.trace.pop();
    compiler.trace.push(TraceItem::DefineMacro(
        compiler.ctx.scope().name(), name));

    let (doc, body) = extract_doc_string(args)?;

    test_define_name(compiler.scope(), name)?;

    let (lambda, captures) = make_lambda(compiler,
        Some(name), params, &body, doc)?;

    if !captures.is_empty() {
        return Err(From::from(CompileError::SyntaxError(
            "macro lambda cannot enclose values")));
    }

    compiler.scope().add_macro(name, lambda);

    let c = compiler.add_const(Owned(Value::Name(name)));
    compiler.push_instruction(Instruction::Const(c))?;
    Ok(())
}

/// `struct` creates a struct definition and binds to global scope.
///
/// ```lisp
/// (struct Foo ((name string)
///              (num integer)))
/// ```
fn op_struct(compiler: &mut Compiler, args: &[Value]) -> Result<(), Error> {
    let name = get_name(compiler, &args[0])?;

    // Replace operator item with more specific item
    compiler.trace.pop();
    compiler.trace.push(TraceItem::DefineStruct(
        compiler.ctx.scope().name(), name));

    let (doc, body) = extract_doc_string(args)?;

    test_define_name(compiler.scope(), name)?;
    let mut fields = NameMap::new();

    match *body {
        Value::Unit => (),
        Value::List(ref li) => {
            for v in li {
                match *v {
                    Value::List(ref li) if li.len() == 2 => {
                        let fname = get_name(compiler, &li[0])?;
                        let fty = get_name(compiler, &li[1])?;

                        fields.insert(fname, fty);
                    }
                    _ => {
                        compiler.set_trace_expr(v);
                        return Err(From::from(CompileError::SyntaxError(
                            "expected list of 2 elements")))
                    }
                }
            }
        }
        ref v => {
            compiler.set_trace_expr(v);
            return Err(From::from(CompileError::SyntaxError("expected list")));
        }
    }

    let def = StructValueDef::new(fields.into_slice());
    let def = Value::StructDef(Rc::new(StructDef::new(name, Box::new(def))));

    if let Some(doc) = doc {
        compiler.scope().add_doc_string(name, doc.to_owned());
    }

    let name_c = compiler.add_const(Owned(Value::Name(name)));
    let c = compiler.add_const(Owned(def));
    compiler.push_instruction(Instruction::Const(c))?;
    compiler.push_instruction(Instruction::SetDef(name_c))?;
    Ok(())
}

/// `if` evaluates a boolean condition expression and chooses a branch based
/// on the result.
///
/// ```lisp
/// (if (foo)
///   (bar)
///   (baz))
/// ```
fn op_if(compiler: &mut Compiler, args: &[Value]) -> Result<(), Error> {
    let then_block = compiler.new_block();
    let else_block = compiler.new_block();
    let final_block = compiler.new_block();

    compiler.compile_value(&args[0])?;
    compiler.current_block().jump_to(JumpInstruction::JumpIfNot, else_block);

    compiler.use_next(then_block);
    compiler.compile_value(&args[1])?;
    compiler.current_block().jump_to(JumpInstruction::Jump, final_block);

    compiler.use_next(else_block);
    match args.get(2) {
        Some(value) => compiler.compile_value(value)?,
        None => compiler.push_instruction(Instruction::Unit)?
    }

    compiler.use_next(final_block);
    Ok(())
}

/// `and` evaluates a series of boolean expressions, yielding the logical AND
/// of all expressions. If a `false` value is evaluated, no further expressions
/// will be evaluated.
fn op_and(compiler: &mut Compiler, args: &[Value]) -> Result<(), Error> {
    let (last, init) = args.split_last().unwrap();
    let last_block = compiler.new_block();

    for arg in init {
        compiler.compile_value(arg)?;

        // The `and` operator expects a boolean value in the value register
        // after this jump instruction is run. Therefore, we must prevent
        // the compiler from merging it with a previous instruction,
        // which might result in a different value, e.g. () for JumpIfNotNull.
        compiler.flush_instructions()?;
        compiler.current_block().jump_to(JumpInstruction::JumpIfNot, last_block);

        let block = compiler.new_block();
        compiler.use_next(block);
    }

    compiler.compile_value(last)?;
    compiler.use_next(last_block);
    Ok(())
}

/// `and` evaluates a series of boolean expressions, yielding the logical OR
/// of all expressions. If a `true` value is evaluated, no further expressions
/// will be evaluated.
fn op_or(compiler: &mut Compiler, args: &[Value]) -> Result<(), Error> {
    let (last, init) = args.split_last().unwrap();
    let last_block = compiler.new_block();

    for arg in init {
        compiler.compile_value(arg)?;

        // The `or` operator expects a boolean value in the value register
        // after this jump instruction is run. Therefore, we must prevent
        // the compiler from merging it with a previous instruction,
        // which might result in a different value, e.g. () for JumpIfNull.
        compiler.flush_instructions()?;
        compiler.current_block().jump_to(JumpInstruction::JumpIf, last_block);

        let block = compiler.new_block();
        compiler.use_next(block);
    }

    compiler.compile_value(last)?;
    compiler.use_next(last_block);
    Ok(())
}

/// `case` evaluates an expression and selects a branch by comparing the value
/// to a series of constant expressions.
///
/// The last branch may use `else` as its pattern to match all values.
/// If there is not a successful match, the value `()` is yielded.
///
/// ```lisp
/// (case foo
///   ((0 2 4 6 8) 'even)
///   ((1 3 5 7 9) 'odd))
///
/// (case bar
///   ((0 1 2 3) 'a)
///   ((4 5 6 7) 'b)
///   (else      'c))
/// ```
fn op_case(compiler: &mut Compiler, args: &[Value]) -> Result<(), Error> {
    let final_block = compiler.new_block();
    let mut code_blocks = Vec::with_capacity(args.len());
    let mut else_case = false;

    compiler.compile_value(&args[0])?;

    for case in &args[1..] {
        if else_case {
            compiler.set_trace_expr(case);
            return Err(From::from(CompileError::SyntaxError("unreachable case")));
        }

        let li = match *case {
            Value::List(ref li) if li.len() == 2 => li,
            _ => {
                compiler.set_trace_expr(case);
                return Err(From::from(CompileError::SyntaxError(
                    "expected list of 2 elements")));
            }
        };

        let pat = &li[0];
        let code = &li[1];

        let code_begin = compiler.new_block();

        match *pat {
            Value::List(ref li) => {
                for v in li {
                    match *v {
                        Value::Unit => compiler.current_block().jump_to(
                            JumpInstruction::JumpIfNull, code_begin),
                        Value::Bool(true) => compiler.current_block().jump_to(
                            JumpInstruction::JumpIf, code_begin),
                        Value::Bool(false) => compiler.current_block().jump_to(
                            JumpInstruction::JumpIfNot, code_begin),
                        ref v => {
                            let c = compiler.add_const(Borrowed(v));
                            compiler.current_block().jump_to(
                                JumpInstruction::JumpIfEqConst(c), code_begin);
                        }
                    }
                    let b = compiler.new_block();
                    compiler.use_next(b);
                }
            }
            Value::Name(standard_names::ELSE) => {
                else_case = true;
                compiler.current_block().jump_to(JumpInstruction::Jump, code_begin);
            }
            ref v => {
                compiler.set_trace_expr(v);
                return Err(From::from(CompileError::SyntaxError(
                    "expected list or `else`")));
            }
        }

        let prev_block = compiler.cur_block as u32;
        compiler.use_block(code_begin);
        compiler.compile_value(code)?;
        compiler.current_block().jump_to(JumpInstruction::Jump, final_block);
        let code_end = compiler.cur_block as u32;
        code_blocks.push((code_begin, code_end));

        let b = compiler.new_block();
        compiler.use_block(prev_block);
        compiler.use_next(b);
    }

    if !else_case {
        compiler.push_instruction(Instruction::Unit)?;
        compiler.current_block().jump_to(JumpInstruction::Jump, final_block);
    }

    for (begin, end) in code_blocks {
        compiler.current_block().set_next(begin);
        compiler.use_block(end);
    }

    compiler.use_next(final_block);
    Ok(())
}

/// `cond` evaluates a series of boolean expressions and chooses the branch
/// of the first expression evaluating to `true`.
///
/// ```lisp
/// (cond
///   ((<  a 50) 'low)
///   ((>= a 50) 'high))
///
/// (cond
///   ((< a 10)  'low)
///   ((< a 90)  'mid)
///   ((< a 100) 'high)
///   (else      'huge))
/// ```
fn op_cond(compiler: &mut Compiler, args: &[Value]) -> Result<(), Error> {
    let final_block = compiler.new_block();
    let mut code_blocks = Vec::with_capacity(args.len());
    let mut else_case = false;

    for arg in args {
        if else_case {
            compiler.set_trace_expr(arg);
            return Err(From::from(CompileError::SyntaxError(
                "unreachable condition")));
        }

        let case = match *arg {
            Value::List(ref li) if li.len() == 2 => li,
            _ => {
                compiler.set_trace_expr(arg);
                return Err(From::from(CompileError::SyntaxError(
                    "expected list of 2 elements")));
            }
        };

        let cond = &case[0];
        let code = &case[1];

        let code_begin = compiler.new_block();

        if let Value::Name(standard_names::ELSE) = *cond {
            else_case = true;
            compiler.current_block().jump_to(JumpInstruction::Jump, code_begin);
        } else {
            compiler.compile_value(cond)?;
            compiler.current_block().jump_to(JumpInstruction::JumpIf, code_begin);
        }

        let prev_block = compiler.cur_block as u32;
        compiler.use_block(code_begin);
        compiler.compile_value(code)?;
        compiler.current_block().jump_to(JumpInstruction::Jump, final_block);
        let code_end = compiler.cur_block as u32;
        code_blocks.push((code_begin, code_end));

        let b = compiler.new_block();
        compiler.use_block(prev_block);
        compiler.use_next(b);
    }

    if !else_case {
        compiler.push_instruction(Instruction::Unit)?;
        compiler.current_block().jump_to(JumpInstruction::Jump, final_block);
    }

    for (begin, end) in code_blocks {
        compiler.current_block().set_next(begin);
        compiler.use_block(end);
    }

    compiler.use_next(final_block);
    Ok(())
}

/// `lambda` defines an anonymous lambda function which may enclose named values
/// from the enclosing scope.
///
/// ```lisp
/// (define (plus-n n)
///   (lambda (v) (+ v n)))
/// ```
fn op_lambda(compiler: &mut Compiler, args: &[Value]) -> Result<(), Error> {
    // Replace operator item with more specific item
    compiler.trace.pop();
    compiler.trace.push(TraceItem::DefineLambda(compiler.ctx.scope().name()));

    let (doc, body) = extract_doc_string(args)?;

    let li = match args[0] {
        Value::Unit => &[][..],
        Value::List(ref li) => &li[..],
        ref v => {
            compiler.set_trace_expr(v);
            return Err(From::from(CompileError::SyntaxError("expected list")));
        }
    };

    let (lambda, captures) = make_lambda(
        compiler, None, li, body, doc)?;

    let c = compiler.add_const(Owned(Value::Lambda(lambda)));
    compiler.load_lambda(c, &captures)?;
    Ok(())
}

/// `export` declares the set of names exported from a code module.
///
/// ```lisp
/// (export (foo bar baz))
/// ```
fn op_export(compiler: &mut Compiler, args: &[Value]) -> Result<(), Error> {
    if compiler.scope().with_exports(|_| ()).is_some() {
        return Err(From::from(CompileError::DuplicateExports));
    }

    let li = match args[0] {
        Value::Unit => &[][..],
        Value::List(ref li) => &li[..],
        ref v => {
            compiler.set_trace_expr(v);
            return Err(From::from(CompileError::SyntaxError(
                "expected list of names in `export`")));
        }
    };

    let mut names = NameSet::new();

    for v in li {
        names.insert(get_name(compiler, v)?);
    }

    compiler.scope().set_exports(names.into_slice());

    compiler.push_instruction(Instruction::Unit)?;
    Ok(())
}

/// `use` imports a series of names from a module.
///
/// ```lisp
/// (use foo (alpha beta gamma))
/// ```
fn op_use(compiler: &mut Compiler, args: &[Value]) -> Result<(), Error> {
    let mod_name = get_name(compiler, &args[0])?;

    // Replace operator item with more specific item
    compiler.trace.pop();
    compiler.trace.push(TraceItem::UseModule(compiler.ctx.scope().name(), mod_name));

    let ctx = compiler.ctx.clone();
    let mods = ctx.scope().modules();
    let m = mods.load_module(mod_name, &ctx)
        .map_err(|e| { compiler.extend_global_trace(); e })?;

    let mut imp_set = ImportSet::new(mod_name);

    match args[1] {
        Value::Keyword(standard_names::ALL) => {
            let names = compiler.scope().import_all(&m.scope);
            imp_set.names.extend(names.iter().map(|&n| (n, n)));
        }
        Value::Unit => (),
        Value::List(ref li) => {
            import_names(mod_name, &mut imp_set,
                compiler.scope(), &m.scope, li)?;
        }
        ref v => {
            compiler.set_trace_expr(v);
            return Err(From::from(CompileError::SyntaxError(
                "expected list of names or `:all`")));
        }
    }

    compiler.scope().add_imports(imp_set);

    compiler.push_instruction(Instruction::Unit)?;
    Ok(())
}

fn extract_doc_string(args: &[Value]) -> Result<(Option<&str>, &Value), Error> {
    if args.len() == 2 {
        Ok((None, &args[1]))
    } else {
        let doc = <&str>::from_value_ref(&args[1])?;

        Ok((Some(doc), &args[2]))
    }
}

/// `const` declares a named constant value in global scope.
/// The value must be a compile-time constant.
///
/// ```lisp
/// (const foo 123)
///
/// (const bar (+ foo 1))
/// ```
fn op_const(compiler: &mut Compiler, args: &[Value]) -> Result<(), Error> {
    let name = get_name(compiler, &args[0])?;

    // Replace operator item with more specific item
    compiler.trace.pop();
    compiler.trace.push(TraceItem::DefineConst(
        compiler.ctx.scope().name(), name));

    let (doc, body) = extract_doc_string(args)?;

    test_define_name(compiler.scope(), name)?;

    if compiler.get_constant(name).is_some() {
        return Err(From::from(CompileError::ConstantExists(name)));
    }

    let mut value = Borrowed(body);

    match compiler.eval_constant(&value)? {
        ConstResult::IsConstant => (),
        ConstResult::IsRuntime |
        ConstResult::Partial(_) => {
            compiler.set_trace_expr(&value);
            return Err(From::from(CompileError::NotConstant(name)));
        }
        ConstResult::Constant(v) => value = Owned(v)
    }

    compiler.add_constant(name, value.into_owned());
    if let Some(doc) = doc {
        compiler.scope().add_doc_string(name, doc.to_owned());
    }

    compiler.load_quoted_value(Owned(Value::Name(name)))?;
    Ok(())
}

/// `set-module-doc` initializes the docstring for the contained module.
/// It may only appear at most one time per module.
///
/// ```lisp
/// (set-module-doc "Module doc string")
/// ```
fn op_set_module_doc(compiler: &mut Compiler, args: &[Value]) -> Result<(), Error> {
    let doc = <&str>::from_value_ref(&args[0])?;

    let scope = compiler.scope().clone();

    scope.with_module_doc_mut(|d| {
        if d.is_none() {
            *d = Some(doc.to_owned());
            compiler.push_instruction(Instruction::Unit)?;
            Ok(())
        } else {
            Err(From::from(CompileError::DuplicateModuleDoc))
        }
    })
}

fn import_names(mod_name: Name, imps: &mut ImportSet,
        a: &GlobalScope, b: &GlobalScope, names: &[Value]) -> Result<(), CompileError> {
    each_import(names, |src, dest| {
        if !b.contains_name(src) {
            return Err(CompileError::ImportError{
                module: mod_name,
                name: src,
            });
        } else if !b.is_exported(src) {
            return Err(CompileError::PrivacyError{
                module: mod_name,
                name: src,
            });
        }

        test_define_name(a, dest)?;

        if let Some(v) = b.get_constant(src) {
            // Store the remote constants as a runtime value in local scope.
            a.add_value(dest, v);
        }

        if let Some(v) = b.get_macro(src) {
            a.add_macro(dest, v);
        }

        if let Some(v) = b.get_value(src) {
            a.add_value(dest, v);
        }

        b.with_doc(src, |d| a.add_doc_string(dest, d.to_owned()));
        imps.names.push((src, dest));
        Ok(())
    })
}

fn each_import<F>(items: &[Value], mut f: F) -> Result<(), CompileError>
        where F: FnMut(Name, Name) -> Result<(), CompileError> {
    let mut iter = items.iter();

    while let Some(item) = iter.next() {
        let (src, dest) = match *item {
            Value::Keyword(dest) => match iter.next() {
                Some(&Value::Name(src)) => (src, dest),
                _ => return Err(CompileError::SyntaxError(
                    "expected name following keyword"))
            },
            Value::Name(name) => (name, name),
            _ => return Err(CompileError::SyntaxError("expected name or keyword"))
        };

        f(src, dest)?;
    }

    Ok(())
}

fn get_name(compiler: &mut Compiler, v: &Value) -> Result<Name, CompileError> {
    match *v {
        Value::Name(name) => Ok(name),
        _ => {
            compiler.set_trace_expr(v);
            Err(CompileError::SyntaxError("expected name"))
        }
    }
}

fn test_define_name(scope: &GlobalScope, name: Name) -> Result<(), CompileError> {
    if !MasterScope::can_define(name) {
        Err(CompileError::CannotDefine(name))
    } else if scope.contains_constant(name) {
        Err(CompileError::ConstantExists(name))
    } else if scope.is_imported(name) {
        Err(CompileError::ImportShadow(name))
    } else {
        Ok(())
    }
}

/// Creates a `Lambda` object using scope and local values from the given compiler.
/// Returns the `Lambda` object and the set of names captured by the lambda.
fn make_lambda(compiler: &mut Compiler, name: Option<Name>,
        args: &[Value], body: &Value, doc: Option<&str>)
        -> Result<(Lambda, Vec<Name>), Error> {
    let mut params = Vec::new();
    let mut req_params = 0;
    let mut kw_params = Vec::new();
    // Whether we've encountered `:key`
    let mut key = false;
    // Whether we've encountered `:optional`
    let mut optional = false;
    // `:rest` argument, if encountered
    let mut rest = None;

    let mut iter = args.iter();

    while let Some(v) = iter.next() {
        let (name, default) = match *v {
            Value::Name(name) => (name, None),
            Value::Keyword(kw) => {
                match kw {
                    standard_names::KEY => {
                        if key {
                            return Err(From::from(CompileError::SyntaxError(
                                "duplicate `:key`")));
                        } else if optional {
                            return Err(From::from(CompileError::SyntaxError(
                                "`:key` and `:optional` are mutually exclusive")));
                        }
                        key = true;
                        req_params = params.len() as u32;
                    }
                    standard_names::OPTIONAL => {
                        if optional {
                            return Err(From::from(CompileError::SyntaxError(
                                "duplicate `:optional`")));
                        } else if key {
                            return Err(From::from(CompileError::SyntaxError(
                                "`:key` and `:optional` are mutually exclusive")));
                        }
                        optional = true;
                        req_params = params.len() as u32;
                    }
                    standard_names::REST => {
                        if key {
                            return Err(From::from(CompileError::SyntaxError(
                                "`:key` and `:rest` are mutually exclusive")));
                        }

                        let arg = match iter.next() {
                            Some(arg) => arg,
                            None => return Err(From::from(CompileError::SyntaxError(
                                "expected name after `:rest`")))
                        };

                        rest = Some(get_name(compiler, arg)?);

                        match iter.next() {
                            Some(_) => return Err(From::from(CompileError::SyntaxError(
                                "extraneous token after `:rest` argument"))),
                            None => break
                        }
                    }
                    _ => return Err(From::from(CompileError::SyntaxError(
                        "expected :key, :optional, or :rest")))
                }
                continue;
            }
            Value::List(ref li) if li.len() == 2 => {
                let name = get_name(compiler, &li[0])?;
                (name, Some(li[1].clone()))
            }
            ref v => {
                compiler.set_trace_expr(v);
                return Err(From::from(CompileError::SyntaxError(
                    "expected name, keyword, or list of 2 elements")));
            }
        };

        let exists = params.iter().any(|&(n, _)| n == name) ||
            kw_params.iter().any(|&(n, _)| n == name);

        if exists {
            compiler.set_trace_expr(v);
            return Err(From::from(CompileError::DuplicateParameter(name)));
        }

        if default.is_some() && !(key || optional) {
            compiler.set_trace_expr(v);
            return Err(From::from(CompileError::SyntaxError(
                "default value before `:optional` or `:key`")));
        }

        if key {
            kw_params.push((name, default));
        } else {
            params.push((name, default));
        }
    }

    if !optional {
        req_params = params.len() as u32;
    }

    if key && kw_params.is_empty() {
        return Err(From::from(CompileError::SyntaxError(
            "expected arguments after `:key`")));
    }

    if optional && req_params == params.len() as u32 {
        return Err(From::from(CompileError::SyntaxError(
            "expected arguments after `:optional`")));
    }

    let (mut code, captures) = compile_lambda(compiler,
        name, params, req_params, kw_params, rest, body)?;

    if let Some(doc) = doc {
        code.flags |= code_flags::HAS_DOC_STRING;
        code.doc = Some(doc.to_owned());
    }

    Ok((Lambda::new(Rc::new(code), compiler.scope()), captures))
}
