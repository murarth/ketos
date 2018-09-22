//! Implements builtin `code` module.

use std::rc::Rc;

use bytecode::{CodeReader, Instruction};
use compile::compile;
use error::Error;
use exec::{Context, ExecError};
use function::{plural, Lambda};
use function::Arity::*;
use module::{Module, ModuleBuilder};
use name::{debug_names, get_standard_name};
use scope::Scope;
use value::{FromValueRef, Value};

/// Loads the `code` module into the given scope.
pub fn load(scope: Scope) -> Module {
    ModuleBuilder::new("code", scope)
        .add_function("compile",        fn_compile,         Exact(1),
            Some("Compiles an expression into a lambda."))
        .add_function("disassemble",    fn_disassemble,     Exact(1),
            Some("Prints bytecode for the given lambda."))
        .add_function("documentation",  fn_documentation,   Exact(1), Some(
"Returns the documentation string for a lambda value or a name.
Returns `()` if the item has no documentation."))
        .add_function("get-const",      fn_get_const,       Exact(2), Some(
"    (get-const lambda n)

Returns the nth const value of a lambda."))
        .add_function("get-value",      fn_get_value,       Exact(2), Some(
"    (get-value lambda n)

Returns the nth captured value of a lambda."))
        .add_function("module-documentation",
                                fn_module_documentation,    Range(0, 1), Some(
"    (module-documentation)
    (module-documentation name)

Returns the documentation string for the named module.
Given no arguments, returns the documentation string for the current module."))
        .finish()
}

/// `compile` compiles an expression into a code object.
fn fn_compile(ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    let code = compile(ctx, &args[0])?;
    Ok(Value::Lambda(Lambda::new(Rc::new(code), ctx.scope())))
}

/// `disassemble` prints information about a `Lambda` code object.
fn fn_disassemble(ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    let l = match args[0] {
        Value::Lambda (ref l) => l,
        ref v => return Err(From::from(ExecError::expected("lambda", v)))
    };

    let scope = ctx.scope();
    let code = &l.code;
    let out = &scope.io().stdout;

    writeln!(out, "{} positional argument{} total",
        code.n_params, plural(code.n_params))?;
    writeln!(out, "{} positional argument{} required",
        code.req_params, plural(code.req_params))?;

    if code.kw_params.is_empty() {
        writeln!(out, "0 keyword arguments")?;
    } else {
        let names = scope.borrow_names();

        writeln!(out, "{} keyword argument{}: {}",
            code.kw_params.len(), plural(code.kw_params.len() as u32),
            code.kw_params.iter().map(|&n| names.get(n))
                .collect::<Vec<_>>().join(" "))?;
    }

    if code.has_rest_params() {
        writeln!(out, "Has rest parameter")?;
    } else {
        writeln!(out, "No rest parameter")?;
    }

    if code.consts.is_empty() {
        writeln!(out, "0 const values")?;
    } else {
        writeln!(out, "{} const value{}:",
            code.consts.len(), plural(code.consts.len() as u32))?;

        let names = scope.borrow_names();

        for (i, v) in code.consts.iter().enumerate() {
            writeln!(out, "  {} = {}", i, debug_names(&names, v))?;
        }
    }

    if let Some(ref v) = l.values {
        writeln!(out, "{} enclosed value{}:", v.len(), plural(v.len() as u32))?;

        let names = scope.borrow_names();

        for (i, v) in v.iter().enumerate() {
            writeln!(out, "  {} = {}", i, debug_names(&names, v))?;
        }
    } else {
        writeln!(out, "0 enclosed values")?;
    }

    let instrs = get_instructions(&code.code)?;
    let mut jumps = Vec::with_capacity(16);

    // Collect all jump labels
    for &(_, ref instr) in &instrs {
        if let Some(off) = instr.jump_label() {
            match jumps.binary_search(&off) {
                Ok(_) => (),
                Err(pos) => jumps.insert(pos, off)
            }
        }
    }

    writeln!(out, "{} bytecode instruction{}:", instrs.len(), plural(instrs.len() as u32))?;

    for (off, instr) in instrs {
        let is_label = jumps.binary_search(&off).is_ok();
        print_instruction(ctx, l, off, instr, is_label)?;
    }

    out.flush()?;
    Ok(().into())
}

fn get_instructions(code: &[u8]) -> Result<Vec<(u32, Instruction)>, ExecError> {
    let mut res = Vec::new();
    let mut r = CodeReader::new(code, 0);

    loop {
        let off = r.offset() as u32;

        let instr = match r.read_instruction() {
            Ok(instr) => instr,
            Err(ExecError::UnexpectedEnd) => break,
            Err(e) => return Err(e)
        };

        res.push((off, instr));
    }

    Ok(res)
}

fn print_instruction(ctx: &Context, lambda: &Lambda,
        offset: u32, instr: Instruction, is_label: bool)
        -> Result<(), Error> {
    use bytecode::Instruction::*;

    let scope = ctx.scope();
    let label_str = if is_label { ">>" } else { "  " };
    let code = &lambda.code;
    let out = &scope.io().stdout;

    let extra = {
        let names = scope.borrow_names();

        match instr {
            LoadC(n) |
            LoadCPush(n) =>
                lambda.values.as_ref().and_then(|v| v.get(n as usize))
                    .map(|v| debug_names(&names, v).to_string()),
            GetDef(n) |
            Const(n) |
            GetDefPush(n) |
            ConstPush(n) |
            EqConst(n) |
            NotEqConst(n) |
            SetDef(n) |
            BuildClosure(n, _) |
            CallConst(n, _)
                => code.consts.get(n as usize).map(
                    |c| debug_names(&names, c).to_string()),
            Jump(l) |
            JumpIf(l) |
            JumpIfNull(l) |
            JumpIfNotNull(l) |
            JumpIfNot(l) |
            JumpIfEq(l) |
            JumpIfNotEq(l) |
            JumpIfBound(l, _)
                => Some(format!("L{}", l)),
            JumpIfEqConst(l, n) |
            JumpIfNotEqConst(l, n)
                => Some(match code.consts.get(n as usize) {
                    None => format!("L{}", l),
                    Some(c) => format!("L{} {}", l, debug_names(&names, c))
                }),
            CallSys(n) |
            CallSysArgs(n, _) =>
                get_standard_name(n).map(|n| names.get(n).to_owned()),
            _ => None
        }
    };

    match extra {
        Some(s) => {
            // fmt::Debug does not honor "<n" formatting,
            // so we make this string first and format again.
            let instr = format!("{:?}", instr);
            writeln!(out, "  {} {:>4}  {:<30} ; {}", label_str, offset, instr, s)?;
        }
        None => writeln!(out, "  {} {:>4}  {:?}", label_str, offset, instr)?
    }

    Ok(())
}

/// `documentation` returns the docstring for a value.
///
/// If the named value does not exist or does not have a docstring,
/// `()` is returned.
fn fn_documentation(ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    match args[0] {
        Value::Function(ref f) => {
            Ok(f.sys_fn.doc
                .map(Value::from)
                .unwrap_or(Value::Unit))
        }
        Value::Lambda(ref l) => {
            Ok(l.code.doc.clone()
                .map(Value::from)
                .unwrap_or(Value::Unit))
        }
        Value::Name(name) => {
            let scope = ctx.scope();
            Ok(scope
                .with_doc(name, |d| d.into())
                .or_else(|| scope.get_value(name)
                    .and_then(|v| value_doc(&v))
                    .map(Value::from))
                .or_else(|| scope.get_macro(name)
                    .and_then(|l| l.code.doc.clone())
                    .map(Value::from))
                .unwrap_or(Value::Unit))
        }
        ref v => Err(From::from(ExecError::expected("name or function", v)))
    }
}

fn value_doc(v: &Value) -> Option<String> {
    match *v {
        Value::Lambda(ref l) => l.code.doc.clone(),
        _ => None
    }
}

/// `get-const` returns the specified const value from a `Lambda` object.
fn fn_get_const(_ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    match args[0] {
        Value::Lambda(ref l) => {
            let n = usize::from_value_ref(&args[1])?;

            let v = l.code.consts.get(n)
                .ok_or_else(|| ExecError::OutOfBounds(n))?;

            Ok(v.clone())
        }
        ref v => Err(From::from(ExecError::expected("lambda", v)))
    }
}

/// `get-value` returns the specified enclosed value from a `Lambda` object.
fn fn_get_value(_ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    match args[0] {
        Value::Lambda(ref l) => {
            let n = usize::from_value_ref(&args[1])?;

            let v = l.values.as_ref().and_then(|v| v.get(n))
                .ok_or_else(|| ExecError::OutOfBounds(n))?;

            Ok(v.clone())
        }
        ref v => Err(From::from(ExecError::expected("lambda", v)))
    }
}

/// `module-documentation` returns the docstring for the named module.
///
/// If the named module is not currently loaded or it does not have a docstring,
/// `()` is returned.
///
/// When given no parameters, the documentation for the current scope is returned.
fn fn_module_documentation(ctx: &Context, args: &mut [Value]) -> Result<Value, Error> {
    if args.is_empty() {
        return Ok(ctx.scope().with_module_doc(|d| d.into())
            .unwrap_or(Value::Unit));
    }

    let name = match args[0] {
        Value::Name(name) => name,
        ref v => return Err(From::from(ExecError::expected("name", v)))
    };

    let m = ctx.scope().modules();

    Ok(m.get_module(name)
        .and_then(|m| m.scope.with_module_doc(|d| d.into()))
        .unwrap_or(Value::Unit))
}
