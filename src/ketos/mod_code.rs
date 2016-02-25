//! Implements builtin `code` module.

use std::rc::Rc;

use bytecode::{CodeReader, Instruction};
use compile::compile;
use error::Error;
use exec::ExecError;
use function::{plural, Lambda};
use function::Arity::Exact;
use io::SharedWrite;
use module::{Module, ModuleBuilder};
use name::{debug_names, get_standard_name};
use scope::Scope;
use value::{FromValueRef, Value};

/// Loads the `code` module into the given scope.
pub fn load(scope: Scope) -> Module {
    ModuleBuilder::new("code", scope)
        .add_function("compile",     fn_compile,     Exact(1))
        .add_function("disassemble", fn_disassemble, Exact(1))
        .add_function("get-const",   fn_get_const,   Exact(2))
        .add_function("get-value",   fn_get_value,   Exact(2))
        .finish()
}

/// `compile` compiles an expression into a code object.
fn fn_compile(scope: &Scope, args: &mut [Value]) -> Result<Value, Error> {
    let code = try!(compile(scope, &args[0]));
    Ok(Value::Lambda(Lambda::new(Rc::new(code), scope)))
}

/// `disassemble` prints information about a `Lambda` code object.
fn fn_disassemble(scope: &Scope, args: &mut [Value]) -> Result<Value, Error> {
    let l = match args[0] {
        Value::Lambda (ref l) => l,
        ref v => return Err(From::from(ExecError::expected("lambda", v)))
    };

    let code = &l.code;
    let out = &scope.get_io().stdout;

    try!(writeln!(out, "{} positional argument{} total",
        code.n_params, plural(code.n_params)));
    try!(writeln!(out, "{} positional argument{} required",
        code.req_params, plural(code.req_params)));

    if code.kw_params.is_empty() {
        try!(writeln!(out, "0 keyword arguments"));
    } else {
        let names = scope.borrow_names();

        try!(writeln!(out, "{} keyword argument{}: {}",
            code.kw_params.len(), plural(code.kw_params.len() as u32),
            code.kw_params.iter().map(|&n| names.get(n))
                .collect::<Vec<_>>().join(" ")));
    }

    if code.has_rest_params() {
        try!(writeln!(out, "Has rest parameter"));
    } else {
        try!(writeln!(out, "No rest parameter"));
    }

    if code.consts.is_empty() {
        try!(writeln!(out, "0 const values"));
    } else {
        try!(writeln!(out, "{} const value{}:",
            code.consts.len(), plural(code.consts.len() as u32)));

        let names = scope.borrow_names();

        for (i, v) in code.consts.iter().enumerate() {
            try!(writeln!(out, "  {} = {}", i, debug_names(&names, v)));
        }
    }

    if let Some(ref v) = l.values {
        try!(writeln!(out, "{} enclosed value{}:", v.len(), plural(v.len() as u32)));

        let names = scope.borrow_names();

        for (i, v) in v.iter().enumerate() {
            try!(writeln!(out, "  {} = {}", i, debug_names(&names, v)));
        }
    } else {
        try!(writeln!(out, "0 enclosed values"));
    }

    let instrs = try!(get_instructions(&code.code));
    let mut jumps = Vec::with_capacity(16);

    // Collect all jump labels
    for &(_, ref instr) in &instrs {
        if let Some(off) = instr.get_jump_label() {
            match jumps.binary_search(&off) {
                Ok(_) => (),
                Err(pos) => jumps.insert(pos, off)
            }
        }
    }

    try!(writeln!(out, "{} bytecode instruction{}:", instrs.len(), plural(instrs.len() as u32)));

    for (off, instr) in instrs {
        let is_label = jumps.binary_search(&off).is_ok();
        try!(print_instruction(scope, l, off, instr, is_label));
    }

    try!(out.flush());
    Ok(().into())
}

fn get_instructions(code: &[u8]) -> Result<Vec<(u32, Instruction)>, ExecError> {
    let mut res = Vec::new();
    let mut r = CodeReader::new(code, 0);

    loop {
        let off = r.get_offset() as u32;

        let instr = match r.read_instruction() {
            Ok(instr) => instr,
            Err(ExecError::UnexpectedEnd) => break,
            Err(e) => return Err(e)
        };

        res.push((off, instr));
    }

    Ok(res)
}

fn print_instruction(scope: &Scope, lambda: &Lambda,
        offset: u32, instr: Instruction, is_label: bool)
        -> Result<(), Error> {
    use bytecode::Instruction::*;

    let label_str = if is_label { ">>" } else { "  " };
    let code = &lambda.code;
    let out = &scope.get_io().stdout;

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
            try!(writeln!(out, "  {} {:>4}  {:<30} ; {}", label_str, offset, instr, s));
        }
        None => try!(writeln!(out, "  {} {:>4}  {:?}", label_str, offset, instr))
    }

    Ok(())
}

/// `get-const` returns the specified const value from a `Lambda` object.
fn fn_get_const(_scope: &Scope, args: &mut [Value]) -> Result<Value, Error> {
    match args[0] {
        Value::Lambda(ref l) => {
            let n = try!(usize::from_value_ref(&args[1]));

            let v = try!(l.code.consts.get(n)
                .ok_or(ExecError::OutOfBounds(n)));

            Ok(v.clone())
        }
        ref v => Err(From::from(ExecError::expected("lambda", v)))
    }
}

/// `get-value` returns the specified enclosed value from a `Lambda` object.
fn fn_get_value(_scope: &Scope, args: &mut [Value]) -> Result<Value, Error> {
    match args[0] {
        Value::Lambda(ref l) => {
            let n = try!(usize::from_value_ref(&args[1]));

            let v = try!(l.values.as_ref().and_then(|v| v.get(n))
                .ok_or(ExecError::OutOfBounds(n)));

            Ok(v.clone())
        }
        ref v => Err(From::from(ExecError::expected("lambda", v)))
    }
}
