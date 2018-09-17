extern crate dirs;
#[macro_use] extern crate gumdrop;
extern crate ketos;
extern crate linefeed;

use std::cell::RefCell;
use std::env::{split_paths, var_os};
use std::io::{self, stderr, Write};
use std::iter::repeat;
use std::path::{Path, PathBuf};
use std::str::FromStr;
use std::sync::Arc;
use std::time::Duration;

use gumdrop::{Options, ParsingStyle};
use ketos::{
    Builder, Interpreter, complete_name,
    Context, Error, RestrictConfig, ParseError, ParseErrorKind,
};
use linefeed::{
    Interface, Prompter, Command, Completer,
    Completion, Function, ReadResult, Signal, Suffix, Terminal,
};

fn main() {
    let status = run();
    std::process::exit(status);
}

#[derive(Options)]
struct KetosOpts {
    #[options(free)]
    free: Vec<String>,

    #[options(help = "Print this help message and exit")]
    help: bool,
    #[options(short = "V", help = "Print version and exit")]
    version: bool,

    #[options(no_long, help = "Evaluate one expression and exit", meta = "EXPR")]
    expr: Option<String>,
    #[options(help = "Run interactively even with a file")]
    interactive: bool,
    #[options(no_long, help = "Add DIR to list of module search paths", meta = "DIR")]
    include: Vec<String>,
    #[options(short = "R",
        help = "Configure execution restrictions; see `-R help` for more details",
        meta = "SPEC")]
    restrict: Option<String>,
    #[options(no_short, help = "Do not run ~/.ketosrc.ket on startup")]
    no_rc: bool,
}

fn run() -> i32 {
    let args = std::env::args().collect::<Vec<_>>();

    // Allow arguments that appear to be options to be passed to scripts
    let opts = match KetosOpts::parse_args(&args[1..], ParsingStyle::StopAtFirstFree) {
        Ok(opts) => opts,
        Err(e) => {
            let _ = writeln!(stderr(), "{}: {}", args[0], e);
            return 1;
        }
    };

    if opts.version {
        print_version();
        return 0;
    }
    if opts.help {
        print_usage(&args[0]);
        return 0;
    }

    // Search current directory first
    let mut paths = vec![PathBuf::new()];

    if let Some(p) = var_os("KETOS_PATH") {
        paths.extend(split_paths(&p));
    }

    paths.extend(opts.include.into_iter().map(PathBuf::from));

    let mut builder = Builder::new()
        .search_paths(paths);

    if let Some(ref res) = opts.restrict {
        if res == "help" {
            print_restrict_usage();
            return 0;
        }

        builder = match parse_restrict(res) {
            Ok(res) => builder.restrict(res),
            Err(e) => {
                println!("{}: {}", args[0], e);
                return 1;
            }
        }
    }

    let interp = builder.finish();

    let interactive = opts.interactive ||
        (opts.free.is_empty() && opts.expr.is_none());

    if let Some(ref expr) = opts.expr {
        if !run_expr(&interp, &expr) && !interactive {
            return 1;
        }
    } else if !opts.free.is_empty() {
        interp.set_args(&opts.free);

        if !run_file(&interp, Path::new(&opts.free[0])) && !interactive {
            return 1;
        }
    }

    if interactive {
        if !opts.no_rc {
            if let Some(p) = dirs::home_dir() {
                let rc = p.join(".ketosrc.ket");
                if rc.is_file() {
                    // Ignore error in interactive mode
                    run_file(&interp, &rc);
                }
            }
        }

        if let Err(e) = run_repl(&interp) {
            eprintln!("terminal device error: {}", e);
        }
    }

    0
}

fn parse_restrict(params: &str) -> Result<RestrictConfig, String> {
    let mut res = RestrictConfig::permissive();

    for param in params.split(',') {
        match param {
            "permissive" => res = RestrictConfig::permissive(),
            "strict" => res = RestrictConfig::strict(),
            _ => {
                let (name, value) = match param.find('=') {
                    Some(pos) => (&param[..pos], &param[pos + 1..]),
                    None => return Err(format!("unrecognized restrict option: {}", param))
                };

                match name {
                    "execution_time" =>
                        res.execution_time = Some(Duration::from_millis(
                            parse_param(name, value)?)),
                    "call_stack_size" =>
                        res.call_stack_size = parse_param(name, value)?,
                    "value_stack_size" =>
                        res.value_stack_size = parse_param(name, value)?,
                    "namespace_size" =>
                        res.namespace_size = parse_param(name, value)?,
                    "memory_limit" =>
                        res.memory_limit = parse_param(name, value)?,
                    "max_integer_size" =>
                        res.max_integer_size = parse_param(name, value)?,
                    "max_syntax_nesting" =>
                        res.max_syntax_nesting = parse_param(name, value)?,
                    _ => return Err(format!("unrecognized parameter: {}", name))
                }
            }
        }
    }

    Ok(res)
}

fn parse_param<T: FromStr>(name: &str, value: &str) -> Result<T, String> {
    value.parse().map_err(|_| format!("invalid `{}` value: {}", name, value))
}

fn display_error(interp: &Interpreter, e: &Error) {
    if let Some(trace) = interp.take_traceback() {
        interp.display_trace(&trace);
    }
    interp.display_error(e);
}

fn run_expr(interp: &Interpreter, expr: &str) -> bool {
    match interp.run_single_expr(expr, None) {
        Ok(value) => {
            interp.display_value(&value);
            true
        }
        Err(e) => {
            display_error(&interp, &e);
            false
        }
    }
}

fn run_file(interp: &Interpreter, file: &Path) -> bool {
    match interp.run_file(file) {
        Ok(()) => true,
        Err(e) => {
            display_error(&interp, &e);
            false
        }
    }
}

fn run_repl(interp: &Interpreter) -> io::Result<()> {
    let interface = Interface::new("ketos")?;

    set_thread_context(interp.context().clone());
    interface.set_completer(Arc::new(KetosCompleter));

    interface.set_prompt("ketos=> ")?;

    interface.set_report_signal(Signal::Interrupt, true);

    interface.define_function("ketos-accept", Arc::new(KetosAccept));

    interface.bind_sequence("\r", Command::from_str("ketos-accept"));
    interface.bind_sequence("\n", Command::from_str("ketos-accept"));

    {
        let mut reader = interface.lock_reader();

        reader.set_word_break_chars(" \t\n#\"'(),:;@[\\]`{}");
        reader.set_string_chars("\"");
        reader.set_blink_matching_paren(true);
    }

    loop {
        match interface.read_line()? {
            ReadResult::Eof => break,
            ReadResult::Input(mut line) => {
                if line.chars().all(|c| c.is_whitespace()) {
                    continue;
                }

                interface.add_history(line.clone());
                line.push('\n');

                match interp.compile_exprs(&line) {
                    Ok(code) => {
                        if !code.is_empty() {
                            match interp.execute_program(code) {
                                Ok(v) => interp.display_value(&v),
                                Err(e) => display_error(&interp, &e)
                            }
                        }
                    }
                    Err(e) => {
                        display_error(&interp, &e);
                    }
                }

                interp.clear_codemap();
            }
            ReadResult::Signal(_) => {
                println!("^C");
                interface.cancel_read_line()?;
            }
        }
    }

    println!();

    Ok(())
}

struct KetosCompleter;

thread_local!{
    // linefeed requires a Completer to impl Send + Sync.
    // Because a Context object contains Rc, it does not impl these traits.
    // Therefore, we must store the Context object in thread-local storage.
    // (We only use the linefeed Interface from a single thread, anyway.)
    static CONTEXT: RefCell<Option<Context>> = RefCell::new(None);
}

fn set_thread_context(ctx: Context) {
    CONTEXT.with(|key| {
        *key.borrow_mut() = Some(ctx);
    });
}

fn thread_context() -> Context {
    CONTEXT.with(|key| {
        key.borrow().clone().unwrap_or_else(
            || panic!("no thread-local Context object set"))
    })
}

impl<Term: Terminal> Completer<Term> for KetosCompleter {
    fn complete(&self, word: &str, prompter: &Prompter<Term>,
            start: usize, end: usize) -> Option<Vec<Completion>> {
        let line_start = prompter.buffer()[..start].rfind('\n')
            .map(|pos| pos + 1).unwrap_or(0);
        let is_whitespace = prompter.buffer()[line_start..start]
            .chars().all(|ch| ch.is_whitespace());

        if is_whitespace && start == end {
            // Indent when there's no word to complete
            let n = 2 - (start - line_start) % 2;

            Some(vec![Completion{
                completion: repeat(' ').take(n).collect(),
                display: None,
                suffix: Suffix::None,
            }])
        } else {
            let ctx = thread_context();
            complete_name(word, ctx.scope()).map(
                |words| words.into_iter().map(Completion::simple).collect())
        }
    }
}

struct KetosAccept;

impl<Term: Terminal> Function<Term> for KetosAccept {
    fn execute(&self, prompter: &mut Prompter<Term>, count: i32, _ch: char) -> io::Result<()> {
        let interp = Interpreter::with_context(thread_context());

        let r = interp.parse_exprs(prompter.buffer(), None);
        interp.clear_codemap();

        match r {
            Err(Error::ParseError(ParseError{kind: ParseErrorKind::MissingCloseParen, ..})) |
            Err(Error::ParseError(ParseError{kind: ParseErrorKind::UnterminatedComment, ..})) |
            Err(Error::ParseError(ParseError{kind: ParseErrorKind::UnterminatedString, ..})) |
            Err(Error::ParseError(ParseError{kind: ParseErrorKind::DocCommentEof, ..})) => {
                if count > 0 {
                    prompter.insert(count as usize, '\n')
                } else {
                    Ok(())
                }
            }
            Ok(_) | Err(_) => prompter.accept_input(),
        }
    }
}

fn print_version() {
    println!("ketos {}", version());
}

fn version() -> &'static str {
    env!("CARGO_PKG_VERSION")
}

fn print_usage(arg0: &str) {
    println!("Usage: {} [OPTIONS] [FILE] [ARGS]", arg0);
    println!();
    println!("{}", KetosOpts::usage());
}

fn print_restrict_usage() {
    print!(
r#"The `-R` / `--restrict` option accepts a comma-separated list of parameters:

  permissive
    Applies "permissive" restrictions (default)

  strict
    Applies "strict" restrictions

  key=value
    Assigns a value to the named restriction configuration parameter.
    Accepted keys are:

      execution_time          Maximum execution time, in milliseconds
      call_stack_size         Maximum call frames
      value_stack_size        Maximum values stored on the stack
      namespace_size          Maximum values stored in global namespace
      memory_limit            Maximum total held memory, in abstract units
      max_integer_size        Maximum integer size, in bits
      max_syntax_nesting      Maximum nested syntax elements
"#);
}
