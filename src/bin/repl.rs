extern crate getopts;
extern crate ketos;
extern crate libc;

use std::env::{split_paths, var_os};
use std::io::{stderr, Write};
use std::path::{Path, PathBuf};

use getopts::{Options, ParsingStyle};
use ketos::{Interpreter, Error, ParseErrorKind, take_traceback};

mod completion;
mod readline;

fn main() {
    let status = run();
    std::process::exit(status);
}

fn run() -> i32 {
    let args = std::env::args().collect::<Vec<_>>();
    let mut opts = Options::new();

    // Allow arguments that appear to be options to be passed to scripts
    opts.parsing_style(ParsingStyle::StopAtFirstFree);

    opts.optopt  ("e", "", "Evaluate one expression and exit", "EXPR");
    opts.optflag ("h", "help", "Print this help message and exit");
    opts.optflag ("i", "interactive", "Run interactively even with a file");
    opts.optmulti("I", "", "Add DIR to list of module search paths", "DIR");
    opts.optflag ("", "no-rc", "Do not run ~/.ketosrc.ket on startup");
    opts.optflag ("V", "version", "Print version and exit");

    let matches = match opts.parse(&args[1..]) {
        Ok(m) => m,
        Err(e) => {
            let _ = writeln!(stderr(), "{}: {}", args[0], e);
            return 1;
        }
    };

    if matches.opt_present("version") {
        print_version();
        return 0;
    }
    if matches.opt_present("help") {
        print_usage(&args[0], &opts);
        return 0;
    }

    // Search current directory first
    let mut paths = vec![PathBuf::new()];

    if let Some(p) = var_os("KETOS_PATH") {
        paths.extend(split_paths(&p));
    }

    paths.extend(matches.opt_strs("I").into_iter().map(PathBuf::from));

    let interp = Interpreter::with_search_paths(paths);

    let interactive = matches.opt_present("interactive") ||
        (matches.free.is_empty() && !matches.opt_present("e"));

    if let Some(expr) = matches.opt_str("e") {
        if !run_expr(&interp, &expr) && !interactive {
            return 1;
        }
    } else if !matches.free.is_empty() {
        interp.set_args(&matches.free[1..]);
        if !run_file(&interp, Path::new(&matches.free[0])) && !interactive {
            return 1;
        }
    }

    if interactive {
        if !matches.opt_present("no-rc") {
            if let Some(p) = std::env::home_dir() {
                let rc = p.join(".ketosrc.ket");
                if rc.is_file() {
                    // Ignore error in interactive mode
                    run_file(&interp, &rc);
                }
            }
        }

        run_repl(&interp);
    }

    0
}

fn display_error(interp: &Interpreter, e: &Error) {
    if let Some(trace) = take_traceback() {
        interp.display_trace(&trace);
    }
    interp.display_error(e);
}

fn run_expr(interp: &Interpreter, expr: &str) -> bool {
    match interp.run_code(expr, None) {
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

#[derive(Copy, Clone)]
enum Prompt {
    Normal,
    OpenComment,
    OpenParen,
    OpenString,
}

fn read_line(interp: &Interpreter, prompt: Prompt) -> Option<String> {
    let prompt = match prompt {
        Prompt::Normal => "ketos=> ",
        Prompt::OpenComment => "ketos#> ",
        Prompt::OpenParen => "ketos(> ",
        Prompt::OpenString => "ketos\"> ",
    };

    readline::read_line(prompt, interp.get_scope())
}

fn run_repl(interp: &Interpreter) {
    let mut buf = String::new();
    let mut prompt = Prompt::Normal;

    while let Some(line) = read_line(interp, prompt) {
        if line.chars().all(|c| c.is_whitespace()) {
            continue;
        }

        readline::push_history(&line);
        buf.push_str(&line);
        buf.push('\n');

        match interp.compile_exprs(&buf) {
            Ok(code) => {
                prompt = Prompt::Normal;
                if !code.is_empty() {
                    match interp.execute_program(code) {
                        Ok(v) => interp.display_value(&v),
                        Err(e) => display_error(&interp, &e)
                    }
                }
            }
            Err(Error::ParseError(ref e)) if e.kind == ParseErrorKind::MissingCloseParen => {
                prompt = Prompt::OpenParen;
                continue;
            }
            Err(Error::ParseError(ref e)) if e.kind == ParseErrorKind::UnterminatedComment => {
                prompt = Prompt::OpenComment;
                continue;
            }
            Err(Error::ParseError(ref e)) if e.kind == ParseErrorKind::UnterminatedString => {
                prompt = Prompt::OpenString;
                continue;
            }
            Err(ref e) => display_error(&interp, e)
        }

        buf.clear();
        interp.clear_codemap();
    }

    println!("");
}

fn print_version() {
    println!("ketos {}", version());
}

fn version() -> &'static str {
    env!("CARGO_PKG_VERSION")
}

fn print_usage(arg0: &str, opts: &Options) {
    print!("{}", opts.usage(&format!("Usage: {} [OPTIONS] [FILE]", arg0)));
}
