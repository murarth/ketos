//! Wrapper to GNU Readline library

use std::cell::Cell;
use std::mem::{size_of, transmute};
use std::ffi::{CStr, CString};
use std::ptr;
use std::slice;
use std::str::from_utf8;
use std::sync::{Once, ONCE_INIT};

use libc::{self, c_char, c_int, size_t};
use ketos::scope::GlobalScope;

use completion::complete;

static INIT_READLINE: Once = ONCE_INIT;

/// Readline completion function. Called to perform text completion.
/// Takes arguments `text` (segment of input being completed),
/// `start` (start of input within line buffer),
/// and `end` (end of input within line buffer).
/// Returns an array whose first element is the substitution text
/// (e.g. longest common prefix) and whose remaining elements are possible
/// substitutions and which is terminated by a NULL element.
type RlCompletionFn = extern "C" fn(*const c_char, c_int, c_int) -> *mut *const c_char;

#[link(name = "readline")]
extern "C" {
    static mut rl_attempted_completion_function: RlCompletionFn;
    static mut rl_attempted_completion_over: c_int;
    static mut rl_basic_word_break_characters: *const c_char;
    static mut rl_line_buffer: *mut c_char;

    // The static variable `rl_basic_quote_characters` is not present in BSD
    // versions of libreadline.
    #[cfg(not(any(
        target_os = "macos", target_os = "ios", target_os = "dragonfly",
        target_os = "freebsd", target_os = "openbsd", target_os = "netbsd")))]
    static mut rl_basic_quote_characters: *const c_char;

    #[link_name = "add_history"]
    fn rl_add_history(line: *const c_char);
    #[link_name = "readline"]
    fn rl_readline(prompt: *const c_char) -> *const c_char;
    fn rl_insert_text(text: *const c_char) -> c_int;
    fn rl_variable_bind(var: *const c_char, value: *const c_char) -> c_int;
}

fn init_readline() {
    unsafe {
        // Set up our custom completion function.
        rl_attempted_completion_function = completion_fn;
        // Set up word break characters.
        // These are anything not permitted in identifiers.
        rl_basic_word_break_characters =
            b" \t\n#\"'(),:;@[\\]`{}\0" // NUL-terminated
            .as_ptr() as *const _;

        init_quote_characters();

        // Blink open paren when a closing paren is typed.
        rl_variable_bind(b"blink-matching-paren\0".as_ptr() as *const _,
            b"on\0".as_ptr() as *const _);
    }
}

#[cfg(any(
    target_os = "macos", target_os = "ios", target_os = "dragonfly",
    target_os = "freebsd", target_os = "openbsd", target_os = "netbsd"))]
unsafe fn init_quote_characters() {}

#[cfg(not(any(
    target_os = "macos", target_os = "ios", target_os = "dragonfly",
    target_os = "freebsd", target_os = "openbsd", target_os = "netbsd")))]
unsafe fn init_quote_characters() {
    // Inform readline that only a double-quote begins a string.
    // This tells it that `'foo` does not constitute an unclosed string,
    // which would otherwise inhibit matching paren blinking.
    // Unfortunately, this also means that it does not recognize true
    // character constants and will get confused with unbalanced
    // single-quoted parentheses. However, this is less troublesome
    // than the alternative.
    rl_basic_quote_characters = b"\"\0".as_ptr() as *const _;
}

/// Pushes a single line into `readline` history.
pub fn push_history(line: &str) {
    let line = CString::new(line.as_bytes()).unwrap();
    unsafe { rl_add_history(line.as_ptr()) };
}

/// Reads a line from the input stream. The result will not contain a trailing
/// newline. Returns `None` if end-of-file is signaled.
pub fn read_line(prompt: &str, gscope: &GlobalScope) -> Option<String> {
    INIT_READLINE.call_once(init_readline);

    // readline won't help us in passing this to the completion function,
    // so we tuck it away for just a short while in thread-local storage.
    unsafe { put_global_scope(gscope); }

    let pr = CString::new(prompt.as_bytes()).unwrap();
    let sp = unsafe { rl_readline(pr.as_ptr()) };

    // ... And clear it when we're done.
    clear_global_scope();

    if sp.is_null() {
        None
    } else {
        let cs = unsafe { CStr::from_ptr(sp) };
        Some(from_utf8(cs.to_bytes()).unwrap().to_owned())
    }
}

/// When `read_line` is called, the supplied `GlobalScope` is stored here,
/// transmuted to a `'static` lifetime. It is held only as long as the call into
/// libreadline. The `GlobalScope` is used by our completion function to
/// list available named values.
thread_local!(static GLOBAL_SCOPE: Cell<Option<&'static GlobalScope>> = Cell::new(None));

/// Clears the stored `&'static GlobalScope`.
fn clear_global_scope() {
    GLOBAL_SCOPE.with(|key| key.set(None));
}

/// Returns the stored `&'static GlobalScope`, if available.
fn get_global_scope() -> Option<&'static GlobalScope> {
    GLOBAL_SCOPE.with(|key| key.get())
}

/// Stores a `&GlobalScope` for access by our completion functions.
///
/// This function is marked unsafe because the caller must guarantee
/// that `clear_global_scope` is called before returning.
unsafe fn put_global_scope(scope: &GlobalScope) {
    GLOBAL_SCOPE.with(|key| key.set(Some(transmute(scope))));
}

/// This function is called by libreadline to perform completion.
///
/// The result, if not `NULL` is a vector of null-terminated strings which
/// becomes wholly owned by libreadline and is therefore allocated using `malloc`.
extern "C" fn completion_fn(text: *const c_char, start: c_int, end: c_int) -> *mut *const c_char {
    unsafe {
        // Prevent readline from calling its default completion function
        // if this function returns NULL.
        rl_attempted_completion_over = 1;
    }

    let input = unsafe { CStr::from_ptr(rl_line_buffer) };
    let text = unsafe { CStr::from_ptr(text) };

    let input_bytes = input.to_bytes();

    // Tab with no text inserts indentation
    if input_bytes.iter().all(|&b| (b as char).is_whitespace()) {
        let indent = b"  \0";
        unsafe { rl_insert_text(
            indent[input_bytes.len() % 2..].as_ptr() as *const _) };
    }

    let start = start as usize;
    let end = end as usize;

    let scope = get_global_scope().expect("missing thread-local GlobalScope");

    let input = from_utf8(input.to_bytes()).unwrap();
    let (prefix, completions) = match complete(input, start, end, scope) {
        Some(r) => r,
        None => return ptr::null_mut()
    };

    let text = from_utf8(text.to_bytes()).unwrap();

    unsafe {
        let size = size_of::<*const c_char>();
        let n = completions.len() + 2;  // +1 for the prefix, +1 for the leading nullptr
        let buf = libc::calloc(n as size_t, size as size_t) as *mut *const c_char;
        let s = slice::from_raw_parts_mut(buf, n);

        /// Allocates space for the given string and copies it into it.
        /// Also appends a terminating zero.
        unsafe fn c_str(s: &str) -> *const c_char {
            let len = s.as_bytes().len();
            let dest = libc::malloc((len + 1) as size_t) as *mut c_char;
            ptr::copy_nonoverlapping(s.as_bytes().as_ptr() as *const c_char, dest, len);

            ptr::write(dest.offset(len as isize), 0 as c_char);
            dest
        }

        {
            s[0] = c_str(&format!("{}{}", text, prefix));

            let mut i = 1;
            for c in completions {
                let completion = format!("{}{}", text, c);
                s[i] = c_str(&completion);
                i += 1;
            }

            // Last element remains NULL
        }

        buf
    }
}
