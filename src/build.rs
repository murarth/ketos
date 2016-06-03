extern crate syntex;
extern crate serde_codegen;

use std::env::var_os;
use std::path::Path;

const FILES: &'static [(&'static str, &'static str)] = &[
    ("tests/value_encode.rs.in", "value_encode.rs"),
];

fn main() {
    let out_dir = var_os("OUT_DIR").unwrap();

    for &(src, dest) in FILES {
        let mut registry = syntex::Registry::new();

        serde_codegen::register(&mut registry);

        registry.expand("",
            &Path::new(src),
            &Path::new(&out_dir).join(dest)).unwrap();
    }
}
