extern crate ketos;

use ketos::{BuiltinModuleLoader, Error, FileModuleLoader, Interpreter, ModuleLoader};

use std::fs::read_dir;
use std::path::{Path, PathBuf};

fn run_file(path: &Path) -> Result<(), Error> {
    let mut loader = FileModuleLoader::with_search_paths(vec![PathBuf::from("lib")]);

    loader.set_read_bytecode(false);
    loader.set_write_bytecode(false);

    let interp = Interpreter::with_loader(Box::new(BuiltinModuleLoader.chain(loader)));

    interp.run_file(path)
}

// Runs all the tests matching `lib/test-*.ket`
#[test]
fn test_run() {
    let dir = read_dir("lib").expect("failed to read dir");

    for ent in dir {
        let ent = ent.expect("failed to read dir entry");
        let fname = ent.file_name();
        let name = fname
            .to_str()
            .expect("failed to convert filename to string");

        if name.starts_with("test-") && name.ends_with(".ket") {
            run_file(&ent.path()).unwrap();
        }
    }
}
