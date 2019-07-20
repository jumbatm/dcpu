//! Finds assembler's test directory, stopping the build if was not found correctly.
use std::path::PathBuf;
fn main() {
    let assembler_dir = {
        let mut assembler_dir = PathBuf::from(std::env::current_dir().unwrap());
        // We expect to find assembler's tests in ../tests/cases
        assembler_dir.pop();
        assembler_dir.push(std::path::PathBuf::from("tests"));
        assembler_dir.push(std::path::PathBuf::from("cases"));
        assert!(assembler_dir.metadata().unwrap().is_dir());
        assembler_dir
    };
    println!(
        "cargo:rustc-env=ASSEMBLER_TEST_ROOT={}",
        assembler_dir.as_path().display()
    )
}
