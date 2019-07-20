use std::path::PathBuf;
use structopt;
use structopt::StructOpt;

/// A basic example
#[derive(StructOpt, Debug)]
#[structopt(name = "basic")]
struct Opt {
    /// Output file
    #[structopt(parse(from_os_str))]
    output: PathBuf,
}

fn main() {
    let opt = Opt::from_args();
    for (input, output) in check_assembler::get_test_dir_iter(opt.output).unwrap() {
        /*
        // Open input for reading.
        let input = std::fs::File::open(input).unwrap();
        // Open output file for writing.
        let output = std::fs::File::create(output);
        */
        println!(
            "{}, {}",
            input.as_path().display(),
            output.as_path().display()
        );
    }
}
