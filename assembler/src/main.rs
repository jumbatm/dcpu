use assembler::InstructionStream;
use structopt;

use std::path::PathBuf;
use structopt::StructOpt;

/// A basic example
#[derive(StructOpt, Debug)]
#[structopt(name = "basic")]
struct Opt {
    // A flag, true if used in the command line. Note doc comment will
    // be used for the help message of the flag.
    /// Activate debug mode
    #[structopt(short = "d", long = "debug")]
    debug: bool,

    /// Files to process
    #[structopt(name = "FILE", parse(from_os_str))]
    files: Vec<PathBuf>,

    /// Output file
    #[structopt(short = "o", long = "output", parse(from_os_str))]
    output: Option<PathBuf>,
}

fn main() {
    let opt = Opt::from_args();
    for file in opt.files {
        let f = std::fs::File::open(file).expect("Error opening file.");
        let stream = InstructionStream::from(f);
        for inst in stream {
            match inst {
                Ok(inst) => {
                    println!("{:?}", inst);
                }
                Err(e) => {
                    if let assembler::ErrorType::SyntaxError(c) = e.error {
                        println!(
                            "{}:{}: Syntax error just before {}",
                            e.line_no,
                            e.col_no,
                            c.unwrap() as char,
                        );
                    } else {
                        panic!(e);
                    }
                    break;
                }
            }
        }
    }
}
