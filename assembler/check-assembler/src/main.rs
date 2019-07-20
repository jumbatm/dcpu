use assembler;
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
    for (input, output) in check_assembler::get_test_dir_iter(PathBuf::from(
        std::env::var("ASSEMBLER_TEST_ROOT").unwrap(),
    ))
    .unwrap()
    {
        println!(
            "Generating {} from {}",
            output.as_path().display(),
            input.as_path().display()
        );
        let (input, mut output) = (
            std::io::BufReader::new(std::fs::File::open(input).unwrap()),
            std::io::BufWriter::new(std::fs::File::create(output).unwrap()),
        );
        let instruction_stream = assembler::InstructionStream::from(input);

        use std::io::Write;

        for inst in instruction_stream {
            output.write_fmt(format_args!("{:?}\n", inst)).unwrap();
        }
        output.flush().unwrap();
    }
}
