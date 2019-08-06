use assembler;
use std::path::PathBuf;
use integration_tester;

fn main() {
    for (input, output) in
        integration_tester::get_default_test_layout(PathBuf::from(assembler::integration_tests::get_root())).unwrap()
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
