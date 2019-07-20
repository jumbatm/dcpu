use assembler;
use testutil;
#[test]
fn run_check_assembler() {
    for (case, expected) in
        testutil::get_test_dir_iter(std::path::PathBuf::from(testutil::get_assembler_test_dir()))
            .unwrap()
            .map(|(case_path, expected_path)| {
                (
                    std::io::BufReader::new(
                        std::fs::File::open(case_path).expect("Incorrect case path."),
                    ),
                    std::fs::read_to_string(expected_path).expect("Incorrect expected path."),
                )
            })
    {
        let insts = assembler::InstructionStream::from(case);

        let mut case = String::new();

        for inst in insts {
            use std::fmt::Write;
            case.write_fmt(format_args!("{:?}\n", inst)).unwrap();
        }
        // We generate a comparison string.
        assert_eq!(case, expected);
    }
}
