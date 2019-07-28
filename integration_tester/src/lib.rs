/// Prepares the test directory.
pub fn get_test_dir_iter(
    test_inputs: std::path::PathBuf,
) -> Result<impl Iterator<Item = (std::path::PathBuf, std::path::PathBuf)>, std::io::Error> {
    // Check to make sure the test directory exists and that it's a folder.
    assert!(test_inputs.metadata()?.is_dir());

    // Now check that the expected folder exists.
    let expected = {
        let mut expected = test_inputs.to_path_buf();
        // Go up one dir, to the parent of test_inputs.
        expected.pop();
        // Go forwards into a new path called expected.
        expected.push(std::path::Path::new("expected"));
        expected
    };
    if !expected.as_path().exists() {
        // Create a folder here.
        std::fs::create_dir(expected.as_path())?;
    } else {
        // Ensure it's a folder.
        assert!(expected.metadata()?.is_dir());
    }

    Ok(std::fs::read_dir(test_inputs)
        .unwrap()
        .filter_map(move |dir_entry_result| {
            dir_entry_result
                .ok()
                .and_then(|dir_entry| {
                    if dir_entry.metadata().ok()?.is_file() {
                        Some(dir_entry.path())
                    } else {
                        None
                    }
                })
                .and_then(|input| {
                    let output = {
                        let file_name = input.file_name()?;
                        let expected = expected.to_path_buf().join(file_name);
                        expected
                    };
                    Some((input, output))
                })
        })
        .into_iter())
}
