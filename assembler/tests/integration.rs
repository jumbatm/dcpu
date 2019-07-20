fn prepare_test_dirs() -> Result<impl Iterator, std::io::Error> {
    // Check to see if it already exists.
    let expected = {
        let mut expected = std::env::current_dir()?;
        expected.push(std::path::Path::new("generate"));
        expected
    };
    if !expected.as_path().exists() {
        // Create a folder here.
        std::fs::create_dir(expected.as_path())?;
    } else {
        // Ensure it's a folder.
        assert!(expected.metadata()?.is_dir());
    }
    // Now, check to make sure the test directory exists.
    let test_inputs = {
        let mut test_inputs = std::env::current_dir()?;
        test_inputs.push(std::path::Path::new("test_inputs"));
        test_inputs
    };
    assert!(test_inputs.metadata()?.is_dir());

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
        }))
}
