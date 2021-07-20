Companinon crate to ‘bintest' and 'testcall’, implements facilities for running tests in
directories.

# Description

Allows creating of (temporary) test directories, optionally with a custom callback for cleanup.
Populating these with content for testing and provide assertion to validate the content.

# Example

```rust
#[test]
fn test_something() {
    let tmpdir = TempDir::new().expect("TempDir created");
    tmpdir.create_file("path/to/testfile", "Hello File!".as_bytes());
    tmpdir
        .sub_path("path/to/testfile")
        .assert_utf8("Hello File!");
}
```

# Future Plans

New features will be added as needed, PR’s are welcome. This is work in progress.
