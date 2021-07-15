//! Companinon crate to ‘bintest' and 'testcall’, implements facilities for running tests in
//! directories.
//!
//!
//! # Description
//! Allows creating of (temporary) test directories, optionally with a custom callback for cleanup.
//! Populating these with content for testing and provide assertion to validate the content.
//!
//!
//! # Example
//!
//! ```ignore
//! fn test_something() {
//!     let tmpdir = TempDir::new().expect("TempDir created");
//!     tmpdir.create_file("path/to/testfile", "Hello File!".as_bytes());
//!     tmpdir
//!         .sub_path("path/to")
//!         .assert_exists("testfile")
//!         .assert_is_file("testfile");
//! }
//! ```
//!
//!
//! # TestPath
//!
//! A trait that augements Path for software testing. There are special implementations for
//! 'tempfile::TempDir' which creates temporary directories that get deletes when going out of
//! scope and TempDirCleanup which adds an custom cleanup callback to TempDir.
//!
//!
//! # SubPath
//!
//! SubPaths refer to pathnames within a TestPath and may not outlive the parent TestPath.
//!
//!
//! ## Fixtures
//!
//! Allow to populate a TestPath with content for testing.
//!
//!
//! ## PathAssertions
//!
//! Check and compare components of a TestPath for validty.
//!
//!
//! # Panics vs. Results
//!
//! 'testpath' is made explicitly for writing tests. To ease this it prefers aborting by panic
//! over error handling. When anything goes wrong the test is aborted and the cause is
//! reported.
//!
use std::fs;
use std::io;
use std::ops::Deref;
use std::path::{Path, PathBuf};
use tempfile::TempDir;

/// Trait for test directoy objects
pub trait TestPath {
    /// Return the underlying Path of an TestPath implementation
    fn path(&self) -> &Path;

    /// Return a canonalized/normalized PathBuf to components within the testpath. Assert and
    /// panic when path escapes from the testpath. Handles non existing components.
    #[track_caller]
    fn sub_path<P>(&self, subcomponents: P) -> SubPath
    where
        P: AsRef<Path> + Sized,
        Self: Sized,
    {
        let testpath = self.path();
        let subpath = PathBuf::from(&testpath)
            .join(subcomponents.as_ref())
            .normalize();
        assert!(subpath.starts_with(testpath), "escaped from testpath");
        SubPath {
            _testpath: self,
            subpath,
        }
    }

    /// Return a canonalized/normalized PathBuf to components within the testpath. Assert and
    /// panic when path escapes from the testpath. Asserts that the given subpath exists.
    #[track_caller]
    fn sub_path_exists<P>(&self, subcomponents: P) -> SubPath
    where
        P: AsRef<Path> + Sized,
        Self: Sized,
    {
        let path = self.sub_path(subcomponents);
        assert!(path.exists(), "path exists: {:?}", path.subpath);
        path
    }

    /// Return a canonalized/normalized PathBuf to components within the testpath. Assert and
    /// panic when path escapes from the testpath. Asserts that the given subpath does not exist.
    #[track_caller]
    fn sub_path_available<P>(&self, subcomponents: P) -> SubPath
    where
        P: AsRef<Path> + Sized,
        Self: Sized,
    {
        let path = self.sub_path(subcomponents);
        assert!(!path.exists(), "path does not exist: {:?}", path.subpath);
        path
    }
}

/// Trait for test directoy objects
pub trait Fixtures: TestPath {
    /// Create a file with the given content in the test directory. Any leading directories
    /// are created automatically. The file itself must not already exist.
    #[track_caller]
    fn create_file<P>(&self, name: P, content: &[u8]) -> &Self
    where
        P: AsRef<Path> + Sized,
        Self: Sized,
    {
        let path = self.sub_path_available(name);

        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent).expect("create directory");
        }

        fs::write(path.subpath, content).expect("create file");

        self
    }

    /// Create a directory within the test directory. Any leading directories
    /// are created automatically. The path must not exist already.
    #[track_caller]
    fn create_dir<P>(&self, name: P) -> &Self
    where
        P: AsRef<Path> + Sized,
        Self: Sized,
    {
        let path = self.sub_path_available(name);
        fs::create_dir_all(path).expect("create directory");
        self
    }

    /// Install something (from outside) into 'self'.
    /// 'from' must be some existing directory or a file, symlinks are resolved.
    ///
    /// Following semantics apply when `from` is a *file*:
    ///
    /// | self is     | What is done                                                                    |
    /// |-------------|---------------------------------------------------------------------------------|
    /// | nonexistant | `self` last component is the new filename, parent dirs are created              |
    /// | dir         | `from` is copied into `self`, but won't overwrite an existing file              |
    /// | file        | `self` gets overwritten                                                         |
    ///
    /// Following semantics apply when `from` is a *directory*:
    ///
    /// | self is     | What is done                                                                    |
    /// |-------------|---------------------------------------------------------------------------------|
    /// | nonexistant | `self` including parents are created, the content of `from` is copied into that |
    /// | dir         | the content of `from` is copied into `self`                                     |
    /// | file        | *ERROR*                                                                         |
    ///
    #[track_caller]
    fn install_from<P>(&self, from: P) -> &Self
    where
        P: AsRef<Path> + Sized,
        Self: Sized,
    {
        let from: PathBuf = if from.as_ref() == Path::new("") {
            PathBuf::from(".")
        } else {
            from.as_ref().normalize()
        };
        assert!(from.exists(), "source does not exist: {:?}", &from);

        if from.is_file() {
            if !self.path().exists() {
                if let Some(parent) = self.path().parent() {
                    fs::create_dir_all(parent).expect("create directories");
                }
                fs::copy(&from, self.path()).expect("file copied");
            }
            if self.path().is_file() {
                fs::copy(&from, self.path()).expect("file copied");
            } else if self.path().is_dir() {
                let target = PathBuf::from(self.path()).join(from.file_name().unwrap());
                assert!(
                    !target.exists(),
                    "won't overwrite existing file: {:?}",
                    &target
                );
                fs::copy(&from, &target).expect("file copied");
            } else {
                panic!("unsupported file type: {:?}", self.path());
            }
        } else if from.is_dir() {
            if !self.path().exists() {
                fs::create_dir_all(self.path()).expect("create directories");
                copy_all(&from, self.path());
            }
            if self.path().is_file() {
                panic!(
                    "cant not copy a dir into a file: {:?} -> {:?}",
                    &from,
                    self.path()
                );
            } else if self.path().is_dir() {
                copy_all(&from, self.path());
            } else {
                panic!("unsupported file type: {:?}", self.path());
            }
        } else {
            panic!("unsupported file type: {:?}", &from);
        }

        self
    }
}

/// Assertions on content of a TestPath
pub trait PathAssertions: TestPath {
    /// Assert that at the given path exists
    #[track_caller]
    fn assert_exists<P>(&self, subpath: &P) -> &Self
    where
        P: AsRef<Path> + ?Sized,
        Self: Sized,
    {
        let path = self.sub_path(subpath);
        assert!(path.exists(), "path exists");
        self
    }

    /// Assert that the given path does not exist
    #[track_caller]
    fn assert_available<P>(&self, subpath: &P) -> &Self
    where
        P: AsRef<Path> + ?Sized,
        Self: Sized,
    {
        let path = self.sub_path(subpath.as_ref());
        assert!(!path.exists(), "path does not exist");
        self
    }

    /// Assert that the given path is a directory
    #[track_caller]
    fn assert_is_dir<P>(&self, name: &P) -> &Self
    where
        P: AsRef<Path> + ?Sized,
        Self: Sized,
    {
        let path = self.sub_path_exists(name.as_ref());
        assert!(path.is_dir());
        self
    }

    /// Assert that the given path is a file
    #[track_caller]
    fn assert_is_file<P>(&self, name: &P) -> &Self
    where
        P: AsRef<Path> + ?Sized,
        Self: Sized,
    {
        let path = self.sub_path_exists(name.as_ref());
        assert!(path.is_file());
        self
    }

    /// Assert that the given path is a symlink
    #[track_caller]
    fn assert_is_symlink<P>(&self, name: &P) -> &Self
    where
        P: AsRef<Path> + ?Sized,
        Self: Sized,
    {
        let path = self.sub_path_exists(name.as_ref());
        assert!(path.symlink_metadata().unwrap().file_type().is_symlink());
        self
    }

    /// Assert that the given path resolves to a element of the given size
    #[track_caller]
    fn assert_size<P>(&self, name: &P, size: u64) -> &Self
    where
        P: AsRef<Path> + ?Sized,
        Self: Sized,
    {
        let path = self.sub_path_exists(name.as_ref());
        assert_eq!(path.metadata().unwrap().len(), size);
        self
    }

    /// Assert that the given path resolves to a element of more than the given size
    #[track_caller]
    fn assert_size_greater<P>(&self, name: &P, size: u64) -> &Self
    where
        P: AsRef<Path> + ?Sized,
        Self: Sized,
    {
        let path = self.sub_path_exists(name.as_ref());
        assert!(path.metadata().unwrap().len() > size);
        self
    }

    /// Assert that the given path resolves to a element of less than the given size
    #[track_caller]
    fn assert_size_smaller<P>(&self, name: &P, size: u64) -> &Self
    where
        P: AsRef<Path> + ?Sized,
        Self: Sized,
    {
        let path = self.sub_path_exists(name.as_ref());
        assert!(path.metadata().unwrap().len() < size);
        self
    }

    /// Assert that self contains exactly the same content than another path (directories are
    /// recursed).
    #[track_caller]
    fn assert_equal<M>(&self, with: &M) -> &Self
    where
        M: AsRef<Path> + ?Sized,
        Self: Sized,
    {
        let with: PathBuf = if with.as_ref() == Path::new("") {
            PathBuf::from(".")
        } else {
            with.as_ref().normalize()
        };

        compare_all(self.path(), with.as_ref(), ComparePolicy::Exact);

        self
    }

    /// Assert that self is is structurally equivalent to another path (contain the same
    /// files). File contents are not compared.
    #[track_caller]
    fn assert_structure<M>(&self, with: &M) -> &Self
    where
        M: AsRef<Path> + ?Sized,
        Self: Sized,
    {
        let with: PathBuf = if with.as_ref() == Path::new("") {
            PathBuf::from(".")
        } else {
            with.as_ref().normalize()
        };

        compare_all(self.path(), with.as_ref(), ComparePolicy::Structure);

        self
    }

    /// Assert that self contains the same content than another path for files that exist on
    /// both sides. Surplus files on either side are ignored.
    #[track_caller]
    fn assert_existing<M>(&self, with: &M) -> &Self
    where
        M: AsRef<Path> + ?Sized,
        Self: Sized,
    {
        let with: PathBuf = if with.as_ref() == Path::new("") {
            PathBuf::from(".")
        } else {
            with.as_ref().normalize()
        };

        compare_all(self.path(), with.as_ref(), ComparePolicy::Existing);

        self
    }
}

/// A Path that lives within a TestPath and must not outlive it.
pub struct SubPath<'a> {
    subpath: PathBuf,
    _testpath: &'a dyn TestPath, // contrains the lifetime to the parent
}

impl Deref for SubPath<'_> {
    type Target = PathBuf;
    fn deref(&self) -> &Self::Target {
        &self.subpath
    }
}

impl AsRef<Path> for SubPath<'_> {
    fn as_ref(&self) -> &Path {
        &self.subpath
    }
}

impl TestPath for Path {
    fn path(&self) -> &Path {
        self
    }
}

impl Fixtures for Path {}
impl PathAssertions for Path {}

impl TestPath for PathBuf {
    fn path(&self) -> &Path {
        self.as_path()
    }
}

impl Fixtures for PathBuf {}
impl PathAssertions for PathBuf {}

impl TestPath for TempDir {
    fn path(&self) -> &Path {
        self.path()
    }
}

impl Fixtures for TempDir {
    //TODO: implement rm
}
impl PathAssertions for TempDir {}

/// Augment a TempDir with a custom callback function that can do additional cleanup work
/// (like unmounting filesystem etc.)
pub struct TempDirCleanup {
    dir: TempDir,
    cleanup_fn: fn(&TempDir),
}

impl Drop for TempDirCleanup {
    fn drop(&mut self) {
        (self.cleanup_fn)(&self.dir);
    }
}

impl TestPath for TempDirCleanup {
    fn path(&self) -> &Path {
        self.dir.path()
    }
}

impl Fixtures for TempDirCleanup {
    //TODO: implement rm
}
impl PathAssertions for TempDirCleanup {}

impl TempDirCleanup {
    /// creates a temporary directory with a cleanup function to be called at drop time.
    //TODO: https://doc.rust-lang.org/std/panic/fn.catch_unwind.html
    pub fn new(cleanup_fn: fn(&TempDir)) -> io::Result<Self> {
        Ok(TempDirCleanup {
            dir: TempDir::new()?,
            cleanup_fn,
        })
    }
}

// normalize paths in rust including components that do not exist yet
trait PathNormalize {
    fn normalize(&self) -> PathBuf;
}

impl PathNormalize for Path {
    fn normalize(&self) -> PathBuf {
        use std::path::Component::*;
        let mut normalized = PathBuf::new();
        for component in self.components() {
            match component {
                Prefix(_) | RootDir | Normal(_) => normalized.push(component),
                CurDir => (),
                ParentDir => {
                    if let Some(_) = normalized.parent() {
                        normalized.pop();
                    }
                }
            }
            normalized = normalized.canonicalize().unwrap_or(normalized);
        }
        normalized
    }
}

/// copy the contents of 'from' into 'to', recursively, symlinks resolved, existing files
/// overwritten, errors panic
fn copy_all(from: &Path, to: &Path) {
    //PLANNED: use async/smol for parallel copy
    for entry in from.read_dir().expect("got dir iterator") {
        let entry = entry.expect("entry");
        let dest = PathBuf::from(to).join(entry.file_name());
        println!("dest is {:?}", dest);
        let entry = entry.path().canonicalize().expect("existing entry");
        if entry.is_file() {
            fs::copy(entry.path(), &dest).expect("file copied");
        } else if entry.is_dir() {
            fs::create_dir_all(&dest).expect("dir created");
            copy_all(&entry, &dest);
        } else {
            panic!("unsupported file type: {:?}", entry.path());
        }
    }
}

/// Policy when comparing directories:
///  * Exact
///    all files must exist on both sides and contain the same content
///  * ExistingExact
///    Only existing files are compared, when a file is missing on either side it gets ignored
///  * Presence
///    Checks only for presence on both sides, but don't compare the content
#[derive(Copy, Clone, PartialEq)]
enum ComparePolicy {
    Exact,
    Existing,
    Structure,
}

/// compare the contents of 'a' with 'b', recursively, symlinks resolved, existing files
/// overwritten, errors panic
fn compare_all(a: &Path, b: &Path, compare_policy: ComparePolicy) {
    if a.is_file() && b.is_file() {
        if compare_policy != ComparePolicy::Structure {
            compare_file(&a, &b);
        }
    } else if a.is_dir() && b.is_dir() {
        compare_dir(&a, &b, compare_policy);
    } else {
        panic!(
            "can't compare {:?} with {:?} because of different file types",
            &a, &b
        );
    }
}

fn compare_file(a: &Path, b: &Path) {
    use std::fs::File;
    use std::io::{BufReader, Read};

    let a_reader = BufReader::with_capacity(65536, File::open(a).expect("a is readable"));
    let b_reader = BufReader::with_capacity(65536, File::open(b).expect("b is readable"));
    for (index, bytes) in a_reader.bytes().zip(b_reader.bytes()).enumerate() {
        match bytes {
            (Ok(a_byte), Ok(b_byte)) => {
                assert_eq!(
                    a_byte, b_byte,
                    "file {:?} doesn't match file {:?} at byte {}",
                    a, b, index
                );
            }
            (Err(err), _) => {
                panic!("failed reading: {:?}, reason: {}", a, err);
            }
            (_, Err(err)) => {
                panic!("failed reading: {:?}, reason: {}", b, err);
            }
        };
    }
}

fn compare_dir(a: &Path, b: &Path, compare_policy: ComparePolicy) {
    use std::collections::HashSet;
    let a_contents = a
        .read_dir()
        .expect("a is a readable directory")
        .map(|a| a.expect("valid entry").file_name())
        .collect::<HashSet<_>>();

    let b_contents = b
        .read_dir()
        .expect("b is a readable directory")
        .map(|b| b.expect("valid entry").file_name())
        .collect::<HashSet<_>>();

    if compare_policy == ComparePolicy::Exact {
        assert_eq!(
            a_contents.symmetric_difference(&b_contents).next(),
            None,
            "directory content matches"
        );
    }

    a_contents.intersection(&b_contents).for_each(|name| {
        compare_all(
            &a.to_path_buf().join(name),
            &b.to_path_buf().join(name),
            compare_policy,
        )
    });
}

#[cfg(test)]
#[cfg(unix)]
mod test_internals {
    use super::*;

    #[test]
    fn path_normalize() {
        assert_eq!(Path::new(""), Path::new(".").normalize());
        assert_eq!(Path::new(""), Path::new("./").normalize());
        assert_eq!(Path::new(""), Path::new("./.").normalize());
        assert_eq!(Path::new("/foo/bar"), Path::new("/foo/bar").normalize());
        assert_eq!(Path::new("/foo"), Path::new("/foo/bar/..").normalize());
        assert_eq!(Path::new("/foo/bar"), Path::new("/foo/./bar/.").normalize());
        assert_ne!(Path::new("/foo/bar"), Path::new("/foo/bar/..").normalize());
        assert_eq!(Path::new("foo/bar"), Path::new("./foo/bar").normalize());
    }

    #[test]
    fn compare_file_same() {
        compare_file(Path::new("Cargo.toml"), Path::new("Cargo.toml"));
    }

    #[test]
    #[should_panic]
    fn compare_file_different() {
        compare_file(Path::new("Cargo.toml"), Path::new("Cargo.lock"));
    }

    #[test]
    fn compare_all_dir_dir_exact() {
        compare_all(Path::new("src"), Path::new("src"), ComparePolicy::Exact);
    }

    #[test]
    fn compare_all_dir_dir_existing() {
        compare_all(Path::new("src"), Path::new("src"), ComparePolicy::Existing);
    }

    #[test]
    fn compare_all_dir_dir_structure() {
        compare_all(Path::new("src"), Path::new("src"), ComparePolicy::Structure);
    }

    #[test]
    #[should_panic]
    fn compare_all_dir_file_fail() {
        compare_all(
            Path::new("src"),
            Path::new("Cargo.toml"),
            ComparePolicy::Structure,
        );
    }
}

#[cfg(test)]
#[cfg(unix)]
mod test_public_interface {
    use crate::*;
    use tempfile::TempDir;

    #[test]
    fn dircleanup() {
        let cleaned_up = {
            let tmpdir =
                TempDirCleanup::new(|_| println!("TempDir cleaned up")).expect("TempDir created");
            println!("TempDir path: {:?}", tmpdir.path());
            PathBuf::from(tmpdir.path())
        };

        assert!(!Path::new(&cleaned_up).exists(), "TempDir got deleted");
    }

    #[test]
    fn create_file() {
        let tmpdir = TempDir::new().expect("TempDir created");
        tmpdir.create_file("path/to/testfile", b"Hello File!");
        tmpdir.assert_exists("path/to/testfile");
    }

    #[test]
    fn create_file_in_sub_dir() {
        let tmpdir = TempDir::new().expect("TempDir created");
        let subdir = tmpdir.sub_path("path/to");
        subdir.create_file("testfile", b"Hello File!");
        tmpdir.assert_exists("path/to/testfile");
        subdir.assert_exists("testfile");
    }

    #[test]
    fn create_file_in_sub_dir_chained() {
        TempDir::new()
            .expect("TempDir created")
            .sub_path("path/to")
            .create_file("testfile", b"Hello File!")
            .assert_exists("testfile");
    }

    #[test]
    #[should_panic]
    fn create_file_fail() {
        let tmpdir = TempDir::new().expect("TempDir created");
        println!("TempDir path: {:?}", tmpdir.path());
        tmpdir.create_file("path/to/testfile", "Hello File!".as_bytes());
        tmpdir.assert_exists("path/to/wrongfile");
    }

    #[test]
    #[should_panic]
    fn create_file_again_fails() {
        let tmpdir = TempDir::new().expect("TempDir created");
        println!("TempDir path: {:?}", tmpdir.path());
        tmpdir.create_file("path/to/testfile", "Hello File!".as_bytes());
        tmpdir.create_file("path/to/testfile", "Hello File again!".as_bytes());
    }

    #[test]
    fn create_is_something() {
        let tmpdir = TempDir::new().expect("TempDir created");
        println!("TempDir path: {:?}", tmpdir.path());
        tmpdir.create_file("path/to/testfile", "Hello File!".as_bytes());
        tmpdir
            .assert_exists("path/to/testfile")
            .assert_is_file("path/to/testfile")
            .assert_is_dir("path/to");
    }

    #[test]
    fn create_dir() {
        let tmpdir = TempDir::new().expect("TempDir created");
        println!("TempDir path: {:?}", tmpdir.path());
        tmpdir.create_dir("path/to/test/dir");
        tmpdir.assert_is_dir("path/to/test/dir");
    }

    #[test]
    #[should_panic]
    fn install_from_nonexistant() {
        let tmpdir = TempDir::new().expect("TempDir created");
        tmpdir.install_from("doesnotexist");
    }

    #[test]
    fn install_from_file_to_dir() {
        let tmpdir = TempDir::new().expect("TempDir created");
        tmpdir.install_from("Cargo.toml");
        tmpdir.sub_path("Cargo.toml").assert_equal("Cargo.toml");
    }

    #[test]
    #[should_panic]
    fn install_from_file_to_dir_existing_file() {
        let tmpdir = TempDir::new().expect("TempDir created");
        tmpdir.create_file("Cargo.toml", "Hello File!".as_bytes());
        tmpdir.install_from("Cargo.toml");
    }

    #[test]
    fn install_from_file_to_file() {
        let tmpdir = TempDir::new().expect("TempDir created");
        tmpdir.create_file("testfile", "Hello File!".as_bytes());
        tmpdir.sub_path("testfile").install_from("Cargo.toml");
        tmpdir.sub_path("testfile").assert_equal("Cargo.toml");
    }

    #[test]
    fn install_from_file_to_nonexisting_dir() {
        let tmpdir = TempDir::new().expect("TempDir created");
        tmpdir
            .sub_path("subdir/Cargo.toml")
            .install_from("Cargo.toml");
        tmpdir
            .sub_path("subdir/Cargo.toml")
            .assert_equal("Cargo.toml");
    }

    #[test]
    fn install_from_dir_to_dir() {
        let tmpdir = TempDir::new().expect("TempDir created");
        tmpdir.install_from("src");
        tmpdir.assert_equal("src");
    }

    #[test]
    fn install_from_dir_to_nonexisting_dir() {
        let tmpdir = TempDir::new().expect("TempDir created");
        tmpdir.sub_path("src").install_from("src");
        tmpdir.sub_path("src").assert_equal("src");
    }

    #[test]
    fn install_from_dir_to_dir_overwriting_file() {
        let tmpdir = TempDir::new().expect("TempDir created");
        tmpdir.create_file("lib.rs", "Hello File!".as_bytes());
        tmpdir.install_from("src");
        tmpdir.assert_equal("src");
    }

    #[test]
    #[cfg(feature = "expensive_tests")]
    fn install_from_current_dir_to_dir() {
        let tmpdir = TempDir::new().expect("TempDir created");
        tmpdir.install_from("");
        tmpdir.sub_path("Cargo.toml").assert_equal("Cargo.toml");
    }

    #[test]
    fn install_from_dir_to_dir_structurecheck() {
        let tmpdir = TempDir::new().expect("TempDir created");
        tmpdir.install_from("src");
        tmpdir.assert_structure("src");
    }

    #[test]
    #[should_panic]
    fn install_from_dir_to_file() {
        let tmpdir = TempDir::new().expect("TempDir created");
        tmpdir.create_file("src", "Hello File!".as_bytes());
        tmpdir.sub_path("src").install_from("src");
    }
}
