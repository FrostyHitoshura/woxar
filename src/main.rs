//! Might and Magic: World of Xeen Archiver. Implemented based on documentation available at:
//!
//! https://xeen.fandom.com/wiki/CC_File_Format

use anyhow::{anyhow, bail, ensure, Context};
use bitvec::{prelude::*, vec::BitVec};
use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};
use clap::{
    App, Arg, ArgMatches, Error as ClapError,
    ErrorKind::{HelpDisplayed, VersionDisplayed},
    SubCommand,
};
use smallvec::SmallVec;
use std::{
    collections::{btree_map::Entry::Vacant, BTreeMap},
    convert::TryFrom,
    env,
    ffi::OsStr,
    fmt::Display,
    fs::File,
    io::{
        stdin, stderr, stdout, Cursor, Error as IoError, Read, Seek, SeekFrom, Write,
    },
    path::Path,
    process::exit,
    str, u16,
};
use thiserror::Error;
use vfs::{PhysicalFS, VfsPath};

use woxar::name::{WoxName, WoxHashedName, WoxReverseDictionary, ReadWoxReverseDictionary, WoxNameError};

const VERSION: &str = env!("CARGO_PKG_VERSION");
const AUTHOR: &str = env!("CARGO_PKG_AUTHORS");

#[derive(Debug, Error)]
enum WoxError {
    #[error("Invalid file name")]
    InvalidFileName(#[from] WoxNameError),
    #[error("Found invalid data in the table of contents")]
    ReadToc,
    #[error("Can't encode file '{0}' as hash {1:#06x} is already in use")]
    GenerateToc(String, WoxHashedName),
    #[error("Hit a race condition")]
    Race,
    #[error("The former has {0} file(s) while the latter has {1} file(s)")]
    DifferentFileCount(usize, usize),
    #[error("The table of contents differs")]
    TocDiffers,
    #[error("One or more file content differs")]
    ContentDiffers,
    #[error("Failed to find file hash {0} in archive")]
    NoHash(WoxHashedName),
    #[error("Requires 2 or more archives to compare")]
    Requires2PlusFiles,
    #[error("No subcommand provided")]
    NoSubcommand,
    #[error("Archives '{0}' and '{1}' differ")]
    ArchivesDiffer(String, String),
}

const ROTATE_ADD_INITIAL: u8 = 0xac;

// None for Crypt: Used for the initial 2 bytes of the file
#[derive(Clone)]
enum Crypt {
    RotateAdd(u8), // Used for the table of contents
    Xor,           // Used for the file contents
}

type FileCount = u16;
type FileSize = u16;

struct Contents {
    data: Vec<u8>,
    list: WoxReverseDictionary,
}

#[derive(PartialEq, Debug)]
enum Direction {
    Read,
    Write,
}

struct Decrypt<S> {
    cursor: S,
    crypt: Option<Crypt>,
}

struct Encrypt<S> {
    sink: S,
    crypt: Option<Crypt>,
}

#[derive(Copy, Clone)]
struct TocEntry {
    id: WoxHashedName,
    offset: u32, // XXX: Actually an u24...
    len: FileSize,
    // In the file... padding: u8 which is expected to be always 0
}

struct TocIter<'a> {
    cursor: Decrypt<Cursor<&'a [u8]>>,
    idx: usize,
    total: usize,

    // A bit array where we keep track of all seen hashes.
    verify: BitVec,
}

struct PayloadIter<'a> {
    toc: TocIter<'a>,
    contents_crypt: Option<Crypt>,
    contents: &'a Contents,
}

struct PayloadBufferedIter<'a> {
    tocs: Vec<TocEntry>,
    idx: usize,
    contents: &'a Contents,
    contents_crypt: Option<Crypt>,
}

impl Contents {
    fn new(data: Vec<u8>, list: WoxReverseDictionary) -> Contents {
        Contents { data, list }
    }

    fn find_entry(&self, hash: WoxHashedName) -> Option<&WoxName> {
        self.list.inner().get(&hash)
    }

    fn entry_name(&self, entry: &TocEntry) -> String {
        match self.find_entry(entry.id) {
            Some(entry) => entry.inner().to_owned(),
            None => format!("{}", entry.id),
        }
    }

    fn read_cursor_at(
        &self,
        offset: u64,
        crypt: Option<Crypt>,
    ) -> Result<Decrypt<Cursor<&[u8]>>, IoError> {
        let mut decrypt = Decrypt::new(Cursor::new(self.data.as_slice()), crypt);
        decrypt.seek(SeekFrom::Start(offset))?;
        Ok(decrypt)
    }

    fn read_cursor(&self) -> Decrypt<Cursor<&[u8]>> {
        Decrypt::new(Cursor::new(&self.data), None)
    }

    fn file_count(&self) -> Result<FileCount, IoError> {
        self.read_cursor().read_u16::<LittleEndian>()
    }

    fn toc_iter(&self) -> Result<TocIter, IoError> {
        let mut cursor = self.read_cursor();

        // XXX: Remplace with self.file_count()
        let total = cursor.read_u16::<LittleEndian>()? as usize;

        cursor.crypt = Some(Crypt::RotateAdd(ROTATE_ADD_INITIAL));

        Ok(TocIter {
            cursor,
            idx: 0,
            total,
            verify: bitvec![0; WoxHashedName::MAX as usize],
        })
    }

    fn payload_iter(&self, contents_crypt: Option<Crypt>) -> Result<PayloadIter, anyhow::Error> {
        Ok(PayloadIter {
            toc: self.toc_iter()?,
            contents_crypt,
            contents: self,
        })
    }

    fn payload_filtered_ordered_iter(
        &self,
        hashes: &[WoxHashedName],
        contents_crypt: Option<Crypt>,
    ) -> Result<PayloadBufferedIter, anyhow::Error> {
        // Read the whole toc and save the entries we are interested for
        // XXX: This is suboptimal: if we found all the entries, we can stop reading the toc
        // XXX: We clone TocEntry 2 times in this function, looks excessive
        let mut acc: Vec<Option<TocEntry>> = vec![None; hashes.len()];
        for entry_result in self.toc_iter()? {
            let entry = entry_result?;

            hashes.iter().enumerate().for_each(|(idx, hash)| {
                if entry.id == *hash {
                    acc[idx] = Some(entry);
                }
            });
        }

        let results = acc
            .iter()
            .enumerate()
            .map(|(idx, optional_entry)| {
                if let Some(entry) = optional_entry {
                    Ok(*entry)
                } else {
                    // XXX: Improve error message
                    Err(WoxError::NoHash(hashes[idx]))
                }
            })
            .collect::<Result<Vec<TocEntry>, WoxError>>()?;

        Ok(PayloadBufferedIter {
            tocs: results,
            idx: 0,
            contents: self,
            contents_crypt,
        })
    }

    fn fetch_payload(
        &self,
        entry: &TocEntry,
        crypt: Option<Crypt>,
    ) -> Result<Vec<u8>, anyhow::Error> {
        let mut payload = vec![0; entry.len as usize];

        self.read_cursor_at(entry.offset as u64, crypt)?
            .read_exact(&mut payload)?;

        Ok(payload)
    }
}

impl Crypt {
    fn crypt_byte(&mut self, direction: Direction, byte: u8) -> u8 {
        const ROTATE: u32 = 6;
        const ADD: u8 = 0x67;

        match (direction, self) {
            (Direction::Read, Crypt::RotateAdd(ref mut state)) => {
                let decrypted = u8::wrapping_add(byte.rotate_right(ROTATE), *state);
                *state = u8::wrapping_add(*state, ADD);

                decrypted
            }
            (Direction::Write, Crypt::RotateAdd(ref mut state)) => {
                let crypted = u8::wrapping_sub(byte, *state).rotate_left(ROTATE);
                *state = u8::wrapping_add(*state, ADD);

                crypted
            }
            (_, Crypt::Xor) => byte ^ 0x35,
        }
    }
}

fn crypt(optional_crypt: &mut Option<Crypt>, direction: Direction, byte: u8) -> u8 {
    optional_crypt
        .as_mut()
        .map_or(byte, |crypt| crypt.crypt_byte(direction, byte))
}

impl<S> Decrypt<S> {
    fn new(cursor: S, crypt: Option<Crypt>) -> Self {
        Self { cursor, crypt }
    }
}

impl<S> Read for Decrypt<S>
where
    S: Read,
{
    fn read(&mut self, buf: &mut [u8]) -> Result<usize, IoError> {
        let bytes_read = self.cursor.read(buf)?;

        buf[..bytes_read]
            .iter_mut()
            .for_each(|byte| *byte = crypt(&mut self.crypt, Direction::Read, *byte));

        Ok(bytes_read)
    }
}

impl<S> Seek for Decrypt<S>
where
    S: Seek,
{
    fn seek(&mut self, pos: SeekFrom) -> Result<u64, IoError> {
        self.cursor.seek(pos)
    }
}

impl<S> Encrypt<S> {
    fn new(sink: S, crypt: Option<Crypt>) -> Self {
        Self { sink, crypt }
    }
}

impl<S> Write for Encrypt<S>
where
    S: Write,
{
    fn write(&mut self, buf: &[u8]) -> Result<usize, IoError> {
        let crypted = buf
            .iter()
            .map(|byte| crypt(&mut self.crypt, Direction::Write, *byte))
            .collect::<Vec<u8>>();

        self.sink.write_all(&crypted)?;

        Ok(buf.len())
    }

    fn flush(&mut self) -> Result<(), IoError> {
        self.sink.flush()
    }
}

impl TocEntry {
    fn new<S>(source: &mut S) -> Result<TocEntry, anyhow::Error>
    where
        S: Read,
    {
        let entry = TocEntry {
            id: WoxHashedName::from(source.read_u16::<LittleEndian>()?),
            offset: source.read_u24::<LittleEndian>()?,
            len: source.read_u16::<LittleEndian>()?,
        };

        // Ensure that the padding byte is set to 0
        if source.read_u8()? != 0 {
            bail!(WoxError::ReadToc)
        } else {
            Ok(entry)
        }
    }

    fn write<S>(&self, sink: &mut S) -> Result<(), IoError>
    where
        S: Write,
    {
        sink.write_u16::<LittleEndian>(self.id.raw())?;
        sink.write_u24::<LittleEndian>(self.offset)?;
        sink.write_u16::<LittleEndian>(self.len)?;
        sink.write_u8(0)
    }
}

impl<'a> Iterator for TocIter<'a> {
    type Item = Result<TocEntry, anyhow::Error>;

    fn next(&mut self) -> Option<Self::Item> {
        self.idx += 1;

        if self.idx <= self.total {
            Some(TocEntry::new(&mut self.cursor).and_then(|entry| {
                let bit = entry.id.raw() as usize;

                if self.verify[bit] {
                    Err(anyhow!(WoxError::ReadToc))
                } else {
                    self.verify.set(bit, true);
                    Ok(entry)
                }
            }))
        } else {
            None
        }
    }
}

impl<'a> Iterator for PayloadIter<'a> {
    type Item = Result<(TocEntry, Vec<u8>), anyhow::Error>;

    fn next(&mut self) -> Option<Self::Item> {
        self.toc.next().map(|entry_result| {
            entry_result.and_then(|entry| {
                self.contents
                    .fetch_payload(&entry, self.contents_crypt.clone())
                    .map(|decrypted| (entry, decrypted))
            })
        })
    }
}

impl<'a> Iterator for PayloadBufferedIter<'a> {
    type Item = Result<(TocEntry, Vec<u8>), anyhow::Error>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.idx < self.tocs.len() {
            let toc = self.tocs[self.idx];
            self.idx += 1;

            Some(
                self.contents
                    .fetch_payload(&toc, self.contents_crypt.clone())
                    .map(|decrypted| (toc, decrypted)),
            )
        } else {
            None
        }
    }
}

fn extract_cc_file<A, S, L>(
    stdout: &mut S,
    archive_stream: &mut A,
    list_stream: L,
    root_directory: &VfsPath,
    hashes_to_extract: &[WoxHashedName],
    contents_crypt: Option<Crypt>,
) -> Result<(), anyhow::Error>
where
    A: Read,
    S: Write,
    L: Read,
{
    let mut data = Vec::<u8>::new();
    archive_stream.read_to_end(&mut data)?;

    let contents = Contents::new(data, WoxReverseDictionary::try_from(ReadWoxReverseDictionary(list_stream))?);

    root_directory.create_dir_all()?;

    if !hashes_to_extract.is_empty() {
        // Extract specific files arm: writing order is important to respect the order the user set
        // by the user on the command line
        contents
            .payload_filtered_ordered_iter(hashes_to_extract, contents_crypt)?
            .try_for_each(
                |payload_result: Result<(TocEntry, Vec<u8>), anyhow::Error>| -> Result<(), anyhow::Error> {
                    let (_entry, contents) = payload_result?;
                    stdout.write_all(&contents)?;
                    Ok(())
                },
            )
    } else {
        // Extract all files arm: writing order isn't important
        contents.payload_iter(contents_crypt)?.try_for_each(
            |payload_result: Result<(TocEntry, Vec<u8>), anyhow::Error>| -> Result<(), anyhow::Error> {
                let payload = payload_result?;
                let mut file = 
                    root_directory.join(&contents.entry_name(&payload.0))?.create_file()?;

                file.write_all(&payload.1)?;
                Ok(())
            },
        )
    }
}

struct FilePayload {
    entry: TocEntry,
    payload: Vec<u8>,
}

fn create_cc_file<W: Write>(
    archive_writer: W,
    root_directory: &VfsPath,
    contents_crypt: Option<Crypt>,
) -> Result<(), anyhow::Error> {
    const TOC_START: usize = 2;
    const TOC_EACH_SIZE: usize = 8; // sizeof(TocEntry) + 1
    let mut cache: BTreeMap<WoxHashedName, FilePayload> = BTreeMap::new();

    // Starts with a u16 about the number of files present in the archive
    let mut archive_size = TOC_START;

    root_directory
        .read_dir()?
        .try_for_each(|path| -> Result<(), anyhow::Error> {
            let mut file_reader = path.open_file()?;
            let mut payload = vec![];
            file_reader.read_to_end(&mut payload)?;

            // The hashing algorithm used only considers the file name. Even if the archive doesn't
            // support directories, all VfsPath are prefixed by a '/' that we need to remove.
            // Consider anything after the last slash to be the file name.
            let full_path_str = path.as_str();
            let path_str = &full_path_str[full_path_str.rfind('/').unwrap() + 1..];

            let toc = TocEntry {
                // If "extract_cc_file" doesn't know the file name, it will output the hash in
                // decimal as file name. So first try to parse the file name as a u16 and it
                // works, then assume it's the hash. Otherwise, it's a real file name and
                // compute the hash from it.
                id: path_str
                    .parse::<u16>()
                    .map(WoxHashedName::from)
                    .unwrap_or_else(|_| WoxHashedName::from(path_str.as_bytes())),
                offset: 0, // Will be filled later
                len: FileSize::try_from(payload.len())?,
            };

            // Make sure the file we add doesn't clash hash-wise with a file we already cached
            if let Vacant(slot) = cache.entry(toc.id) {
                let file_payload = FilePayload {
                    entry: toc,
                    payload,
                };

                // Make sure that the size we read from the directory entry matches with what we
                // read from the actual file...
                if file_payload.entry.len as usize == file_payload.payload.len() {
                    archive_size += TOC_EACH_SIZE + file_payload.payload.len();

                    slot.insert(file_payload);

                    Ok(())
                } else {
                    // Race condition between readdir and when we actually read the file?
                    Err(anyhow!(WoxError::Race))
                }
            } else {
                Err(anyhow!(WoxError::GenerateToc(
                    path.as_str().to_string(),
                    toc.id
                )))
            }
        })?;

    let archive_files = u16::try_from(cache.len())?;
    let mut encrypt = Encrypt::new(archive_writer, None);
    let mut payload_offset = TOC_START + TOC_EACH_SIZE * archive_files as usize;

    // Step 1: Write the number of files in this archive
    encrypt.write_u16::<LittleEndian>(archive_files)?;

    // Step 2: Get ready and write the table of contents
    encrypt.crypt = Some(Crypt::RotateAdd(ROTATE_ADD_INITIAL));
    cache
        .values_mut()
        .try_for_each(|file_payload| -> Result<(), anyhow::Error> {
            // Modify the value in the hash since we will use this information in step 3
            // XXX: Incorrect, offset is actually an u24...
            file_payload.entry.offset = u32::try_from(payload_offset)?;

            payload_offset += file_payload.payload.len();

            Ok(file_payload.entry.write(&mut encrypt)?)
        })?;

    // Step 3: Get ready and write all the contents of the archive
    encrypt.crypt = contents_crypt;
    cache
        .values()
        .try_for_each(|file_payload| encrypt.write_all(&file_payload.payload))?;

    // Step 4: Actually write the file on disk
    Ok(encrypt.flush()?)
}

fn full_read<R>(reader: &mut R) -> Result<Vec<u8>, IoError>
where
    R: Read,
{
    let mut buf = vec![];
    reader.read_to_end(&mut buf)?;
    Ok(buf)
}

fn compare_cc_files<A, B>(a: &mut A, b: &mut B) -> Result<(), anyhow::Error>
where
    A: Read,
    B: Read,
{
    type Toc = BTreeMap<WoxHashedName, TocEntry>;

    // We don't care about the crypto used for the file contents, use the least expensive one
    let contents_crypt = None;

    // Step 1: Load archives data from disk
    let contents = [
        Contents::new(full_read(a)?, WoxReverseDictionary::default()),
        Contents::new(full_read(b)?, WoxReverseDictionary::default()),
    ];

    // Step 2: If there's a difference in file count, then the archive are different
    let file_counts = contents
        .iter()
        .map(|content| content.file_count())
        .collect::<Result<SmallVec<[FileSize; 2]>, IoError>>()?;

    ensure!(
        file_counts[0] == file_counts[1],
        WoxError::DifferentFileCount(file_counts[0].into(), file_counts[1].into()),
    );

    let tocs = contents
        .iter()
        .map(|content| {
            content
                .toc_iter()?
                .map(|toc_result| toc_result.map(|toc| (toc.id, toc)))
                .collect::<Result<Toc, anyhow::Error>>()
        })
        .collect::<Result<SmallVec<[Toc; 2]>, anyhow::Error>>()?;

    // Step 3: If the TOC is different, then the archives are different.
    ensure!(
        tocs[0]
            .values()
            .zip(tocs[1].values())
            .all(|(a_entry, b_entry)| a_entry.id == b_entry.id && a_entry.len == b_entry.len),
        WoxError::TocDiffers
    );

    // Step 4: Last and more expensive check: make sure that the file contents is the same
    for (a_entry, b_entry) in tocs[0].values().zip(tocs[1].values()) {
        let a_payload = contents[0].fetch_payload(a_entry, contents_crypt.clone())?;
        let b_payload = contents[1].fetch_payload(b_entry, contents_crypt.clone())?;

        ensure!(a_payload == b_payload, WoxError::ContentDiffers);
    }

    Ok(())
}

fn open_file_or_stdin(path: &OsStr) -> Result<Box<dyn Read>, anyhow::Error> {
    if path == "-" {
        Ok(Box::new(stdin()))
    } else {
        Ok(Box::new(File::open(path)?))
    }
}

fn create_file_or_stdout(path: &OsStr) -> Result<Box<dyn Write>, anyhow::Error> {
    if path == "-" {
        Ok(Box::new(stdout()))
    } else {
        Ok(Box::new(File::create(path)?))
    }
}

trait Job<S>
where
    S: Write,
{
    fn name(&self) -> &'static str;
    fn subcommand(&self) -> App;
    fn execute(&self, args: &ArgMatches, stdout: &mut S) -> Result<(), anyhow::Error>;
}

fn new_subcommand<'a>(name: &'a str, about: &'a str) -> App<'a, 'a> {
    SubCommand::with_name(name)
        .about(about)
        .version(VERSION)
        .author(AUTHOR)
}

struct Extract {}

impl Extract {
    fn execute_with_dictionary<S, D>(
        &self,
        matches: &ArgMatches,
        stdout: &mut S,
        dictionary: D,
    ) -> Result<(), anyhow::Error>
    where
        S: Write,
        D: Read,
    {
        let optional_hashes = matches.values_of("file").map(|files_iter| {
            files_iter
                .map(|file| {
                    // If it's a number, it's already a hash and use it as is
                    file.parse::<WoxHashedName>()
                        .unwrap_or_else(|_| WoxHashedName::from(file.as_bytes()))
                })
                .collect::<Vec<_>>()
        });

        extract_cc_file(
            stdout,
            &mut open_file_or_stdin(matches.value_of_os("archive").unwrap())?,
            dictionary,
            &VfsPath::new(PhysicalFS::new(
                Path::new(
                    matches
                        .value_of_os("root")
                        .unwrap_or_else(|| OsStr::new(".")),
                )
                .to_path_buf(),
            )),
            if let Some(ref hashes) = optional_hashes {
                hashes
            } else {
                &[]
            },
            if matches.is_present("disable-contents-crypt") {
                None
            } else {
                Some(Crypt::Xor)
            },
        )
    }
}

impl<S> Job<S> for Extract
where
    S: Write,
{
    fn name(&self) -> &'static str {
        "extract"
    }

    fn subcommand(&self) -> App {
        new_subcommand(<Self as Job<S>>::name(self), "Extract an archive to a new directory")
            .arg(
                Arg::with_name("archive")
                    .long("archive")
                    .short("a")
                    .required(true)
                    .value_name("FILE")
                    .help("Archive file to extract, use '-' for stdin"),
            )
            .arg(
                Arg::with_name("dictionary")
                    .long("dictionary")
                    .value_name("FILE")
                    .help("Archived files dictionary file"),
            )
            .arg(
                Arg::with_name("root")
                    .long("root")
                    .short("C")
                    .value_name("DIRECTORY")
                    .help("Directory to extract to, if not provided, extract to current directory"),
            )
            .arg(
                Arg::with_name("file")
                    .long("file")
                    .short("f")
                    .multiple(true)
                    .value_name("ARCHIVED_FILE")
                    .help("File name from the archive to extract, written to stdout. If a number is provided, it's assumed to be a file hash."),
            )
            .arg(
                Arg::with_name("disable-contents-crypt")
                .long("disable-contents-crypt")
                .required(false)
                .takes_value(false)
                .help("Don't decrypt the file contents"),
            )
    }

    fn execute(&self, matches: &ArgMatches, stdout: &mut S) -> Result<(), anyhow::Error> {
        if let Some(dict) = matches.value_of_os("dictionary") {
            self.execute_with_dictionary(matches, stdout, &mut File::open(dict)?)
        } else {
            self.execute_with_dictionary(matches, stdout, &mut Cursor::new(&[]))
        }
    }
}

struct Create {}

impl<S> Job<S> for Create
where
    S: Write,
{
    fn name(&self) -> &'static str {
        "create"
    }

    fn subcommand(&self) -> App {
        new_subcommand(
            <Self as Job<S>>::name(self),
            "Create an archive from an existing directory",
        )
        .arg(
            Arg::with_name("archive")
                .long("archive")
                .short("a")
                .required(true)
                .value_name("FILE")
                .help("Archive file to create, use '-' for stdout"),
        )
        .arg(
            Arg::with_name("root")
                .long("root")
                .short("C")
                .required(true)
                .value_name("DIRECTORY")
                .help("Directory containing the files to archive"),
        )
        .arg(
            Arg::with_name("disable-contents-crypt")
                .long("disable-contents-crypt")
                .required(false)
                .takes_value(false)
                .help("Don't decrypt the file contents"),
        )
    }

    fn execute(&self, matches: &ArgMatches, _stdout: &mut S) -> Result<(), anyhow::Error> {
        create_cc_file(
            create_file_or_stdout(matches.value_of_os("archive").unwrap())?,
            &VfsPath::new(PhysicalFS::new(
                Path::new(matches.value_of_os("root").unwrap()).to_path_buf(),
            )),
            if matches.is_present("disable-contents-crypt") {
                None
            } else {
                Some(Crypt::Xor)
            },
        )
    }
}

struct Compare {}

impl<S> Job<S> for Compare
where
    S: Write,
{
    fn name(&self) -> &'static str {
        "compare"
    }

    fn subcommand(&self) -> App {
        new_subcommand(<Self as Job<S>>::name(self), "Compare two or more archives")
            .arg(Arg::with_name("archives").multiple(true))
    }

    fn execute(&self, matches: &ArgMatches, _stdout: &mut S) -> Result<(), anyhow::Error> {
        let mut iter = matches.values_of("archives").unwrap();
        let reference_path = iter.next().ok_or(WoxError::Requires2PlusFiles)?;
        let mut reference = File::open(Path::new(reference_path))?;

        let mut did_compare = false;
        for comparee_path in iter {
            //
            // When we compare more than 2 files, rewind the first file (we call it "reference"
            // here) and compare it with the third (or fourth, etc...) file. It's not the best
            // way to do this because:
            //
            // 1) It implies that "reference" implements Seek.
            // 2) We are going to extract "reference" more than once.
            //
            if did_compare {
                reference.seek(SeekFrom::Start(0))?;
            }

            compare_cc_files(&mut reference, &mut File::open(Path::new(comparee_path))?)
                .with_context(|| {
                    WoxError::ArchivesDiffer(reference_path.into(), comparee_path.into())
                })?;

            did_compare = true;
        }

        ensure!(did_compare, WoxError::Requires2PlusFiles);
        Ok(())
    }
}

struct Hash {}

impl<S> Job<S> for Hash
where
    S: Write,
{
    fn name(&self) -> &'static str {
        "hash"
    }

    fn subcommand(&self) -> App {
        new_subcommand(
            <Self as Job<S>>::name(self),
            "Compute the hash of a file name and output it on stdout",
        )
        .arg(Arg::with_name("name").required(true))
    }

    fn execute(&self, matches: &ArgMatches, stdout: &mut S) -> Result<(), anyhow::Error> {
        Ok(writeln!(
            stdout,
            "{}",
            WoxHashedName::from(matches.value_of("name").unwrap().as_bytes())
        )?)
    }
}

fn build_known_jobs<S>() -> [Box<dyn Job<S>>; 4]
where
    S: Write,
{
    [
        Box::new(Extract {}),
        Box::new(Create {}),
        Box::new(Compare {}),
        Box::new(Hash {}),
    ]
}

fn exec_cmdline<A, S>(args: &[A], stdout: &mut S) -> Result<(), anyhow::Error>
where
    A: AsRef<str> + AsRef<OsStr>,
    S: Write,
    String: From<A>,
{
    let jobs = build_known_jobs::<S>();

    let mut app = App::new("woxar")
        .version(VERSION)
        .author(AUTHOR)
        .about("Might and Magic: World of Xeen Archiver");
    for job in jobs.iter() {
        app = app.subcommand(job.subcommand());
    }
    let matches = app.get_matches_from_safe(&*args)?;

    if let Some((found, submatches)) = jobs.iter().find_map(|job| {
        matches
            .subcommand_matches(job.name())
            .map(|submatches| (job, submatches))
    }) {
        found.execute(submatches, stdout)?;
        stdout.flush()?;
        Ok(())
    } else {
        bail!(WoxError::NoSubcommand)
    }
}

fn exec_cmdline_manage_errors<'a, A, S, E>(args: &[A], stdout: &mut S, stderr: &mut E) -> bool
where
    A: AsRef<str> + Display + From<&'a str> + AsRef<OsStr>,
    S: Write,
    E: Write,
    String: From<A>,
{
    if let Err(err) = exec_cmdline(args, stdout) {
        match err.downcast_ref::<ClapError>() {
            Some(ClapError { kind, message, .. })
                if matches!(*kind, HelpDisplayed | VersionDisplayed) =>
            {
                writeln!(stdout, "{}", message).unwrap();
                true
            }
            _ => {
                writeln!(
                    stderr,
                    "{}: ERROR: {}",
                    args.get(0).unwrap_or(&"<unknown>".into()),
                    err
                )
                .unwrap();
                false
            }
        }
    } else {
        true
    }
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let mut stdout = stdout();
    let mut stderr = stderr();

    exit(
        if exec_cmdline_manage_errors(&args, &mut stdout, &mut stderr) {
            0
        } else {
            1
        },
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::empty;
    use vfs::MemoryFS;

    #[test]
    fn rotate_add_crypt() {
        type Buf = [u8; 8];
        const PLAINTEXT: Buf = [0x01, 0x23, 0x45, 0x67, 0x89, 0xab, 0xcd, 0xef];
        const EXPECTED_CRYPT: Buf = [176, 159, 143, 126, 110, 93, 77, 60];

        let mut state = Some(Crypt::RotateAdd(ROTATE_ADD_INITIAL));
        let crypted = PLAINTEXT
            .iter()
            .map(|byte| crypt(&mut state, Direction::Read, *byte))
            .collect::<SmallVec<Buf>>();

        assert_eq!(&crypted[..], EXPECTED_CRYPT);

        let mut state = Some(Crypt::RotateAdd(ROTATE_ADD_INITIAL));
        let decrypted = crypted
            .iter()
            .map(|byte| crypt(&mut state, Direction::Write, *byte))
            .collect::<SmallVec<Buf>>();

        assert_eq!(PLAINTEXT, &decrypted[..]);
    }

    fn cmdline_expect(subcmd: Option<&str>, arg: &str, on_stdout: bool) {
        let mut stdout = Vec::<u8>::new();
        let mut stderr = Vec::<u8>::new();
        let mut cmdline = SmallVec::<[&str; 3]>::new();

        cmdline.push("unit-test");

        if let Some(subcmd_str) = subcmd {
            cmdline.push(subcmd_str);
        }

        cmdline.push(arg);

        assert!(exec_cmdline_manage_errors(
            &cmdline,
            &mut stdout,
            &mut stderr
        ));

        if on_stdout {
            assert!(!stdout.is_empty());
        }

        assert!(stderr.is_empty());
    }

    #[test]
    fn cmdline_help_n_version() {
        let jobs = build_known_jobs::<Vec<u8>>();

        // Note: clap behavior is different for --help and --version. The former will write the
        // message in the generated Error while the latter will print directly to stdout, bypassing
        // our output capture strategy. No idea if this behavior is intended by clap or not... but
        // it's annoying for unit testing purposes.
        for arg in [
            ("--help", true),
            ("-h", true),
            ("--version", false),
            ("-V", false),
        ]
        .iter()
        {
            cmdline_expect(None, arg.0, arg.1);

            for job in &jobs {
                cmdline_expect(Some(job.name()), arg.0, arg.1);
            }
        }
    }

    #[test]
    fn compare_archives() {
        assert!(compare_cc_files(&mut empty(), &mut empty()).is_err());

        const ARCHIVE_WITH_NO_FILES: [u8; 2] = [0, 0];
        compare_cc_files(
            &mut Cursor::new(&ARCHIVE_WITH_NO_FILES),
            &mut Cursor::new(&ARCHIVE_WITH_NO_FILES),
        )
        .unwrap();
    }

    fn fs_write(root: &VfsPath, name: &str, contents: &[u8]) {
        let path = root.join(name).unwrap();
        let mut file = path.create_file().unwrap();
        file.write_all(contents).unwrap();
    }

    fn build_memory_fs_with_b_name(b_name: &str) -> VfsPath {
        let root = VfsPath::new(MemoryFS::new());

        fs_write(&root, "A.TXT", b"A");
        fs_write(&root, b_name, b"BB");
        fs_write(&root, "C.TXT", b"CCC");

        root
    }

    fn build_memory_fs() -> VfsPath {
        build_memory_fs_with_b_name("B.TXT")
    }

    // List of files in the file system created by build_memory_fs().
    fn archive_dictionary() -> Cursor<&'static [u8]> {
        Cursor::new(b"A.TXT\nB.TXT\nC.TXT\n")
    }

    // An archived version of the file system created by build_memory_fs().
    const ARCHIVE_CONTENTS: &[u8] = 
            &[
                3, 0, 130, 132, 40, 199, 46, 148, 186, 224, 184, 182, 90, 249, 32, 198, 172, 210,
                174, 168, 204, 235, 18, 57, 158, 196, 116, 119, 119, 118, 118, 118
            ];

    fn fs_as_tree(root: &VfsPath) -> BTreeMap<String, Vec<u8>> {
        root.read_dir().unwrap().map(|path| {
            let mut reader = path.open_file().unwrap();
            let mut contents = vec![];
            reader.read_to_end(&mut contents).unwrap();

            (path.as_str().into(), contents)
        }).collect()
    }

    fn compare_fs(a: &VfsPath, b: &VfsPath) -> bool {
        fs_as_tree(a) == fs_as_tree(b)
    }

    #[test]
    fn create_archive() {
        let root = build_memory_fs();

        let mut archive = vec![];
        create_cc_file(&mut archive, &root, Some(Crypt::Xor)).unwrap();
        assert_eq!(
            ARCHIVE_CONTENTS,
            archive.as_slice()
        );
    }

    #[test]
    fn extract_whole_archive() {
        let root = VfsPath::new(MemoryFS::new());

        let mut stdout = vec![];
        extract_cc_file(&mut stdout, &mut Cursor::new(ARCHIVE_CONTENTS), archive_dictionary(), &root, &[], Some(Crypt::Xor)).unwrap();

        // When no hashes are provided, the contents of the archive will be written to the provided
        // file system.
        assert!(stdout.is_empty());
        assert!(compare_fs(&root, &build_memory_fs()));
    }

    #[test]
    fn extract_with_partial_dictionary() {
        let root = VfsPath::new(MemoryFS::new());
        let partial_dictionary = Cursor::new(b"A.TXT\nC.TXT\n");
        let b_hashed_name = format!("{}", WoxHashedName::from("B.TXT".as_bytes()).raw());

        let mut stdout = vec![];
        extract_cc_file(&mut stdout, &mut Cursor::new(ARCHIVE_CONTENTS), partial_dictionary, &root, &[], Some(Crypt::Xor)).unwrap();

        // In this test, we don't have "B.TXT" in the dictionary. As a result, that file will have
        // the hashed value as name.
        assert!(stdout.is_empty());
        assert!(compare_fs(&root, &build_memory_fs_with_b_name(&b_hashed_name)));
    }

    #[test]
    fn extract_selected_hash_archive() {
        let root = VfsPath::new(MemoryFS::new());
        let hashes = [
            WoxHashedName::from("A.TXT".as_bytes()),
            WoxHashedName::from("C.TXT".as_bytes()),
            WoxHashedName::from("B.TXT".as_bytes()),
        ];

        let mut stdout = vec![];
        extract_cc_file(&mut stdout, &mut Cursor::new(ARCHIVE_CONTENTS), archive_dictionary(), &root, &hashes, Some(Crypt::Xor)).unwrap();

        // With provided hashes, the selected hashes of the archive will be written to the provided
        // "stdout" stream. Ordering of the hashes is expected to be reflected in the output.
        assert_eq!(&stdout, b"ACCCBB");
        assert_eq!(root.read_dir().unwrap().count(), 0);
    }
}
