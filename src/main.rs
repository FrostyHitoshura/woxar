//! Might and Magic: World of Xeen Archiver. Implemented based on documentation available at:
//!
//! https://xeen.fandom.com/wiki/CC_File_Format

#![deny(warnings)]

extern crate bit_vec;

use bit_vec::BitVec;
use clap::{
    App, Arg, ArgMatches, Error as ClapError,
    ErrorKind::{HelpDisplayed, VersionDisplayed},
    SubCommand,
};
use smallvec::SmallVec;
use std::{
    collections::{btree_map::Entry::Vacant, BTreeMap, HashMap},
    convert::TryFrom,
    env, error, fmt,
    fmt::{Display, Formatter},
    fs,
    fs::create_dir_all,
    io::{stderr, stdout, Error as IoError, Write},
    num::{ParseIntError, TryFromIntError},
    path::Path,
    process::exit,
    str,
    str::Utf8Error,
    u16,
};

const VERSION: &'static str = env!("CARGO_PKG_VERSION");
const AUTHOR: &'static str = env!("CARGO_PKG_AUTHORS");

fn parse_u16_hex(input: &str) -> Result<u16, ParseIntError> {
    let starting_offset = if input.starts_with("0x") || input.starts_with("0X") {
        2
    } else {
        0
    };

    u16::from_str_radix(&input[starting_offset..], 16)
}

#[derive(Debug)]
enum ErrorCode {
    EndOfFile(usize, usize),
    FileName,
    ReadToc,
    GenerateToc(String, FileHash),
    Race,
    Compare(String, String, String),
}

#[derive(Debug)]
enum WoxError {
    Error(ErrorCode),
    Utf8Error(Utf8Error),
    ParseIntError(ParseIntError),
    IoError(IoError),
    TryFromIntError(TryFromIntError),
    ClapError(ClapError),
    Generic(String),
}

impl From<ErrorCode> for WoxError {
    fn from(error: ErrorCode) -> Self {
        WoxError::Error(error)
    }
}

impl From<Utf8Error> for WoxError {
    fn from(error: Utf8Error) -> Self {
        WoxError::Utf8Error(error)
    }
}

impl From<ParseIntError> for WoxError {
    fn from(error: ParseIntError) -> Self {
        WoxError::ParseIntError(error)
    }
}

impl From<IoError> for WoxError {
    fn from(error: IoError) -> Self {
        WoxError::IoError(error)
    }
}

impl From<TryFromIntError> for WoxError {
    fn from(error: TryFromIntError) -> Self {
        WoxError::TryFromIntError(error)
    }
}

impl From<ClapError> for WoxError {
    fn from(error: ClapError) -> Self {
        WoxError::ClapError(error)
    }
}

const ROTATE_ADD_INITIAL: u8 = 0xac;

enum Crypt {
    None,          // Used for the initial 2 bytes of the file
    RotateAdd(u8), // Used for the table of contents
    Xor,           // Used for the file contents
}

type FileCount = u16;
type FileSize = u16;
type FileHash = u16;
type ListHash = HashMap<FileHash, ListEntry>;

struct ListEntry {
    name: String,
    expected_hash: Option<FileHash>,
    expected_size: Option<FileSize>,
}

struct Contents {
    data: Vec<u8>,
    list: ListHash,
}

#[derive(PartialEq, Debug)]
enum Direction {
    Read,
    Write,
}

struct ReadCursor<'a> {
    contents: &'a Contents,
    offset: usize,
    crypt: Crypt,
}

struct WriteCursor<'a> {
    contents: &'a mut Contents,
    crypt: Crypt,
}

struct TocEntry {
    id: u16,
    offset: u32, // XXX: Actually an u24...
    len: FileSize,
    // In the file... padding: u8 which is expected to be always 0
}

struct TocIter<'a> {
    cursor: ReadCursor<'a>,
    idx: usize,
    total: usize,

    // A bit array where we keep track of all seen hashes.
    verify: BitVec,
}

struct PayloadIter<'a> {
    toc: TocIter<'a>,
}

impl ListEntry {
    fn new(name: String) -> ListEntry {
        ListEntry {
            name: name,
            expected_hash: None,
            expected_size: None,
        }
    }
}

impl Contents {
    fn new(data: Vec<u8>) -> Contents {
        Contents {
            data: data,
            list: HashMap::new(),
        }
    }

    fn parse_list(&mut self, data: Vec<u8>) -> Result<(), WoxError> {
        data.split(|byte| *byte == b'\n')
            .filter(|line| line.len() >= 1)
            .try_for_each(|line: &[u8]| -> Result<(), WoxError> {
                let mut csv = line.split(|byte| *byte == b',');

                if let Some(name) = csv.next() {
                    if name.len() < 1 {
                        return Err(WoxError::Error(ErrorCode::FileName));
                    }

                    let utf8_name = str::from_utf8(name)?;
                    let mut entry = ListEntry::new(utf8_name.to_string());

                    if let Some(hash) = csv.next() {
                        entry.expected_hash = Some(parse_u16_hex(str::from_utf8(hash)?)?);
                    }

                    if let Some(size) = csv.next() {
                        entry.expected_size = Some(str::from_utf8(size)?.parse()?);
                    }

                    self.list.insert(compute_hash(name), entry);
                };

                Ok(())
            })?;

        Ok(())
    }

    fn find_entry(&self, hash: FileHash) -> Option<&ListEntry> {
        self.list.get(&hash)
    }

    fn entry_name(&self, entry: &TocEntry) -> String {
        match self.find_entry(entry.id) {
            Some(entry) => format!("{}", entry.name),
            None => format!("{}", entry.id),
        }
    }

    fn read_cursor_at(&self, offset: usize, crypt: Crypt) -> ReadCursor {
        ReadCursor {
            contents: self,
            offset: offset,
            crypt: crypt,
        }
    }

    fn read_cursor(&self) -> ReadCursor {
        self.read_cursor_at(0, Crypt::None)
    }

    fn write_cursor(&mut self) -> WriteCursor {
        WriteCursor {
            contents: self,
            crypt: Crypt::None,
        }
    }

    fn file_count(&self) -> Result<FileCount, WoxError> {
        Ok(self.read_cursor().read_u16()?)
    }

    fn toc_iter(&self) -> Result<TocIter, WoxError> {
        let mut cursor = self.read_cursor();

        // XXX: Remplace with self.file_count()
        let total = cursor.read_u16()? as usize;

        cursor.crypt = Crypt::RotateAdd(ROTATE_ADD_INITIAL);

        Ok(TocIter {
            cursor: cursor,
            idx: 0,
            total: total,
            verify: BitVec::from_elem(FileHash::max_value() as usize, false),
        })
    }

    fn payload_iter(&self) -> Result<PayloadIter, WoxError> {
        Ok(PayloadIter {
            toc: self.toc_iter()?,
        })
    }

    fn fetch_payload(&self, entry: &TocEntry) -> Result<Vec<u8>, WoxError> {
        self.read_cursor_at(entry.offset as usize, Crypt::Xor)
            .read(entry.len as usize)
    }
}

fn crypt(mut crypt: &mut Crypt, direction: Direction, byte: u8) -> u8 {
    const ROTATE: u32 = 6;
    const ADD: u8 = 0x67;

    match (&direction, &mut crypt) {
        (_, Crypt::None) => byte,
        (Direction::Read, Crypt::RotateAdd(state)) => {
            let decrypted = u8::wrapping_add(byte.rotate_right(ROTATE), *state);
            *crypt = Crypt::RotateAdd(u8::wrapping_add(*state, ADD));

            decrypted
        }
        (Direction::Write, Crypt::RotateAdd(state)) => {
            let crypted = u8::wrapping_sub(byte, *state).rotate_left(ROTATE);
            *crypt = Crypt::RotateAdd(u8::wrapping_add(*state, ADD));

            crypted
        }
        (_, Crypt::Xor) => byte ^ 0x35,
    }
}

impl<'a> ReadCursor<'a> {
    fn contents(&self) -> &Contents {
        self.contents
    }

    fn read_u8(&mut self) -> Result<u8, WoxError> {
        let len = self.contents.data.len();
        if len <= self.offset {
            Err(WoxError::Error(ErrorCode::EndOfFile(len, self.offset)))
        } else {
            let byte = self.contents.data[self.offset];
            self.offset = self.offset + 1;

            Ok(crypt(&mut self.crypt, Direction::Read, byte))
        }
    }

    fn read_u16(&mut self) -> Result<u16, WoxError> {
        Ok(u16::from_le_bytes([self.read_u8()?, self.read_u8()?]))
    }

    fn read_u24(&mut self) -> Result<u32, WoxError> {
        Ok(u32::from_le_bytes([
            self.read_u8()?,
            self.read_u8()?,
            self.read_u8()?,
            0,
        ]))
    }

    fn read(&mut self, size: usize) -> Result<Vec<u8>, WoxError> {
        let len = self.contents.data.len();
        let next_offset = self.offset + size;
        if next_offset > len {
            return Err(WoxError::Error(ErrorCode::EndOfFile(len, next_offset - 1)));
        }

        let decrypted = self.contents.data[self.offset..next_offset]
            .iter()
            .map(|i| crypt(&mut self.crypt, Direction::Read, *i))
            .collect();

        self.offset = next_offset;

        Ok(decrypted)
    }
}

impl<'a> WriteCursor<'a> {
    fn write_u8(&mut self, byte: u8) -> Result<(), WoxError> {
        let cap = self.contents.data.capacity();
        let len = self.contents.data.len();
        if len >= cap {
            Err(WoxError::Error(ErrorCode::EndOfFile(cap, len)))
        } else {
            self.contents
                .data
                .push(crypt(&mut self.crypt, Direction::Write, byte));
            Ok(())
        }
    }

    fn write_u16(&mut self, byte: u16) -> Result<(), WoxError> {
        // little endian
        self.write_u8(byte as u8)?;
        self.write_u8((byte >> 8) as u8)
    }

    fn write_u24(&mut self, byte: u32) -> Result<(), WoxError> {
        // little endian
        self.write_u8(byte as u8)?;
        self.write_u8((byte >> 8) as u8)?;
        self.write_u8((byte >> 16) as u8)
    }

    fn write(&mut self, data: &Vec<u8>) -> Result<(), WoxError> {
        let cap = self.contents.data.capacity();
        let next_len = self.contents.data.len() + data.len();
        if next_len > cap {
            return Err(WoxError::Error(ErrorCode::EndOfFile(cap, next_len - 1)));
        }

        let crypted = data
            .iter()
            .map(|o| crypt(&mut self.crypt, Direction::Write, *o))
            .collect::<Vec<u8>>();

        self.contents.data.extend_from_slice(&crypted);

        Ok(())
    }
}

impl TocEntry {
    fn new(cursor: &mut ReadCursor) -> Result<TocEntry, WoxError> {
        let entry = TocEntry {
            id: cursor.read_u16()?,
            offset: cursor.read_u24()?,
            len: cursor.read_u16()?,
        };

        // Ensure that the padding byte is set to 0
        if cursor.read_u8()? != 0 {
            Err(WoxError::Error(ErrorCode::ReadToc))
        } else {
            Ok(entry)
        }
    }

    fn write(&self, cursor: &mut WriteCursor) -> Result<(), WoxError> {
        cursor.write_u16(self.id)?;
        cursor.write_u24(self.offset)?;
        cursor.write_u16(self.len)?;
        cursor.write_u8(0_u8)
    }
}

impl<'a> TocIter<'a> {
    fn contents(&self) -> &Contents {
        self.cursor.contents()
    }
}

impl<'a> Iterator for TocIter<'a> {
    type Item = Result<TocEntry, WoxError>;

    fn next(&mut self) -> Option<Self::Item> {
        self.idx += 1;

        if self.idx <= self.total {
            match TocEntry::new(&mut self.cursor) {
                Err(err) => Some(Err(err)),
                Ok(entry) => {
                    let bit = entry.id as usize;

                    if self.verify[bit] {
                        Some(Err(WoxError::Error(ErrorCode::ReadToc)))
                    } else {
                        self.verify.set(bit, true);
                        Some(Ok(entry))
                    }
                }
            }
        } else {
            None
        }
    }
}

impl<'a> Iterator for PayloadIter<'a> {
    type Item = Result<(TocEntry, Vec<u8>), WoxError>;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(entry_result) = self.toc.next() {
            match entry_result {
                Ok(entry) => match self.toc.contents().fetch_payload(&entry) {
                    Ok(decrypted) => Some(Ok((entry, decrypted))),
                    Err(err) => Some(Err(err)),
                },
                Err(err) => Some(Err(err)),
            }
        } else {
            None
        }
    }
}

impl Display for WoxError {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            WoxError::Error(ours) => {
                write!(f, "{}", match ours {
                    ErrorCode::EndOfFile(len, offset) => format!("Premature end of file encountered, attempted to access offset {} while size is {}", offset, len),
                    ErrorCode::FileName => "Invalid file name format".to_string(),
                    ErrorCode::ReadToc => "Found invalid data in the table of contents".to_string(),
                    ErrorCode::GenerateToc(file, hash) => format!("Can't encode file '{}' as hash {:#06x} is already in use", file, hash),
                    ErrorCode::Race => "Hit a race condition".to_string(),
                    ErrorCode::Compare(a, b, reason) => format!("Archives '{}' and '{}' differ: {}", a, b, reason),
                })
            }
            // XXX: Transform into generic match?
            WoxError::Utf8Error(err) => write!(f, "{}", err),
            WoxError::ParseIntError(err) => write!(f, "{}", err),
            WoxError::IoError(err) => write!(f, "{}", err),
            WoxError::TryFromIntError(err) => write!(f, "{}", err),
            WoxError::ClapError(err) => write!(f, "{}", err),
            WoxError::Generic(err) => write!(f, "{}", err),
        }
    }
}

impl error::Error for WoxError {
    fn description(&self) -> &str {
        "World of Xeen Archiver error"
    }
}

fn compute_hash(name: &[u8]) -> FileHash {
    if name.len() == 0 {
        // Follows ScummVM's BaseCCArchive::convertNameToId
        0xffff
    } else {
        name.iter().skip(1).fold(name[0] as FileHash, |acc, byte| {
            FileHash::wrapping_add(FileHash::rotate_right(acc, 7), *byte as FileHash)
        })
    }
}

fn extract_cc_file(
    archive_path: &Path,
    list_file: Option<&Path>,
    root_directory: &Path,
) -> Result<(), WoxError> {
    let mut contents = Contents::new(fs::read(archive_path)?);

    if let Some(lf) = list_file {
        contents.parse_list(fs::read(lf)?)?
    };

    create_dir_all(root_directory)?;

    contents.payload_iter()?.try_for_each(
        |payload_result: Result<(TocEntry, Vec<u8>), WoxError>| -> Result<(), WoxError> {
            let payload = payload_result?;
            fs::write(
                root_directory.join(contents.entry_name(&payload.0)),
                payload.1,
            )?;
            Ok(())
        },
    )
}

struct FilePayload {
    entry: TocEntry,
    payload: Vec<u8>,
}

fn create_cc_file(archive_path: &Path, root_directory: &Path) -> Result<(), WoxError> {
    const TOC_START: usize = 2;
    const TOC_EACH_SIZE: usize = 8; // sizeof(TocEntry) + 1
    let mut cache: BTreeMap<FileHash, FilePayload> = BTreeMap::new();

    // Starts with a u16 about the number of files present in the archive
    let mut archive_size = TOC_START;

    root_directory
        .read_dir()?
        .try_for_each(|dir_entry_result| -> Result<(), WoxError> {
            let dir_entry = dir_entry_result?;

            if let Some(path) = dir_entry.file_name().to_str() {
                let toc = TocEntry {
                    // If "extract_cc_file" doesn't know the file name, it will output the hash in
                    // decimal as file name. So first try to parse the file name as a u16 and it
                    // works, then assume it's the hash. Otherwise, it's a real file name and
                    // compute the hash from it.
                    id: u16::from_str_radix(&path, 10).unwrap_or(compute_hash(path.as_bytes())),
                    offset: 0, // Will be filled later
                    len: FileSize::try_from(dir_entry.metadata()?.len())?,
                };

                // Make sure the file we add doesn't clash hash-wise with a file we already cached
                if let Vacant(slot) = cache.entry(toc.id) {
                    let file_payload = FilePayload {
                        entry: toc,
                        payload: fs::read(dir_entry.path())?,
                    };

                    // Make sure that the size we read from the directory entry matches with what we
                    // read from the actual file...
                    if file_payload.entry.len as usize == file_payload.payload.len() {
                        archive_size += TOC_EACH_SIZE + file_payload.payload.len();

                        slot.insert(file_payload);

                        Ok(())
                    } else {
                        // Race condition between readdir and when we actually read the file?
                        Err(WoxError::Error(ErrorCode::Race))
                    }
                } else {
                    Err(WoxError::Error(ErrorCode::GenerateToc(
                        path.to_string(),
                        toc.id,
                    )))
                }
            } else {
                Err(WoxError::Error(ErrorCode::FileName))
            }
        })?;

    let archive_files = u16::try_from(cache.len())?;
    let mut contents = Contents::new(Vec::<u8>::with_capacity(archive_size));
    let mut cursor = contents.write_cursor();
    let mut payload_offset = TOC_START + TOC_EACH_SIZE * archive_files as usize;

    // Step 1: Write the number of files in this archive
    cursor.write_u16(archive_files)?;

    // Step 2: Get ready and write the table of contents
    cursor.crypt = Crypt::RotateAdd(ROTATE_ADD_INITIAL);
    cache.values_mut().try_for_each(|file_payload| {
        // Modify the value in the hash since we will use this information in step 3
        // XXX: Incorrect, offset is actually an u24...
        file_payload.entry.offset = u32::try_from(payload_offset)?;

        payload_offset += file_payload.payload.len();

        file_payload.entry.write(&mut cursor)
    })?;

    // Step 3: Get ready and write all the contents of the archive
    cursor.crypt = Crypt::Xor;
    cache
        .values()
        .try_for_each(|file_payload| cursor.write(&file_payload.payload))?;

    // Step 4: Actually write the file on disk
    Ok(fs::write(archive_path, contents.data)?)
}

fn compare_cc_files(paths: [&Path; 2]) -> Result<(), WoxError> {
    type Toc = BTreeMap<FileHash, TocEntry>;

    // Step 1: Load archives data from disk
    let contents = paths
        .iter()
        .map(|path| Ok(Contents::new(fs::read(path)?)))
        .collect::<Result<SmallVec<[Contents; 2]>, WoxError>>()?;

    // Step 2: If there's a difference in file count, then the archive are different
    let file_counts = contents
        .iter()
        .map(|content| Ok(content.file_count()?))
        .collect::<Result<SmallVec<[FileSize; 2]>, WoxError>>()?;

    if file_counts[0] != file_counts[1] {
        return Err(WoxError::Error(ErrorCode::Compare(
            paths[0].to_str().unwrap().to_string(),
            paths[1].to_str().unwrap().to_string(),
            format!(
                "The former has {} file(s) while the latter has {} file(s)",
                file_counts[0], file_counts[1]
            ),
        )));
    }

    let tocs = contents
        .iter()
        .map(|content| {
            content
                .toc_iter()?
                .map(|toc_result| match toc_result {
                    Ok(toc) => Ok((toc.id, toc)),
                    Err(err) => Err(err),
                })
                .collect::<Result<Toc, WoxError>>()
        })
        .collect::<Result<SmallVec<[Toc; 2]>, WoxError>>()?;

    // Step 3: If the TOC is different, then the archives are different.
    if !tocs[0]
        .values()
        .zip(tocs[1].values())
        .all(|(a_entry, b_entry)| a_entry.id == b_entry.id && a_entry.len == b_entry.len)
    {
        return Err(WoxError::Error(ErrorCode::Compare(
            paths[0].to_str().unwrap().to_string(),
            paths[1].to_str().unwrap().to_string(),
            "The table of contents differ".into(),
        )));
    }

    // Step 4: Last and more expensive check: make sure that the file contents is the same
    if tocs[0]
        .values()
        .zip(tocs[1].values())
        .all(|(a_entry, b_entry)| {
            if let (Ok(a_payload), Ok(b_payload)) = (
                contents[0].fetch_payload(&a_entry),
                contents[1].fetch_payload(&b_entry),
            ) {
                a_payload == b_payload
            } else {
                // XXX: We lost the error here...
                false
            }
        })
    {
        Ok(())
    } else {
        Err(WoxError::Error(ErrorCode::Compare(
            paths[0].to_str().unwrap().to_string(),
            paths[1].to_str().unwrap().to_string(),
            "One or mode file content differs".into(),
        )))
    }
}

trait Job {
    fn name(&self) -> &'static str;
    fn subcommand(&self) -> App;
    fn execute(&self, args: &ArgMatches, stdout: &mut dyn Write) -> Result<(), WoxError>;
}

fn new_subcommand<'a>(name: &'a str, about: &'a str) -> App<'a, 'a> {
    SubCommand::with_name(name)
        .about(about)
        .version(VERSION)
        .author(AUTHOR)
}

struct Extract {}

impl Job for Extract {
    fn name(&self) -> &'static str {
        "extract"
    }

    fn subcommand(&self) -> App {
        new_subcommand(self.name(), "Extract an archive to a new directory")
            .arg(
                Arg::with_name("archive")
                    .long("archive")
                    .short("a")
                    .required(true)
                    .value_name("FILE")
                    .help("Archive file to extract"),
            )
            .arg(
                Arg::with_name("fl")
                    .long("fl")
                    .value_name("FILE")
                    .help("Archived files list manifest file"),
            )
            .arg(
                Arg::with_name("root")
                    .long("root")
                    .short("C")
                    .required(true)
                    .value_name("DIRECTORY")
                    .help("Directory to extract to"),
            )
    }

    fn execute(&self, matches: &ArgMatches, _stdout: &mut dyn Write) -> Result<(), WoxError> {
        extract_cc_file(
            Path::new(matches.value_of_os("archive").unwrap()),
            matches.value_of_os("fl").and_then(|fl| Some(Path::new(fl))),
            Path::new(matches.value_of_os("root").unwrap()),
        )
    }
}

struct Create {}

impl Job for Create {
    fn name(&self) -> &'static str {
        "create"
    }

    fn subcommand(&self) -> App {
        new_subcommand(self.name(), "Create an archive from an existing directory")
            .arg(
                Arg::with_name("archive")
                    .long("archive")
                    .short("a")
                    .required(true)
                    .value_name("FILE")
                    .help("Archive file to create"),
            )
            .arg(
                Arg::with_name("root")
                    .long("root")
                    .short("C")
                    .required(true)
                    .value_name("DIRECTORY")
                    .help("Directory containing the files to archive"),
            )
    }

    fn execute(&self, matches: &ArgMatches, _stdout: &mut dyn Write) -> Result<(), WoxError> {
        create_cc_file(
            Path::new(matches.value_of_os("archive").unwrap()),
            Path::new(matches.value_of_os("root").unwrap()),
        )
    }
}

struct Compare {}

impl Job for Compare {
    fn name(&self) -> &'static str {
        "compare"
    }

    fn subcommand(&self) -> App {
        new_subcommand(self.name(), "Compare two or more archives")
            .arg(Arg::with_name("archives").multiple(true))
    }

    fn execute(&self, matches: &ArgMatches, _stdout: &mut dyn Write) -> Result<(), WoxError> {
        let mut iter = matches.values_of("archives").unwrap();
        let first = iter.next();
        let second = iter.next();
        let third = iter.next();

        if first.is_none() || second.is_none() {
            Err(WoxError::Generic(
                "Requires 2 or more archives to compare".into(),
            ))
        } else if third.is_some() {
            unimplemented!()
        } else {
            compare_cc_files([Path::new(first.unwrap()), Path::new(second.unwrap())])
        }
    }
}

struct Hash {}

impl Job for Hash {
    fn name(&self) -> &'static str {
        "hash"
    }

    fn subcommand(&self) -> App {
        new_subcommand(
            self.name(),
            "Compute the hash from a file and output on stdout",
        )
        .arg(Arg::with_name("file").required(true))
    }

    fn execute(&self, matches: &ArgMatches, stdout: &mut dyn Write) -> Result<(), WoxError> {
        Ok(writeln!(
            stdout,
            "{}",
            compute_hash(&fs::read(matches.value_of_os("file").unwrap())?)
        )?)
    }
}

fn build_known_jobs() -> [Box<dyn Job>; 4] {
    [
        Box::new(Extract {}),
        Box::new(Create {}),
        Box::new(Compare {}),
        Box::new(Hash {}),
    ]
}

fn exec_cmdline(args: &[String], stdout: &mut dyn Write) -> Result<(), WoxError> {
    let jobs = build_known_jobs();

    let mut app = App::new("woxar")
        .version(VERSION)
        .author(AUTHOR)
        .about("Might and Magic: World of Xeen Archiver");
    for job in jobs.iter() {
        app = app.subcommand(job.subcommand());
    }
    let matches = app.get_matches_from_safe(args)?;

    if let Some((found, submatches)) = jobs.iter().find_map(|job| {
        if let Some(submatches) = matches.subcommand_matches(job.name()) {
            Some((job, submatches))
        } else {
            None
        }
    }) {
        found.execute(&submatches, stdout)
    } else {
        return Err(WoxError::Generic(
            "Fatal internal error: Failed to find a subcommand".into(),
        ));
    }
}

fn exec_cmdline_manage_errors(
    args: &[String],
    stdout: &mut dyn Write,
    stderr: &mut dyn Write,
) -> bool {
    if let Err(err) = exec_cmdline(args, stdout) {
        match err {
            WoxError::ClapError(clap_err)
                if clap_err.kind == HelpDisplayed || clap_err.kind == VersionDisplayed =>
            {
                writeln!(stdout, "{}", clap_err.message).unwrap();
                true
            }
            err => {
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

    #[test]
    fn rotate_add_crypt() {
        type Buf = [u8; 8];
        const PLAINTEXT: Buf = [0x01, 0x23, 0x45, 0x67, 0x89, 0xab, 0xcd, 0xef];
        const EXPECTED_CRYPT: Buf = [176, 159, 143, 126, 110, 93, 77, 60];

        let mut state = Crypt::RotateAdd(ROTATE_ADD_INITIAL);
        let crypted = PLAINTEXT
            .iter()
            .map(|byte| crypt(&mut state, Direction::Read, *byte))
            .collect::<SmallVec<Buf>>();

        assert_eq!(&crypted[..], EXPECTED_CRYPT);

        let mut state = Crypt::RotateAdd(ROTATE_ADD_INITIAL);
        let decrypted = crypted
            .iter()
            .map(|byte| crypt(&mut state, Direction::Write, *byte))
            .collect::<SmallVec<Buf>>();

        assert_eq!(PLAINTEXT, &decrypted[..]);
    }

    #[test]
    fn hash() {
        // Not expected to happen for real, simply make sure we don't crash!
        compute_hash(&[0; 0]);

        const SIXTY_FOUR: [u8; 1] = [64];
        assert_eq!(compute_hash(&SIXTY_FOUR), 64);

        const TWO_BYTES: [u8; 2] = [12, 34];
        assert_eq!(compute_hash(&TWO_BYTES), 6178);
    }

    fn cmdline_expect(subcmd: Option<&str>, arg: &str, on_stdout: bool) {
        let mut stdout = Vec::<u8>::new();
        let mut stderr = Vec::<u8>::new();
        let mut cmdline = SmallVec::<[String; 3]>::new();

        cmdline.push("unit-test".into());

        if let Some(subcmd_str) = subcmd {
            cmdline.push(subcmd_str.into());
        }

        cmdline.push(arg.into());

        assert_eq!(
            exec_cmdline_manage_errors(&cmdline, &mut stdout, &mut stderr),
            true
        );

        if on_stdout {
            assert!(stdout.len() > 0);
        }

        assert!(stderr.is_empty());
    }

    #[test]
    fn cmdline_help_n_version() {
        let jobs = build_known_jobs();

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
}
