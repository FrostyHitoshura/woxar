use bitvec::{prelude::*, vec::BitVec};
use derivative::Derivative;
use thiserror::Error;

use std::{
    cmp::Eq,
    collections::HashMap,
    convert::{TryFrom, TryInto},
    fmt,
    fmt::{Display, Formatter, LowerHex},
    hash::Hash,
    io,
    io::{BufRead, BufReader, Read, Write},
    num::ParseIntError,
    str::{from_utf8_unchecked, FromStr},
};

pub struct NameIter<'a> {
    generator: &'a AsciiNameSet,
    count: u8,
    done: bool,
    max_name: usize,
}

trait NameSet {
    type Name;

    /// Add to this set a potential new member. If adding to the set was done, returns true.
    fn eq_and_mark(&mut self, needle: &Self::Name) -> bool;

    /// Is the set now complete with previous calls to [`Self::eq_and_mark`]?
    fn is_complete(&self) -> bool;

    /// If the set is partial, returns the last indice of the part, otherwise [`None`].
    fn is_partial(&self) -> Option<usize>;
}

#[derive(Error, Debug, PartialEq)]
pub enum AsciiNameConversionError {
    #[error("Name is empty")]
    IsEmpty,
    #[error("Found nul byte (0x00) at offset {0}")]
    NulByte(usize),
}

#[derive(Error, Debug)]
pub enum AsciiNameSetError {
    #[error("Invalid prefix")]
    InvalidPrefix(AsciiNameConversionError),
    #[error("Invalid suffix")]
    InvalidSuffix(AsciiNameConversionError),
}

// XXX: Vec<NonZeroU8> would be a better fit for the inner type.
#[derive(Debug, PartialEq)]
struct AsciiName(Vec<u8>);

pub struct AsciiNameSet {
    prefix: AsciiName,
    max_count: u8,
    suffix: AsciiName,
    mark: BitVec,
}

impl TryFrom<&[u8]> for AsciiName {
    type Error = AsciiNameConversionError;

    fn try_from(slice: &[u8]) -> Result<Self, Self::Error> {
        if slice.is_empty() {
            return Err(AsciiNameConversionError::IsEmpty);
        }

        let mut out = Vec::<u8>::with_capacity(slice.len());

        for (offset, byte) in slice.iter().enumerate() {
            if *byte == 0 {
                return Err(AsciiNameConversionError::NulByte(offset));
            }

            out.push(*byte);
        }

        Ok(Self(out))
    }
}

impl AsciiNameSet {
    pub fn new(prefix: &[u8], max_count: u8, suffix: &[u8]) -> Result<Self, AsciiNameSetError> {
        Ok(Self {
            prefix: prefix
                .try_into()
                .map_err(AsciiNameSetError::InvalidPrefix)?,
            max_count,
            suffix: suffix
                .try_into()
                .map_err(AsciiNameSetError::InvalidSuffix)?,
            mark: bitvec![0; (max_count as usize) + 1],
        })
    }

    pub fn generator(&self) -> NameIter {
        NameIter {
            generator: self,
            count: 0,
            done: false,
            max_name: self.prefix.0.len()
                + max_digits(self.max_count) as usize
                + self.suffix.0.len(),
        }
    }
}

impl NameSet for AsciiNameSet {
    type Name = AsciiName;

    fn eq_and_mark(&mut self, needle: &Self::Name) -> bool {
        let start_number = if let Some(val) = match_string(&needle.0, &self.prefix.0) {
            val
        } else {
            return false;
        };

        let end_number = if let Some(val) = match_uint(&needle.0[start_number..]) {
            val + start_number
        } else {
            return false;
        };

        // Safety: Function "match_uint" can only return an index containing digits.
        let index: u8 =
            match unsafe { from_utf8_unchecked(&needle.0[start_number..end_number]) }.parse() {
                Ok(val) => val,
                Err(_err) => return false,
            };

        if index > self.max_count {
            return false;
        }

        let end = if let Some(val) = match_string(&needle.0[end_number..], &self.suffix.0) {
            val + end_number
        } else {
            return false;
        };

        if needle.0.len() != end {
            return false;
        }

        self.mark.set(index as usize, true);
        true
    }

    fn is_complete(&self) -> bool {
        self.mark.all()
    }

    fn is_partial(&self) -> Option<usize> {
        partial(&self.mark)
    }
}

impl<'a> Iterator for NameIter<'a> {
    type Item = Vec<u8>;

    fn next(&mut self) -> Option<Self::Item> {
        if !self.done && self.count <= self.generator.max_count {
            let mut name = Vec::with_capacity(self.max_name);

            name.write_all(&self.generator.prefix.0).unwrap();
            write!(&mut name, "{}", self.count).unwrap();
            name.write_all(&self.generator.suffix.0).unwrap();

            if self.count == self.generator.max_count {
                self.done = true;
            } else {
                self.count += 1;
            }

            Some(name)
        } else {
            None
        }
    }
}

fn max_digits(val: u8) -> u8 {
    if val < 10 {
        1
    } else if val < 100 {
        2
    } else {
        3
    }
}

fn match_string(needle: &[u8], word: &[u8]) -> Option<usize> {
    if needle.len() >= word.len() && &needle[..word.len()] == word {
        Some(word.len())
    } else {
        None
    }
}

fn match_uint(needle: &[u8]) -> Option<usize> {
    enum State {
        Init,
        LeadingZero,
        NonZero,
    }

    if needle.is_empty() {
        return None;
    }

    let mut state = State::Init;
    for (index, ch) in needle.iter().enumerate() {
        let digit = (b'0'..b'9').contains(ch);

        // The .parse() method allows leading 0 as valid and we don't want that feature here.
        state = match (state, ch) {
            (State::Init, b'0') => State::LeadingZero,
            (State::LeadingZero, _) if digit => return None,
            _ => State::NonZero,
        };

        if !digit {
            if index == 0 {
                return None;
            } else {
                return Some(index);
            }
        }
    }

    Some(needle.len())
}

fn partial(marked: &BitVec) -> Option<usize> {
    if let Some(idx) = marked.as_bitslice().first_zero() {
        if marked[idx..].first_one() == None {
            idx.checked_sub(1)
        } else {
            None
        }
    } else {
        // No zero found: the set is complete!
        Some(marked.len() - 1)
    }
}

#[derive(Debug, Error)]
pub enum WoxNameError {
    #[error("Invalid character '{0}' in file name")]
    InvalidCharInFileName(char),
    #[error("Invalid special current directory name")]
    CurrentDirectory,
    #[error("Invalid special parent directory name")]
    ParentDirectory,
    #[error("I/O failed")]
    Io(#[from] io::Error),
}

#[derive(PartialEq, Eq, Hash, Copy, Clone, PartialOrd, Ord, Derivative)]
#[derivative(Debug = "transparent")]
pub struct WoxHashedName(u16);

pub struct WoxHashedNameSet {
    hashes: Vec<WoxHashedName>,
    mark: BitVec,
}

impl WoxHashedName {
    pub const MAX: u16 = u16::MAX;

    pub fn raw(&self) -> u16 {
        self.0
    }
}

impl From<&[u8]> for WoxHashedName {
    fn from(input: &[u8]) -> Self {
        Self(if input.is_empty() {
            // Follows ScummVM's BaseCCArchive::convertNameToId
            0xffff
        } else {
            input.iter().skip(1).fold(input[0] as u16, |acc, byte| {
                u16::wrapping_add(u16::rotate_right(acc, 7), *byte as u16)
            })
        })
    }
}

impl From<u16> for WoxHashedName {
    fn from(raw: u16) -> Self {
        Self(raw)
    }
}

impl FromStr for WoxHashedName {
    type Err = ParseIntError;

    fn from_str(input: &str) -> Result<Self, Self::Err> {
        let starting_offset = if input.starts_with("0x") || input.starts_with("0X") {
            2
        } else {
            0
        };

        Ok(Self(u16::from_str_radix(&input[starting_offset..], 16)?))
    }
}

impl Display for WoxHashedName {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        Display::fmt(&self.0, f)
    }
}

impl LowerHex for WoxHashedName {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        LowerHex::fmt(&self.0, f)
    }
}

impl From<&AsciiNameSet> for WoxHashedNameSet {
    fn from(set: &AsciiNameSet) -> Self {
        let hashes = set
            .generator()
            .map(|ascii| WoxHashedName::from(ascii.as_slice()))
            .collect::<Vec<_>>();
        let mark_len = hashes.len();

        Self {
            hashes,
            mark: bitvec![0; mark_len],
        }
    }
}

impl NameSet for WoxHashedNameSet {
    type Name = WoxHashedName;

    fn eq_and_mark(&mut self, needle: &Self::Name) -> bool {
        let mut found = false;

        for (offset, hash) in self.hashes.iter().enumerate() {
            if hash == needle {
                self.mark.set(offset, true);
                found = true;
            }
        }

        found
    }

    fn is_complete(&self) -> bool {
        self.mark.all()
    }

    fn is_partial(&self) -> Option<usize> {
        partial(&self.mark)
    }
}

pub struct WoxName(String);

impl WoxName {
    pub fn new(name: &str) -> Self {
        Self(name.to_owned())
    }

    pub fn inner(&self) -> &str {
        &self.0
    }
}

pub struct WoxReverseDictionary(HashMap<WoxHashedName, WoxName>);

pub struct ReadWoxReverseDictionary<R>(pub R);

impl<R> TryFrom<ReadWoxReverseDictionary<R>> for WoxReverseDictionary
where
    R: Read,
{
    type Error = WoxNameError;

    fn try_from(input: ReadWoxReverseDictionary<R>) -> Result<Self, Self::Error> {
        let mut list = HashMap::new();

        for maybe_line in BufReader::new(input.0).lines() {
            let name = maybe_line?;

            if name.is_empty() {
                continue;
            }

            // Forbid characters that have special meaning for POSIX file systems.
            for forbidden in ['/', char::from_u32(0).unwrap()] {
                if name.find(forbidden).is_some() {
                    return Err(WoxNameError::InvalidCharInFileName(forbidden));
                }
            }

            // Forbid attempts at a file system traversal attack.
            match name.as_str() {
                "." => return Err(WoxNameError::CurrentDirectory),
                ".." => return Err(WoxNameError::ParentDirectory),
                _ => list.insert(WoxHashedName::from(name.as_bytes()), WoxName::new(&name)),
            };
        }

        Ok(Self(list))
    }
}

impl Default for WoxReverseDictionary {
    fn default() -> Self {
        Self(HashMap::new())
    }
}

impl WoxReverseDictionary {
    pub fn inner(&self) -> &HashMap<WoxHashedName, WoxName> {
        &self.0
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Cursor;

    #[test]
    fn invalid_ascii_names() {
        assert_eq!(
            AsciiName::try_from("".as_bytes()),
            Err(AsciiNameConversionError::IsEmpty)
        );

        assert_eq!(
            AsciiName::try_from("test\0123".as_bytes()),
            Err(AsciiNameConversionError::NulByte(4))
        );
    }

    #[test]
    fn generator() {
        let generated = AsciiNameSet::new(b"PREFIX", 10, b".TXT")
            .unwrap()
            .generator()
            .collect::<Vec<_>>();

        const EXPECTED: &[&[u8]] = &[
            b"PREFIX0.TXT",
            b"PREFIX1.TXT",
            b"PREFIX2.TXT",
            b"PREFIX3.TXT",
            b"PREFIX4.TXT",
            b"PREFIX5.TXT",
            b"PREFIX6.TXT",
            b"PREFIX7.TXT",
            b"PREFIX8.TXT",
            b"PREFIX9.TXT",
            b"PREFIX10.TXT",
        ];

        assert_eq!(&generated, EXPECTED);
    }

    #[test]
    fn set_completion_ordered_markings() {
        let mut generator = AsciiNameSet::new(b"PREFIX", 2, b".TXT").unwrap();

        const TESTS: &[&[u8]] = &[b"PREFIX0.TXT", b"PREFIX1.TXT", b"PREFIX2.TXT"];

        assert_eq!(generator.is_partial(), None);

        for (idx, test) in TESTS.iter().enumerate() {
            assert!(!generator.is_complete());

            let converted: AsciiName = (*test).try_into().unwrap();
            assert!(generator.eq_and_mark(&converted));

            assert_eq!(generator.is_partial(), Some(idx));
        }

        assert!(generator.is_complete());
    }

    #[test]
    fn set_completion_unordered_markings() {
        let mut generator = AsciiNameSet::new(b"PREFIX", 2, b".TXT").unwrap();

        const TESTS: &[&[u8]] = &[b"PREFIX2.TXT", b"PREFIX0.TXT", b"PREFIX1.TXT"];

        for test in TESTS {
            assert!(!generator.is_complete());
            assert_eq!(generator.is_partial(), None);

            let converted: AsciiName = (*test).try_into().unwrap();
            assert!(generator.eq_and_mark(&converted));
        }

        assert!(generator.is_complete());
        assert_eq!(generator.is_partial(), Some(2));
    }

    #[test]
    fn fuzz_mark_parsing() {
        let mut generator = AsciiNameSet::new(b"PREFIX", 1, b".TXT").unwrap();

        const TESTS: &[&[u8]] = &[
            b"0.TXT",
            b"0",
            b".TXT",
            b"PREFIX01.TXT",
            b"PREFIX2.TXT",
            b"PREFIX0.TXT.TXT",
        ];

        for test in TESTS {
            let converted: AsciiName = (*test).try_into().unwrap();
            assert!(!generator.eq_and_mark(&converted));
        }
    }

    #[test]
    fn wox_hash() {
        // Not expected to happen for real, simply make sure we don't crash!
        const EMPTY: &[u8] = &[];
        assert_eq!(WoxHashedName::from(EMPTY), WoxHashedName(0xffff));

        const SIXTY_FOUR: &[u8] = &[64];
        assert_eq!(WoxHashedName::from(SIXTY_FOUR), WoxHashedName(64));

        const TWO_BYTES: &[u8] = &[12, 34];
        assert_eq!(WoxHashedName::from(TWO_BYTES), WoxHashedName(6178));
    }

    #[test]
    fn wox_hashed_name_set() {
        let ascii_set = AsciiNameSet::new(b"OUT", 5, b".SPL").unwrap();
        let mut wox_set = WoxHashedNameSet::from(&ascii_set);

        for (idx, ascii_name) in ascii_set.generator().enumerate() {
            assert!(wox_set.eq_and_mark(&WoxHashedName::from(ascii_name.as_slice())));
            assert_eq!(wox_set.is_partial(), Some(idx));
        }

        assert!(wox_set.is_complete());
        assert_eq!(
            &wox_set.hashes,
            &[
                WoxHashedName(0x2a0c),
                WoxHashedName(0x2a1c),
                WoxHashedName(0x2a2c),
                WoxHashedName(0x2a3c),
                WoxHashedName(0x284c),
                WoxHashedName(0x2a5c)
            ]
        );
    }

    #[test]
    fn wox_reverse_dictionary() {
        // Allow lines with only the file name.
        WoxReverseDictionary::try_from(ReadWoxReverseDictionary(Cursor::new(b"A.TXT\n"))).unwrap();

        // Lines can also come with the hash value as well as the expected file size in bytes.
        WoxReverseDictionary::try_from(ReadWoxReverseDictionary(Cursor::new(b"A.TXT\n"))).unwrap();

        // Allow empty lines.
        assert!(
            WoxReverseDictionary::try_from(ReadWoxReverseDictionary(Cursor::new(b"\n")))
                .unwrap()
                .0
                .is_empty()
        );

        // File names should be POSIX compatible, no slashes nor NUL and do now allow names with special meaning.
        for test in &[
            "INVALID/NAME.TXT\n".as_bytes(),
            "INVALID\0NAME.TXT\n".as_bytes(),
            ".\n".as_bytes(),
            "..\n".as_bytes(),
        ] {
            assert!(
                WoxReverseDictionary::try_from(ReadWoxReverseDictionary(Cursor::new(test)))
                    .is_err()
            );
        }
    }
}
