# woxar
_woxar_ is an application that extract and create .CC archive files from _Might and Magic® IV & V: World of Xeen_. This repository doesn't store the original data files, they must be obtained separately. It is command line driven and can be easily integrated into existing scripts.

## Building
This software requires a recent [Rust](https://www.rust-lang.org) compiler (tested with 1.44.0) as well as [Cargo](https://crates.io), the native build engine for _Rust_. These are likely already packaged for your Linux distribution of choice. The binary generated by the build process will have no dependency outside of the standard C library.

The software can be built using this command:
```sh
cargo build --release
```
Note: The previous command will download several _Rust_ 3rd party libraries so network access is mandatory for the first invocation.

## Example Usage
Extract _xeen.cc_ into directory _extracted_:
```sh
target/release/woxar extract --archive xeen.cc --root extracted --dictionary data/xeen.fl
```
Modify the files in _extracted_ and then repack your modifications as _repacked.cc_:
```sh
target/release/woxar create --archive repacked.cc --root extracted
```

## Archive Format Limitations
This file format was designed to be deliberately obfuscated, likely to prevent users easily modify the game data. All the data is scrambled with an "rotate and add" cipher.

The second layer of obfuscation is the lack of file names in the archive, only a hashes are present. As a workaround, this software provides the real names of the files in the data/\*.fl files. Note that this is not a cryptographic hash and only 16 bits and as a result, it's trivial to have hash collisions. _woxar_ allows the extraction and creation of archives without file names. In this case, all the file names will be a unsigned 16 bits integer.

Other limitations not related to the obfuscation:
- Each file is also limited to 64K bytes in size.
- Each file offset is encoded as a 24 bit integer value. This puts a soft cap to a useful archive size to about 16.8M.

## Related Links
- [Original games on GOG](https://www.gog.com/game/might_and_magic_6_limited_edition)
- [Open Source implementation in ScummVM](https://www.scummvm.org/)

## To Do
- Add support for Might and Magic III: Isles of Terra.
- Add support for Might and Magic: Swords of Xeen.
- Add support for save games generated by these games, they use a similar file format.
- Improve unit test coverage.
