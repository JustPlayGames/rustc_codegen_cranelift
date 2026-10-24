# object 0.40.0, patched

The crates.io release of `object` 0.40.0 with three changes.

1. `write::Object`'s symbol map and `write::StringTable` use hashbrown's default hasher
   (foldhash) in every build. Upstream picks std's `HashMap` (SipHash) whenever the `std` or
   `write_std` feature is on, which every user of the writer here turns on. Hashing every
   symbol name twice with SipHash cost about 0.5% of a rustc run's instructions with this
   backend. Only hashing changes: insertion order, and with it every file the writer
   produces, stays the same.

2. The COFF writer writes the big object format (`ANON_OBJECT_HEADER_BIGOBJ`, 32-bit section
   numbers, 20-byte symbol records, as LLVM and `cl /bigobj` write it) when an object has more
   than 65,279 sections. Function sections on Windows give a codegen unit three sections per
   function (code, .pdata, .xdata), and the plain format's 16-bit section numbers wrapped:
   symbols then pointed at the wrong sections. `write::coff::Writer::set_bigobj` and
   `reserve_section_headers_u32` are the low-level API for it. Test: `tests/coff_bigobj.rs`
   (`cargo test --manifest-path vendor/object/Cargo.toml --features read,write,std --release
   --test coff_bigobj`).

3. The COFF writer's search for a defined external outside every COMDAT (to name weak
   symbols' defaults) looked through every COMDAT's sections for each symbol: quadratic once
   every function has a COMDAT of its own (1.7 s of a 1.9 s write for 32,639 functions). It
   marks the COMDATs' sections once now; the output is unchanged.

Drop this directory and the `[patch.crates-io]` entry once an `object` release does the same.
