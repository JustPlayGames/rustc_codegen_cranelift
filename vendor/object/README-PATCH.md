# object 0.40.0, patched

The crates.io release of `object` 0.40.0 with one change: `write::Object`'s symbol map and
`write::StringTable` use hashbrown's default hasher (foldhash) in every build. Upstream picks
std's `HashMap` (SipHash) whenever the `std` or `write_std` feature is on, which every user of
the writer here turns on. Hashing every symbol name twice with SipHash cost about 0.5% of a
rustc run's instructions with this backend. Only hashing changes: insertion order, and with it
every file the writer produces, stays the same.

Drop this directory and the `[patch.crates-io]` entry once an `object` release does the same.
