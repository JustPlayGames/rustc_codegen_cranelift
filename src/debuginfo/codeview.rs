//! CodeView debuginfo (`.debug$S`) for MSVC targets.
//!
//! MSVC-style linkers (link.exe, lld-link) build the PDB from the CodeView records in the
//! objects' `.debug$S` sections; they ignore DWARF. This emits what backtraces and debuggers need
//! to map code to source: a procedure symbol per function (name and code range) and C13 line
//! tables, with the file checksum and string tables they refer to.

use cranelift_codegen::MachSrcLoc;
use cranelift_codegen::binemit::CodeOffset;
use cranelift_object::ObjectProduct;
use gimli::write::FileId;
use object::write::Relocation;
use object::{RelocationEncoding, RelocationFlags, RelocationKind, SectionKind};
use rustc_span::{SourceFile, SourceFileHashAlgorithm};

use crate::prelude::*;

const CV_SIGNATURE_C13: u32 = 4;

const DEBUG_S_SYMBOLS: u32 = 0xf1;
const DEBUG_S_LINES: u32 = 0xf2;
const DEBUG_S_STRINGTABLE: u32 = 0xf3;
const DEBUG_S_FILECHKSMS: u32 = 0xf4;

const S_END: u16 = 0x0006;
const S_FRAMEPROC: u16 = 0x1012;
const S_OBJNAME: u16 = 0x1101;
const S_GPROC32: u16 = 0x1110;
const S_COMPILE3: u16 = 0x113c;

const LF_PROCEDURE: u16 = 0x1008;
const LF_ARGLIST: u16 = 0x1201;
const T_VOID: u32 = 0x0003;
/// The first type index of an object's `.debug$T`: below are the built-in types.
const TYPE_INDEX_BEGIN: u32 = 0x1000;
/// `void ()`: the type every procedure symbol gets (debuggers skip procedures without one).
const PROC_TYPE: u32 = TYPE_INDEX_BEGIN + 1;

const CV_PFLAG_NOFPO: u8 = 0x01;

const CV_CFL_RUST: u32 = 0x15;
const CV_CFL_X64: u16 = 0xd0;
const CV_CFL_ARM64: u16 = 0xf6;

const CHKSUM_TYPE_NONE: u8 = 0;
const CHKSUM_TYPE_MD5: u8 = 1;
const CHKSUM_TYPE_SHA1: u8 = 2;
const CHKSUM_TYPE_SHA_256: u8 = 3;

/// Line numbers are 24 bits wide in a C13 line entry.
const MAX_LINE: u64 = 0x00ff_ffff;

struct CvFile {
    path: Vec<u8>,
    checksum_kind: u8,
    checksum: Vec<u8>,
}

#[derive(Clone, Copy, PartialEq, Eq)]
struct CvLine {
    offset: u32,
    file: u32,
    line: u32,
}

struct CvFunction {
    func_id: FuncId,
    name: String,
    code_len: u32,
    /// Offset of the first instruction with a source location of its own (after the prologue).
    body_start: u32,
    lines: Vec<CvLine>,
}

/// The procedure name of a function, recorded by `define_function`.
pub(crate) struct CvFunctionInfo {
    pub(crate) name: String,
}

pub(crate) struct CodeViewUnit {
    machine: u16,
    obj_name: String,
    producer: String,
    comp_dir: Vec<u8>,
    files: Vec<CvFile>,
    file_map: FxHashMap<FileId, u32>,
    functions: Vec<CvFunction>,
}

impl CodeViewUnit {
    pub(crate) fn new(
        arch: target_lexicon::Architecture,
        obj_name: String,
        producer: String,
        comp_dir: &[u8],
    ) -> Option<Self> {
        let machine = match arch {
            target_lexicon::Architecture::X86_64 | target_lexicon::Architecture::X86_64h => {
                CV_CFL_X64
            }
            target_lexicon::Architecture::Aarch64(_) => CV_CFL_ARM64,
            _ => return None,
        };
        Some(CodeViewUnit {
            machine,
            obj_name,
            producer,
            comp_dir: comp_dir.to_vec(),
            files: Vec::new(),
            file_map: FxHashMap::default(),
            functions: Vec::new(),
        })
    }

    /// Records the path and checksum of a file the line program already knows as `file_id`.
    pub(crate) fn add_file(&mut self, file_id: FileId, dir: &[u8], name: &[u8], sf: &SourceFile) {
        if self.file_map.contains_key(&file_id) {
            return;
        }
        let absolute = |p: &[u8]| {
            p.first() == Some(&b'/') || p.first() == Some(&b'\\') || (p.len() > 1 && p[1] == b':')
        };
        // Built on Windows, the paths are Windows paths: use one separator style throughout.
        let windows =
            self.comp_dir.contains(&b'\\') || (self.comp_dir.len() > 1 && self.comp_dir[1] == b':');
        let sep = if windows { b'\\' } else { b'/' };
        let mut path = Vec::new();
        if !absolute(dir) && !absolute(name) && !self.comp_dir.is_empty() {
            path.extend_from_slice(&self.comp_dir);
            path.push(sep);
        }
        if !dir.is_empty() && !absolute(name) {
            path.extend_from_slice(dir);
            path.push(sep);
        }
        path.extend_from_slice(name);
        if windows {
            for b in &mut path {
                if *b == b'/' {
                    *b = b'\\';
                }
            }
        }

        let (checksum_kind, checksum) = match sf.src_hash.kind {
            SourceFileHashAlgorithm::Md5 => (CHKSUM_TYPE_MD5, sf.src_hash.hash_bytes().to_vec()),
            SourceFileHashAlgorithm::Sha1 => (CHKSUM_TYPE_SHA1, sf.src_hash.hash_bytes().to_vec()),
            SourceFileHashAlgorithm::Sha256 => {
                (CHKSUM_TYPE_SHA_256, sf.src_hash.hash_bytes().to_vec())
            }
            _ => (CHKSUM_TYPE_NONE, Vec::new()),
        };

        let index = u32::try_from(self.files.len()).unwrap();
        self.files.push(CvFile { path, checksum_kind, checksum });
        self.file_map.insert(file_id, index);
    }

    /// Records a compiled function: its code range and the line table from Cranelift's source
    /// locations (`source_locs` maps a `SourceLoc` index to file, line and column).
    pub(crate) fn add_function(
        &mut self,
        func_id: FuncId,
        info: CvFunctionInfo,
        context: &Context,
        source_locs: &indexmap::IndexSet<(FileId, u64, u64)>,
        function_loc: (FileId, u64, u64),
    ) -> CodeOffset {
        let mcr = context.compiled_code().unwrap();
        let code_len = mcr.buffer.total_size();
        assert_ne!(code_len, 0);

        let mut lines: Vec<CvLine> = Vec::new();
        let mut body_start = None;
        for &MachSrcLoc { start, end: _, loc } in mcr.buffer.get_srclocs_sorted() {
            let loc = loc.as_abs();
            let (file_id, line, _col) = if loc.is_default() {
                function_loc
            } else {
                if body_start.is_none() {
                    body_start = Some(start);
                }
                source_locs[loc.bits() as usize]
            };
            if line == 0 || line > MAX_LINE {
                continue;
            }
            let Some(&file) = self.file_map.get(&file_id) else { continue };
            let row = CvLine { offset: start, file, line: line as u32 };
            match lines.last() {
                Some(last) if last.file == row.file && last.line == row.line => {}
                Some(last) if last.offset == row.offset => {
                    *lines.last_mut().unwrap() = row;
                }
                _ => lines.push(row),
            }
        }

        self.functions.push(CvFunction {
            func_id,
            name: info.name,
            code_len,
            body_start: body_start.unwrap_or(0),
            lines,
        });
        code_len
    }

    pub(crate) fn emit(&self, product: &mut ObjectProduct) {
        let mut out = Vec::new();
        // (offset in the section, function, true = SECREL, false = SECTION)
        let mut relocs: Vec<(usize, FuncId, bool)> = Vec::new();

        out.extend_from_slice(&CV_SIGNATURE_C13.to_le_bytes());

        subsection(&mut out, DEBUG_S_SYMBOLS, |out| {
            record(out, S_OBJNAME, |r| {
                r.extend_from_slice(&0u32.to_le_bytes());
                cstr(r, self.obj_name.as_bytes());
            });
            record(out, S_COMPILE3, |r| {
                r.extend_from_slice(&CV_CFL_RUST.to_le_bytes());
                r.extend_from_slice(&self.machine.to_le_bytes());
                // Front end and back end versions: none that a debugger would special-case.
                for v in [1u16, 0, 0, 0, 1, 0, 0, 0] {
                    r.extend_from_slice(&v.to_le_bytes());
                }
                cstr(r, self.producer.as_bytes());
            });
        });

        // The file checksum table: lines refer to files by their entry's byte offset.
        let mut strings = vec![0u8];
        let mut checksums = Vec::new();
        let mut file_offsets = Vec::with_capacity(self.files.len());
        for file in &self.files {
            file_offsets.push(u32::try_from(checksums.len()).unwrap());
            let name_offset = u32::try_from(strings.len()).unwrap();
            strings.extend_from_slice(&file.path);
            strings.push(0);
            checksums.extend_from_slice(&name_offset.to_le_bytes());
            checksums.push(u8::try_from(file.checksum.len()).unwrap());
            checksums.push(file.checksum_kind);
            checksums.extend_from_slice(&file.checksum);
            pad4(&mut checksums, 0);
        }

        for func in &self.functions {
            subsection(&mut out, DEBUG_S_SYMBOLS, |out| {
                let base = out.len();
                // S_GPROC32 for every function, as LLVM writes for Rust functions: debuggers
                // find procedures by name through the PDB's globals stream.
                record(out, S_GPROC32, |r| {
                    r.extend_from_slice(&0u32.to_le_bytes()); // pParent
                    r.extend_from_slice(&0u32.to_le_bytes()); // pEnd
                    r.extend_from_slice(&0u32.to_le_bytes()); // pNext
                    r.extend_from_slice(&func.code_len.to_le_bytes());
                    r.extend_from_slice(&func.body_start.to_le_bytes()); // DbgStart
                    r.extend_from_slice(&func.code_len.to_le_bytes()); // DbgEnd
                    r.extend_from_slice(&PROC_TYPE.to_le_bytes()); // type
                    r.extend_from_slice(&0u32.to_le_bytes()); // offset (SECREL)
                    r.extend_from_slice(&0u16.to_le_bytes()); // segment (SECTION)
                    r.push(CV_PFLAG_NOFPO); // flags: has a frame pointer
                    // A record is at most 64 KiB: cut very long (generic) names.
                    cstr(r, truncate(&func.name, 4096).as_bytes());
                });
                relocs.push((base + 32, func.func_id, true));
                relocs.push((base + 36, func.func_id, false));
                record(out, S_FRAMEPROC, |r| {
                    r.extend_from_slice(&0u32.to_le_bytes()); // cbFrame
                    r.extend_from_slice(&0u32.to_le_bytes()); // cbPad
                    r.extend_from_slice(&0u32.to_le_bytes()); // offPad
                    r.extend_from_slice(&0u32.to_le_bytes()); // cbSaveRegs
                    r.extend_from_slice(&0u32.to_le_bytes()); // offExHdr
                    r.extend_from_slice(&0u16.to_le_bytes()); // sectExHdr
                    // Locals and parameters are addressed from the frame pointer (RBP / X29).
                    r.extend_from_slice(&((2u32 << 14) | (2u32 << 16)).to_le_bytes());
                });
                record(out, S_END, |_| {});
            });

            if func.lines.is_empty() {
                continue;
            }
            subsection(&mut out, DEBUG_S_LINES, |out| {
                let base = out.len();
                out.extend_from_slice(&0u32.to_le_bytes()); // offCon (SECREL)
                out.extend_from_slice(&0u16.to_le_bytes()); // segCon (SECTION)
                out.extend_from_slice(&0u16.to_le_bytes()); // flags: no columns
                out.extend_from_slice(&func.code_len.to_le_bytes());
                relocs.push((base, func.func_id, true));
                relocs.push((base + 4, func.func_id, false));

                for block in func.lines.chunk_by(|a, b| a.file == b.file) {
                    let n = u32::try_from(block.len()).unwrap();
                    out.extend_from_slice(&file_offsets[block[0].file as usize].to_le_bytes());
                    out.extend_from_slice(&n.to_le_bytes());
                    out.extend_from_slice(&(12 + 8 * n).to_le_bytes());
                    for line in block {
                        out.extend_from_slice(&line.offset.to_le_bytes());
                        // linenumStart (24 bits), deltaLineEnd (7 bits) = 0, fStatement = 1
                        out.extend_from_slice(&(line.line | 0x8000_0000).to_le_bytes());
                    }
                }
            });
        }

        subsection(&mut out, DEBUG_S_FILECHKSMS, |out| out.extend_from_slice(&checksums));
        subsection(&mut out, DEBUG_S_STRINGTABLE, |out| out.extend_from_slice(&strings));

        // .debug$T: an empty argument list and `void ()` (`PROC_TYPE`).
        let mut types = CV_SIGNATURE_C13.to_le_bytes().to_vec();
        type_record(&mut types, LF_ARGLIST, |r| r.extend_from_slice(&0u32.to_le_bytes()));
        type_record(&mut types, LF_PROCEDURE, |r| {
            r.extend_from_slice(&T_VOID.to_le_bytes()); // return type
            r.push(0); // calling convention: near C
            r.push(0); // function attributes
            r.extend_from_slice(&0u16.to_le_bytes()); // parameter count
            r.extend_from_slice(&TYPE_INDEX_BEGIN.to_le_bytes()); // argument list
        });
        let types_section =
            product.object.add_section(Vec::new(), b".debug$T".to_vec(), SectionKind::Debug);
        product.object.section_mut(types_section).set_data(types, 4);

        let section =
            product.object.add_section(Vec::new(), b".debug$S".to_vec(), SectionKind::Debug);
        // COFF relocations have implicit addends: set the data first.
        product.object.section_mut(section).set_data(out, 4);
        for (offset, func_id, secrel) in relocs {
            let symbol = product.function_symbol(func_id);
            let (kind, size) = if secrel {
                (RelocationKind::SectionOffset, 32)
            } else {
                (RelocationKind::SectionIndex, 16)
            };
            product
                .object
                .add_relocation(
                    section,
                    Relocation {
                        offset: u64::try_from(offset).unwrap(),
                        symbol,
                        flags: RelocationFlags::Generic {
                            kind,
                            encoding: RelocationEncoding::Generic,
                            size,
                        },
                        addend: 0,
                    },
                )
                .unwrap();
        }
    }
}

fn truncate(s: &str, max: usize) -> &str {
    if s.len() <= max {
        return s;
    }
    let mut end = max;
    while !s.is_char_boundary(end) {
        end -= 1;
    }
    &s[..end]
}

fn cstr(out: &mut Vec<u8>, s: &[u8]) {
    // CodeView names are NUL-terminated: an embedded NUL would cut the name short.
    out.extend(s.iter().map(|&b| if b == 0 { b'?' } else { b }));
    out.push(0);
}

fn pad4(out: &mut Vec<u8>, byte: u8) {
    while out.len() % 4 != 0 {
        out.push(byte);
    }
}

/// A subsection: kind, length, contents, padded to 4 bytes (the padding is not in the length).
fn subsection(out: &mut Vec<u8>, kind: u32, f: impl FnOnce(&mut Vec<u8>)) {
    out.extend_from_slice(&kind.to_le_bytes());
    let len_at = out.len();
    out.extend_from_slice(&0u32.to_le_bytes());
    let start = out.len();
    f(out);
    let len = u32::try_from(out.len() - start).unwrap();
    out[len_at..len_at + 4].copy_from_slice(&len.to_le_bytes());
    pad4(out, 0);
}

/// A type record: length (excluding itself), kind, contents, padded to 4 bytes with LF_PAD bytes.
fn type_record(out: &mut Vec<u8>, kind: u16, f: impl FnOnce(&mut Vec<u8>)) {
    let start = out.len();
    out.extend_from_slice(&0u16.to_le_bytes());
    out.extend_from_slice(&kind.to_le_bytes());
    f(out);
    while out.len() % 4 != 0 {
        let left = 4 - out.len() % 4;
        out.push(0xf0 | left as u8);
    }
    let len = u16::try_from(out.len() - start - 2).unwrap();
    out[start..start + 2].copy_from_slice(&len.to_le_bytes());
}

/// A symbol record: length (excluding itself), kind, contents, padded to 4 bytes.
fn record(out: &mut Vec<u8>, kind: u16, f: impl FnOnce(&mut Vec<u8>)) {
    let start = out.len();
    out.extend_from_slice(&0u16.to_le_bytes());
    out.extend_from_slice(&kind.to_le_bytes());
    f(out);
    pad4(out, 0);
    let len = u16::try_from(out.len() - start - 2).expect("CodeView record too long");
    out[start..start + 2].copy_from_slice(&len.to_le_bytes());
}
