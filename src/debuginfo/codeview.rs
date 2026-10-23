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
const S_UDT: u16 = 0x1108;
const S_LOCAL: u16 = 0x113e;
const S_DEFRANGE_FRAMEPOINTER_REL: u16 = 0x1142;
const S_DEFRANGE_FRAMEPOINTER_REL_FULL_SCOPE: u16 = 0x1144;

/// `S_LOCAL` flags: the variable is a parameter.
const CV_LVARFLAG_ISPARAM: u16 = 0x0001;
/// `S_FRAMEPROC` flags: locals and parameters are addressed from the stack pointer (RSP / SP),
/// which Cranelift keeps fixed after the prologue.
const FRAMEPROC_SP_BASED: u32 = (1 << 14) | (1 << 16);

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

struct CvLocal {
    name: String,
    type_index: u32,
    is_param: bool,
    sp_offset: i32,
    /// Where the variable is in scope; `None`: the whole function.
    ranges: Option<Vec<(u32, u32)>>,
}

struct CvFunction {
    func_id: FuncId,
    locals: Vec<CvLocal>,
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
    pub(super) types: super::codeview_types::CvTypeTable,
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
            types: {
                // .debug$T starts with an empty argument list and `void ()` (`PROC_TYPE`).
                let mut types = CV_SIGNATURE_C13.to_le_bytes().to_vec();
                type_record(&mut types, LF_ARGLIST, |r| r.extend_from_slice(&0u32.to_le_bytes()));
                type_record(&mut types, LF_PROCEDURE, |r| {
                    r.extend_from_slice(&T_VOID.to_le_bytes()); // return type
                    r.push(0); // calling convention: near C
                    r.push(0); // function attributes
                    r.extend_from_slice(&0u16.to_le_bytes()); // parameter count
                    r.extend_from_slice(&TYPE_INDEX_BEGIN.to_le_bytes()); // argument list
                });
                super::codeview_types::CvTypeTable::new(types, PROC_TYPE + 1)
            },
        })
    }

    /// Records the path and checksum of a file the line program already knows as `file_id`.
    pub(crate) fn add_file(&mut self, file_id: FileId, dir: &[u8], name: &[u8], sf: &SourceFile) {
        if self.file_map.contains_key(&file_id) {
            return;
        }
        let path = full_path(&self.comp_dir, dir, name);

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
        source_locs: &indexmap::IndexSet<(FileId, u64, u64, u32)>,
        function_loc: (FileId, u64, u64),
        variables: &[super::variables::DebugVariable],
        scope_parents: &[Option<u32>],
        scope_ranges: &[Vec<(u32, u32)>],
    ) -> CodeOffset {
        let mcr = context.compiled_code().unwrap();
        let code_len = mcr.buffer.total_size();
        assert_ne!(code_len, 0);

        let mut lines: Vec<CvLine> = Vec::new();
        let mut body_start = None;
        for &MachSrcLoc { start, end: _, loc } in mcr.buffer.get_srclocs_sorted() {
            let loc = loc.as_abs();
            let (file_id, line, _col) = if loc.is_default() {
                // Code without a location inside the body continues the previous line (see
                // `create_debug_lines`); the prologue belongs to the function's line.
                if body_start.is_some() {
                    continue;
                }
                function_loc
            } else {
                if body_start.is_none() {
                    body_start = Some(start);
                }
                let (file_id, line, column, _) = source_locs[loc.bits() as usize];
                (file_id, line, column)
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

        let mut locals = Vec::new();
        if let Some(frame_layout) = mcr.buffer.frame_layout() {
            for var in variables {
                let Some(sp_offset) = var.sp_offset(frame_layout) else { continue };
                let Ok(sp_offset) = i32::try_from(sp_offset) else { continue };
                let scope = var.scope as usize;
                let ranges = match scope_parents.get(scope) {
                    Some(Some(_)) if scope_ranges[scope].is_empty() => continue,
                    Some(Some(_)) => Some(scope_ranges[scope].clone()),
                    _ => None,
                };
                locals.push(CvLocal {
                    name: var.name.clone(),
                    type_index: var.cv_type,
                    is_param: var.arg_index.is_some(),
                    sp_offset,
                    ranges,
                });
            }
        }

        self.functions.push(CvFunction {
            func_id,
            locals,
            name: info.name,
            code_len,
            body_start: body_start.unwrap_or(0),
            lines,
        });
        code_len
    }

    pub(crate) fn emit(&self, product: &mut ObjectProduct) {
        let mut out = Vec::new();
        // (offset in the section, function, true = SECREL / false = SECTION, addend)
        let mut relocs: Vec<(usize, FuncId, bool, i64)> = Vec::new();

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
                relocs.push((base + 32, func.func_id, true, 0));
                relocs.push((base + 36, func.func_id, false, 0));
                record(out, S_FRAMEPROC, |r| {
                    r.extend_from_slice(&0u32.to_le_bytes()); // cbFrame
                    r.extend_from_slice(&0u32.to_le_bytes()); // cbPad
                    r.extend_from_slice(&0u32.to_le_bytes()); // offPad
                    r.extend_from_slice(&0u32.to_le_bytes()); // cbSaveRegs
                    r.extend_from_slice(&0u32.to_le_bytes()); // offExHdr
                    r.extend_from_slice(&0u16.to_le_bytes()); // sectExHdr
                    r.extend_from_slice(&FRAMEPROC_SP_BASED.to_le_bytes());
                });
                for local in &func.locals {
                    record(out, S_LOCAL, |r| {
                        let ty = self.types.complete_type(local.type_index);
                        r.extend_from_slice(&ty.to_le_bytes());
                        let flags = if local.is_param { CV_LVARFLAG_ISPARAM } else { 0 };
                        r.extend_from_slice(&flags.to_le_bytes());
                        cstr(r, local.name.as_bytes());
                    });
                    let Some(ranges) = &local.ranges else {
                        record(out, S_DEFRANGE_FRAMEPOINTER_REL_FULL_SCOPE, |r| {
                            r.extend_from_slice(&local.sp_offset.to_le_bytes());
                        });
                        continue;
                    };
                    for &(start, end) in ranges {
                        // A range covers at most 0xffff bytes.
                        let mut start = start;
                        while start < end {
                            let len = (end - start).min(0xffff);
                            let base = out.len();
                            record(out, S_DEFRANGE_FRAMEPOINTER_REL, |r| {
                                r.extend_from_slice(&local.sp_offset.to_le_bytes());
                                r.extend_from_slice(&0u32.to_le_bytes()); // start (SECREL)
                                r.extend_from_slice(&0u16.to_le_bytes()); // section (SECTION)
                                r.extend_from_slice(&(len as u16).to_le_bytes());
                            });
                            relocs.push((base + 8, func.func_id, true, i64::from(start)));
                            relocs.push((base + 12, func.func_id, false, 0));
                            start += len;
                        }
                    }
                }
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
                relocs.push((base, func.func_id, true, 0));
                relocs.push((base + 4, func.func_id, false, 0));

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

        // A user-defined type symbol for every complete aggregate and enum, as LLVM writes: they
        // keep the complete records in link.exe's PDB and let debuggers find types by name.
        if !self.types.udts.is_empty() {
            subsection(&mut out, DEBUG_S_SYMBOLS, |out| {
                for (name, ty) in &self.types.udts {
                    record(out, S_UDT, |r| {
                        r.extend_from_slice(&ty.to_le_bytes());
                        cstr(r, truncate(name, 4000).as_bytes());
                    });
                }
            });
        }

        // link.exe rejects an empty file checksum subsection (LNK1103), as in an object without
        // any line table (the allocator shim): leave both tables out then.
        if !checksums.is_empty() {
            subsection(&mut out, DEBUG_S_FILECHKSMS, |out| out.extend_from_slice(&checksums));
            subsection(&mut out, DEBUG_S_STRINGTABLE, |out| out.extend_from_slice(&strings));
        }

        let types_section =
            product.object.add_section(Vec::new(), b".debug$T".to_vec(), SectionKind::Debug);
        product.object.section_mut(types_section).set_data(self.types.data.clone(), 4);

        let section =
            product.object.add_section(Vec::new(), b".debug$S".to_vec(), SectionKind::Debug);
        // COFF relocations have implicit addends: set the data first.
        product.object.section_mut(section).set_data(out, 4);
        for (offset, func_id, secrel, addend) in relocs {
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
                        addend,
                    },
                )
                .unwrap();
        }
    }
}

fn is_absolute(p: &[u8]) -> bool {
    p.first() == Some(&b'/') || p.first() == Some(&b'\\') || (p.len() > 1 && p[1] == b':')
}

/// The path of a source file as the file checksum table names it, built as LLVM's
/// `CodeViewDebug::getFullFilepath` does: a Unix path is kept as it is, anything else is a Windows
/// path with backslashes only and no `.`, `..` or doubled separators. Debuggers take the file
/// name after the last backslash: with a slash left in, cdb never finds `bp file.rs:line`.
fn full_path(comp_dir: &[u8], dir: &[u8], name: &[u8]) -> Vec<u8> {
    let mut full_dir = Vec::new();
    if !is_absolute(dir) && !comp_dir.is_empty() {
        full_dir.extend_from_slice(comp_dir);
    }
    if !dir.is_empty() {
        if !full_dir.is_empty() && !matches!(full_dir.last(), Some(b'/' | b'\\')) {
            full_dir.push(if full_dir.contains(&b'\\') { b'\\' } else { b'/' });
        }
        full_dir.extend_from_slice(dir);
    }
    let dir = &full_dir[..];

    if dir.first() == Some(&b'/') || name.first() == Some(&b'/') {
        if name.first() == Some(&b'/') || dir.is_empty() {
            return name.to_vec();
        }
        let mut path = dir.to_vec();
        if path.last() != Some(&b'/') {
            path.push(b'/');
        }
        path.extend_from_slice(name);
        return path;
    }

    let mut path = Vec::new();
    if (name.len() > 1 && name[1] == b':') || dir.is_empty() {
        path.extend_from_slice(name);
    } else {
        path.extend_from_slice(dir);
        path.push(b'\\');
        path.extend_from_slice(name);
    }
    // Canonicalize textually, as LLVM: the files may not exist where this runs.
    let path: Vec<u8> = path.into_iter().map(|b| if b == b'/' { b'\\' } else { b }).collect();
    let mut parts: Vec<&[u8]> = Vec::new();
    let leading = path.iter().take_while(|&&b| b == b'\\').count().min(2);
    for part in path[leading..].split(|&b| b == b'\\') {
        match part {
            b"" | b"." => {}
            b".." if parts.last().is_some_and(|p| *p != b".." && !p.ends_with(b":")) => {
                parts.pop();
            }
            _ => parts.push(part),
        }
    }
    let mut out = vec![b'\\'; leading];
    for (i, part) in parts.iter().enumerate() {
        if i > 0 {
            out.push(b'\\');
        }
        out.extend_from_slice(part);
    }
    out
}

pub(super) fn truncate(s: &str, max: usize) -> &str {
    if s.len() <= max {
        return s;
    }
    let mut end = max;
    while !s.is_char_boundary(end) {
        end -= 1;
    }
    &s[..end]
}

pub(super) fn cstr(out: &mut Vec<u8>, s: &[u8]) {
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
pub(super) fn type_record(out: &mut Vec<u8>, kind: u16, f: impl FnOnce(&mut Vec<u8>)) {
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
