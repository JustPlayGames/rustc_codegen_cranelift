//! A structural check of the CodeView debuginfo (`.debug$S`, `.debug$T`) in a COFF object, for the
//! rules MSVC's link.exe holds objects to. lld-link accepts what link.exe rejects ("LNK1103:
//! debugging information corrupt") or silently leaves out of the PDB, and link.exe only runs on
//! Windows, so this checks the same rules wherever the tests run.

use std::collections::{HashMap, HashSet};

const CV_SIGNATURE_C13: u32 = 4;

const DEBUG_S_SYMBOLS: u32 = 0xf1;
const DEBUG_S_LINES: u32 = 0xf2;
const DEBUG_S_STRINGTABLE: u32 = 0xf3;
const DEBUG_S_FILECHKSMS: u32 = 0xf4;

const S_END: u16 = 0x0006;
const S_GPROC32: u16 = 0x1110;
const S_LPROC32: u16 = 0x110f;
const S_UDT: u16 = 0x1108;
const S_LOCAL: u16 = 0x113e;
const S_DEFRANGE_FRAMEPOINTER_REL: u16 = 0x1142;

const LF_MODIFIER: u16 = 0x1001;
const LF_POINTER: u16 = 0x1002;
const LF_BITFIELD: u16 = 0x1205;
const LF_NESTTYPE: u16 = 0x1510;
const LF_STMEMBER: u16 = 0x150e;
const LF_PROCEDURE: u16 = 0x1008;
const LF_ARGLIST: u16 = 0x1201;
const LF_FIELDLIST: u16 = 0x1203;
const LF_ARRAY: u16 = 0x1503;
const LF_STRUCTURE: u16 = 0x1505;
const LF_UNION: u16 = 0x1506;
const LF_ENUM: u16 = 0x1507;
const LF_INDEX: u16 = 0x1404;
const LF_MEMBER: u16 = 0x150d;
const LF_ENUMERATE: u16 = 0x1502;

const PROP_FWDREF: u16 = 0x0080;
const PROP_HAS_UNIQUE_NAME: u16 = 0x0200;

/// The longest type record LLVM writes, length field included.
const MAX_TYPE_RECORD: usize = 0xff00;

const IMAGE_REL_AMD64_SECTION: u16 = 0x000a;
const IMAGE_REL_AMD64_SECREL: u16 = 0x000b;

/// What a check found besides the problems, so that a test can tell it checked something.
#[derive(Debug, Default)]
pub(crate) struct Summary {
    pub(crate) procedures: usize,
    pub(crate) line_blocks: usize,
    pub(crate) complete_udts: usize,
    pub(crate) continuations: usize,
    pub(crate) locals: usize,
}

struct Section<'a> {
    name: String,
    data: &'a [u8],
    /// (offset, type)
    relocs: Vec<(u32, u16)>,
}

fn u16_at(d: &[u8], o: usize) -> Option<u16> {
    Some(u16::from_le_bytes(d.get(o..o + 2)?.try_into().unwrap()))
}

fn u32_at(d: &[u8], o: usize) -> Option<u32> {
    Some(u32::from_le_bytes(d.get(o..o + 4)?.try_into().unwrap()))
}

fn sections(obj: &[u8]) -> Result<Vec<Section<'_>>, String> {
    let bad = || "not a COFF object".to_owned();
    let count = u16_at(obj, 2).ok_or_else(bad)? as usize;
    let symtab = u32_at(obj, 8).ok_or_else(bad)? as usize;
    let nsyms = u32_at(obj, 12).ok_or_else(bad)? as usize;
    let opt = u16_at(obj, 16).ok_or_else(bad)? as usize;
    let strtab = symtab + 18 * nsyms;
    let mut out = Vec::new();
    for i in 0..count {
        let h = 20 + opt + 40 * i;
        let raw = obj.get(h..h + 8).ok_or_else(bad)?;
        let raw = &raw[..raw.iter().position(|&b| b == 0).unwrap_or(8)];
        let name = if let Some(off) = raw.strip_prefix(b"/") {
            let off: usize =
                std::str::from_utf8(off).map_err(|_| bad())?.parse().map_err(|_| bad())?;
            let s = obj.get(strtab + off..).ok_or_else(bad)?;
            String::from_utf8_lossy(&s[..s.iter().position(|&b| b == 0).unwrap_or(s.len())])
                .into_owned()
        } else {
            String::from_utf8_lossy(raw).into_owned()
        };
        let size = u32_at(obj, h + 16).ok_or_else(bad)? as usize;
        let ptr = u32_at(obj, h + 20).ok_or_else(bad)? as usize;
        let rptr = u32_at(obj, h + 24).ok_or_else(bad)? as usize;
        let mut nrel = u16_at(obj, h + 32).ok_or_else(bad)? as usize;
        let characteristics = u32_at(obj, h + 36).ok_or_else(bad)?;
        let data = if ptr == 0 { &[][..] } else { obj.get(ptr..ptr + size).ok_or_else(bad)? };
        // IMAGE_SCN_LNK_NRELOC_OVFL: the count is in the first relocation, which counts itself.
        let mut first = 0;
        if characteristics & 0x0100_0000 != 0 && nrel == 0xffff {
            nrel = u32_at(obj, rptr).ok_or_else(bad)? as usize;
            first = 1;
        }
        let mut relocs = Vec::with_capacity(nrel);
        for r in first..nrel {
            let o = rptr + 10 * r;
            relocs.push((u32_at(obj, o).ok_or_else(bad)?, u16_at(obj, o + 8).ok_or_else(bad)?));
        }
        out.push(Section { name, data, relocs });
    }
    Ok(out)
}

/// A CodeView numeric leaf at `o`: its length in bytes.
fn numeric_len(d: &[u8], o: usize) -> Option<usize> {
    let v = u16_at(d, o)?;
    Some(match v {
        0..0x8000 => 2,
        0x8000 | 0x8001 => 3,
        0x8002 | 0x8010 => 4,
        0x8003 | 0x8004 | 0x8005 => 6,
        0x8009 | 0x800a | 0x8006 => 10,
        _ => return None,
    })
}

fn cstr_len(d: &[u8], o: usize) -> Option<usize> {
    Some(d.get(o..)?.iter().position(|&b| b == 0)? + 1)
}

struct TypeRecord<'a> {
    kind: u16,
    body: &'a [u8],
}

/// Checks the CodeView in `obj`; `Err` lists every rule a record breaks.
pub(crate) fn check(obj: &[u8]) -> Result<Summary, Vec<String>> {
    let mut problems = Vec::new();
    let mut summary = Summary::default();
    let sections = match sections(obj) {
        Ok(s) => s,
        Err(e) => return Err(vec![e]),
    };

    // .debug$T
    let mut types: Vec<TypeRecord<'_>> = Vec::new();
    for sec in sections.iter().filter(|s| s.name == ".debug$T") {
        if !types.is_empty() {
            problems.push("more than one .debug$T section".to_owned());
        }
        let d = sec.data;
        if u32_at(d, 0) != Some(CV_SIGNATURE_C13) {
            problems.push(".debug$T: no CV_SIGNATURE_C13".to_owned());
            continue;
        }
        let mut p = 4;
        while p < d.len() {
            let index = 0x1000 + types.len() as u32;
            let (Some(len), Some(kind)) = (u16_at(d, p), u16_at(d, p + 2)) else {
                problems.push(format!("type {index:#x}: truncated record"));
                break;
            };
            let len = len as usize;
            if 2 + len > MAX_TYPE_RECORD {
                problems.push(format!(
                    "type {index:#x}: record of {} bytes (> {MAX_TYPE_RECORD:#x})",
                    2 + len
                ));
            }
            if (2 + len) % 4 != 0 {
                problems.push(format!("type {index:#x}: record length {len} leaves it unaligned"));
            }
            let Some(body) = d.get(p + 4..p + 2 + len) else {
                problems.push(format!("type {index:#x}: record runs past the section"));
                break;
            };
            types.push(TypeRecord { kind, body });
            p += 2 + len;
        }
    }
    let next_type = 0x1000 + types.len() as u32;
    let valid = |ti: u32| ti < 0x1000 || ti < next_type;

    // The type indices each record refers to, the forward references and complete records of
    // aggregates by unique name.
    let mut refs: Vec<Vec<u32>> = Vec::with_capacity(types.len());
    let mut forward_unique: HashMap<u32, Vec<u8>> = HashMap::new();
    let mut complete_by_unique: HashMap<Vec<u8>, u32> = HashMap::new();
    let mut complete_udts: Vec<u32> = Vec::new();
    for (i, rec) in types.iter().enumerate() {
        let index = 0x1000 + i as u32;
        let b = rec.body;
        let mut r = Vec::new();
        match rec.kind {
            LF_POINTER | LF_ARRAY | LF_MODIFIER | LF_BITFIELD => r.extend(u32_at(b, 0)),
            LF_PROCEDURE => {
                r.extend(u32_at(b, 0));
                r.extend(u32_at(b, 8));
            }
            LF_ARGLIST => {
                let n = u32_at(b, 0).unwrap_or(0) as usize;
                r.extend((0..n).filter_map(|k| u32_at(b, 4 + 4 * k)));
            }
            LF_STRUCTURE | LF_UNION | LF_ENUM => {
                let props = u16_at(b, 2).unwrap_or(0);
                let (field_list, name_at) = match rec.kind {
                    LF_STRUCTURE => (u32_at(b, 4), 16),
                    LF_UNION => (u32_at(b, 4), 8),
                    _ => (u32_at(b, 8), 12),
                };
                if rec.kind == LF_ENUM {
                    r.extend(u32_at(b, 4));
                }
                r.extend(field_list.filter(|&f| f != 0));
                let name_at = if rec.kind == LF_ENUM {
                    Some(name_at)
                } else {
                    numeric_len(b, name_at).map(|n| name_at + n)
                };
                let has_unique = props & PROP_HAS_UNIQUE_NAME != 0;
                let unique = name_at.and_then(|at| {
                    let n = cstr_len(b, at)?;
                    if !has_unique {
                        return Some(None);
                    }
                    let u = cstr_len(b, at + n)?;
                    Some(Some(b[at + n..at + n + u - 1].to_vec()))
                });
                match unique {
                    None => problems.push(format!("type {index:#x}: unreadable name")),
                    Some(Some(unique)) if props & PROP_FWDREF != 0 => {
                        forward_unique.insert(index, unique);
                    }
                    Some(Some(unique)) => {
                        complete_by_unique.insert(unique, index);
                        complete_udts.push(index);
                    }
                    // Without a unique name (LLVM's nested types), nothing links a forward
                    // reference to it: records refer to it directly.
                    Some(None) => {}
                }
            }
            LF_FIELDLIST => {
                let mut o = 0;
                while o < b.len() {
                    let Some(leaf) = u16_at(b, o) else { break };
                    let end = match leaf {
                        LF_MEMBER => {
                            r.extend(u32_at(b, o + 4));
                            numeric_len(b, o + 8)
                                .and_then(|n| Some(o + 8 + n + cstr_len(b, o + 8 + n)?))
                        }
                        LF_NESTTYPE | LF_STMEMBER => {
                            r.extend(u32_at(b, o + 4));
                            cstr_len(b, o + 8).map(|n| o + 8 + n)
                        }
                        LF_ENUMERATE => numeric_len(b, o + 4)
                            .and_then(|n| Some(o + 4 + n + cstr_len(b, o + 4 + n)?)),
                        LF_INDEX => {
                            let target = u32_at(b, o + 4).unwrap_or(u32::MAX);
                            r.push(target);
                            summary.continuations += 1;
                            if target >= index {
                                problems.push(format!(
                                    "type {index:#x}: LF_INDEX to {target:#x}, not an earlier record"
                                ));
                            }
                            Some(o + 8)
                        }
                        _ => {
                            // Other members: stop, we can't size them.
                            break;
                        }
                    };
                    let Some(mut end) = end else {
                        problems.push(format!("type {index:#x}: truncated field list member"));
                        break;
                    };
                    // LF_PAD bytes up to the next 4-byte boundary of the record.
                    while end % 4 != 0 && end < b.len() {
                        let pad = b[end];
                        if pad & 0xf0 != 0xf0 {
                            problems
                                .push(format!("type {index:#x}: member not padded with LF_PAD"));
                        }
                        end += 1;
                    }
                    o = end;
                }
            }
            _ => {}
        }
        for &t in &r {
            if t >= 0x1000 && t >= index {
                problems.push(format!(
                    "type {index:#x} (kind {:#x}) refers to {t:#x}, not an earlier record",
                    rec.kind
                ));
            }
        }
        refs.push(r);
    }
    summary.complete_udts = complete_udts.len();

    // .debug$S
    let mut symbol_types: Vec<(u32, &'static str)> = Vec::new();
    let mut found_debug_s = false;
    // LLVM writes a `.debug$S` per COMDAT function, with the file tables in another one: they
    // are the object's.
    let mut checksums: Option<&[u8]> = None;
    let mut strings: Option<&[u8]> = None;
    let mut line_file_refs: Vec<u32> = Vec::new();
    for sec in sections.iter().filter(|s| s.name == ".debug$S") {
        found_debug_s = true;
        let d = sec.data;
        let relocs: HashMap<u32, u16> = sec.relocs.iter().copied().collect();
        let reloc_is = |at: usize, want: u16, what: &str, problems: &mut Vec<String>| {
            if relocs.get(&(at as u32)) != Some(&want) {
                problems.push(format!(".debug$S+{at:#x}: {what} without its relocation"));
            }
        };
        if u32_at(d, 0) != Some(CV_SIGNATURE_C13) {
            problems.push(".debug$S: no CV_SIGNATURE_C13".to_owned());
            continue;
        }
        let mut p = 4;
        while p < d.len() {
            let (Some(kind), Some(len)) = (u32_at(d, p), u32_at(d, p + 4)) else {
                problems.push(format!(".debug$S+{p:#x}: truncated subsection header"));
                break;
            };
            let start = p + 8;
            let len = len as usize;
            let Some(body) = d.get(start..start + len) else {
                problems.push(format!(".debug$S+{p:#x}: subsection runs past the section"));
                break;
            };
            match kind {
                DEBUG_S_SYMBOLS => {
                    let mut o = 0;
                    let mut scopes: Vec<u16> = Vec::new();
                    while o < body.len() {
                        let (Some(rlen), Some(rkind)) = (u16_at(body, o), u16_at(body, o + 2))
                        else {
                            problems.push(format!(".debug$S+{:#x}: truncated symbol", start + o));
                            break;
                        };
                        let rlen = rlen as usize;
                        if (rlen + 2) % 4 != 0 {
                            problems.push(format!(
                                ".debug$S+{:#x}: symbol {rkind:#x} of length {rlen} leaves the next unaligned",
                                start + o
                            ));
                        }
                        let at = start + o;
                        match rkind {
                            S_GPROC32 | S_LPROC32 => {
                                scopes.push(S_END);
                                summary.procedures += 1;
                                symbol_types.extend(u32_at(body, o + 28).map(|t| (t, "S_GPROC32")));
                                reloc_is(
                                    at + 32,
                                    IMAGE_REL_AMD64_SECREL,
                                    "procedure offset",
                                    &mut problems,
                                );
                                reloc_is(
                                    at + 36,
                                    IMAGE_REL_AMD64_SECTION,
                                    "procedure section",
                                    &mut problems,
                                );
                            }
                            // LLVM's: procedures with an id, blocks, thunks, inline sites.
                            0x1147 | 0x1146 => scopes.push(0x114f),
                            0x1103 | 0x1102 => scopes.push(S_END),
                            0x114d => scopes.push(0x114e),
                            S_END | 0x114f | 0x114e => {
                                if scopes.pop() != Some(rkind) {
                                    problems.push(format!(
                                        ".debug$S+{at:#x}: {rkind:#x} closes no open scope"
                                    ));
                                }
                            }
                            S_LOCAL => {
                                summary.locals += 1;
                                symbol_types.extend(u32_at(body, o + 4).map(|t| (t, "S_LOCAL")));
                            }
                            S_UDT => {
                                symbol_types.extend(u32_at(body, o + 4).map(|t| (t, "S_UDT")));
                            }
                            S_DEFRANGE_FRAMEPOINTER_REL => {
                                reloc_is(
                                    at + 8,
                                    IMAGE_REL_AMD64_SECREL,
                                    "range start",
                                    &mut problems,
                                );
                                reloc_is(
                                    at + 12,
                                    IMAGE_REL_AMD64_SECTION,
                                    "range section",
                                    &mut problems,
                                );
                            }
                            _ => {}
                        }
                        o += 2 + rlen;
                    }
                    if !scopes.is_empty() {
                        problems.push(format!(".debug$S+{p:#x}: procedure without S_END"));
                    }
                }
                DEBUG_S_LINES => {
                    reloc_is(start, IMAGE_REL_AMD64_SECREL, "line table offset", &mut problems);
                    reloc_is(
                        start + 4,
                        IMAGE_REL_AMD64_SECTION,
                        "line table section",
                        &mut problems,
                    );
                    let flags = u16_at(body, 6).unwrap_or(0);
                    let mut o = 12;
                    while o < body.len() {
                        let (Some(file), Some(n), Some(size)) =
                            (u32_at(body, o), u32_at(body, o + 4), u32_at(body, o + 8))
                        else {
                            problems
                                .push(format!(".debug$S+{:#x}: truncated line block", start + o));
                            break;
                        };
                        let per_line = if flags & 1 != 0 { 12 } else { 8 };
                        if size as usize != 12 + per_line * n as usize {
                            problems.push(format!(
                                ".debug$S+{:#x}: line block size {size} for {n} lines",
                                start + o
                            ));
                        }
                        line_file_refs.push(file);
                        summary.line_blocks += 1;
                        o += size.max(12) as usize;
                    }
                }
                DEBUG_S_FILECHKSMS => {
                    if body.is_empty() {
                        // link.exe: LNK1103.
                        problems.push(format!(".debug$S+{p:#x}: empty file checksum subsection"));
                    }
                    checksums = Some(body);
                }
                DEBUG_S_STRINGTABLE => strings = Some(body),
                _ => {}
            }
            p = start + len;
            while p % 4 != 0 {
                if d.get(p).is_some_and(|&b| b != 0) {
                    problems.push(format!(".debug$S+{p:#x}: subsection padding not zero"));
                }
                p += 1;
            }
        }
    }

    let mut file_entries: HashSet<u32> = HashSet::new();
    if let Some(checksums) = checksums {
        let mut o = 0;
        while o + 6 <= checksums.len() {
            file_entries.insert(o as u32);
            let name = u32_at(checksums, o).unwrap() as usize;
            let path = strings.and_then(|s| s.get(name..name + cstr_len(s, name)? - 1));
            match path {
                None => problems
                    .push(format!("file checksum entry {o:#x}: name not in the string table")),
                Some(path) => {
                    // A Windows path (not starting with '/', as LLVM tells them apart) with
                    // a '/' in it: debuggers take the file name after the last backslash.
                    if path.first() != Some(&b'/') && path.contains(&b'/') {
                        problems.push(format!(
                            "file {:?}: a Windows path with a '/'",
                            String::from_utf8_lossy(path)
                        ));
                    }
                }
            }
            o += 6 + checksums[o + 4] as usize; // name, checksum size and kind, checksum
            o = (o + 3) & !3;
        }
    } else if !line_file_refs.is_empty() {
        problems.push("line tables without a file checksum subsection".to_owned());
    }
    for f in line_file_refs {
        if !file_entries.contains(&f) {
            problems.push(format!("line block names file entry {f:#x}, which does not exist"));
        }
    }

    // Types the symbols name, and what link.exe keeps: the records the symbols reach.
    let mut reached: HashSet<u32> = HashSet::new();
    let mut stack: Vec<u32> = Vec::new();
    for &(t, what) in &symbol_types {
        if !valid(t) {
            problems.push(format!("{what} names type {t:#x}, past the last type record"));
            continue;
        }
        if let Some(unique) = forward_unique.get(&t) {
            if complete_by_unique.contains_key(unique) {
                // link.exe resolves no forward reference for a symbol: the debugger then
                // shows the type without its fields.
                problems.push(format!(
                    "{what} names the forward reference {t:#x}, not its complete record"
                ));
            }
        }
        stack.push(t);
    }
    while let Some(t) = stack.pop() {
        if t < 0x1000 || !reached.insert(t) {
            continue;
        }
        if let Some(r) = refs.get((t - 0x1000) as usize) {
            stack.extend(r.iter().copied().filter(|&x| valid(x)));
        }
    }
    for &t in &complete_udts {
        if !reached.contains(&t) {
            // link.exe drops type records no symbol reaches (lld keeps them).
            problems
                .push(format!("complete type {t:#x} is reached by no symbol: link.exe drops it"));
        }
    }
    if !found_debug_s && !types.is_empty() {
        problems.push(".debug$T without .debug$S".to_owned());
    }

    if problems.is_empty() { Ok(summary) } else { Err(problems) }
}
