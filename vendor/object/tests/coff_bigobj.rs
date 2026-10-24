//! The COFF writer switches to the big object format when an object has more sections than
//! 16-bit section numbers can name (vendor patch, see README-PATCH.md).

use object::read::{Object as _, ObjectComdat as _, ObjectSection as _, ObjectSymbol as _};
use object::write::{Comdat, Object, Relocation, Symbol, SymbolSection};
use object::{
    Architecture, BinaryFormat, ComdatKind, Endianness, RelocationEncoding, RelocationFlags,
    RelocationKind, SectionKind, SymbolFlags, SymbolKind, SymbolScope,
};

/// An object like a codegen unit with function sections: per function a COMDAT `.text` section
/// with a local leader and a global symbol, and an associated `.pdata` section relocated
/// against it. Returns the written file.
fn write_functions(count: usize) -> Vec<u8> {
    let mut obj = Object::new(BinaryFormat::Coff, Architecture::X86_64, Endianness::Little);
    obj.add_file_symbol(b"a_rather_long_file_name_for_several_aux_records.rs".to_vec());
    let image_offset = RelocationFlags::Generic {
        kind: RelocationKind::ImageOffset,
        encoding: RelocationEncoding::Generic,
        size: 32,
    };
    for i in 0..count {
        let name = format!("function_number_{i}").into_bytes();
        let func = obj.add_symbol(Symbol {
            name: name.clone(),
            value: 0,
            size: 0,
            kind: SymbolKind::Text,
            scope: SymbolScope::Linkage,
            weak: false,
            section: SymbolSection::Undefined,
            flags: SymbolFlags::None,
        });
        let text = obj.add_section(Vec::new(), b".text".to_vec(), SectionKind::Text);
        obj.section_symbol(text);
        let leader = obj.add_symbol(Symbol {
            name,
            value: 0,
            size: 0,
            kind: SymbolKind::Text,
            scope: SymbolScope::Compilation,
            weak: false,
            section: SymbolSection::Section(text),
            flags: SymbolFlags::None,
        });
        obj.add_symbol_data(func, text, &[0xc3, (i & 0xff) as u8], 16);
        let pdata = obj.add_section(Vec::new(), b".pdata".to_vec(), SectionKind::ReadOnlyData);
        obj.section_symbol(pdata);
        obj.section_mut(pdata).set_data(vec![0; 8], 4);
        for offset in [0, 4] {
            obj.add_relocation(
                pdata,
                Relocation { offset, symbol: func, addend: offset as i64, flags: image_offset },
            )
            .unwrap();
        }
        obj.add_comdat(Comdat {
            kind: ComdatKind::NoDuplicates,
            symbol: leader,
            sections: vec![text, pdata],
        });
    }
    // A weak symbol: its auxiliary record is padded to the symbol size too.
    obj.add_symbol(Symbol {
        name: b"weak_one".to_vec(),
        value: 0,
        size: 0,
        kind: SymbolKind::Text,
        scope: SymbolScope::Linkage,
        weak: true,
        section: SymbolSection::Undefined,
        flags: SymbolFlags::None,
    });
    obj.write().unwrap()
}

fn check(count: usize, bigobj: bool) {
    let data = write_functions(count);
    let file = object::File::parse(&*data).unwrap();
    assert_eq!(matches!(file, object::File::CoffBig(_)), bigobj);
    assert_eq!(file.sections().count(), 2 * count);

    let mut functions = 0;
    for symbol in file.symbols() {
        let Ok(name) = symbol.name() else { continue };
        let Some(i) = name.strip_prefix("function_number_") else { continue };
        let i: usize = i.parse().unwrap();
        if !symbol.is_global() {
            continue;
        }
        functions += 1;
        // The function's .text section is the (2i)th section, numbered from 1.
        let section = file.section_by_index(symbol.section_index().unwrap()).unwrap();
        assert_eq!(symbol.section_index().unwrap().0, 2 * i + 1);
        assert_eq!(section.name().unwrap(), ".text");
        assert_eq!(section.data().unwrap(), &[0xc3, (i & 0xff) as u8]);
    }
    assert_eq!(functions, count);

    let mut comdats = 0;
    for comdat in file.comdats() {
        let sections: Vec<_> = comdat.sections().collect();
        assert_eq!(sections.len(), 2, "{:?}", comdat.name());
        let pdata = file.section_by_index(sections[1]).unwrap();
        assert_eq!(pdata.name().unwrap(), ".pdata");
        assert_eq!(pdata.relocations().count(), 2);
        for (_, reloc) in pdata.relocations() {
            let object::RelocationTarget::Symbol(target) = reloc.target() else { panic!() };
            let target = file.symbol_by_index(target).unwrap();
            assert_eq!(target.section_index(), Some(sections[0]));
        }
        comdats += 1;
    }
    assert_eq!(comdats, count);
    assert!(file.symbol_by_name("weak_one").is_some());
    let file_symbol = file.symbols().find(|s| s.kind() == SymbolKind::File).unwrap();
    assert_eq!(file_symbol.name().unwrap(), "a_rather_long_file_name_for_several_aux_records.rs");
}

#[test]
fn small_objects_stay_plain_coff() {
    check(100, false);
    // 65,278 sections: the most a plain COFF object can number.
    check(32_639, false);
}

#[test]
fn objects_with_more_sections_are_bigobj() {
    check(32_640, true);
    check(40_000, true);
}
