use gimli::write::{Address, Writer};
use gimli::{DW_EH_PE_omit, DW_EH_PE_uleb128, Encoding, LittleEndian};

pub(super) struct GccExceptTable {
    pub call_sites: CallSiteTable,
    pub actions: ActionTable,
    pub type_info: TypeInfoTable,
}

impl GccExceptTable {
    pub(super) fn write<W: Writer>(
        &self,
        w: &mut W,
        encoding: Encoding,
    ) -> gimli::write::Result<()> {
        // lpStartEncoding
        w.write_u8(DW_EH_PE_omit.0)?;
        // lpStart (omitted)
        let type_info_padding = if self.type_info.type_info.is_empty() {
            // ttypeEncoding
            w.write_u8(DW_EH_PE_omit.0)?;
            None
        } else {
            // ttypeEncoding
            w.write_u8(self.type_info.ttype_encoding.0)?;

            // classInfoOffset
            let class_info_offset_field_offset = w.len() as u64;

            // Note: The offset in classInfoOffset is relative to position right after classInfoOffset
            // itself.
            // Each table's size is computed once: the padding search below asks for it up to
            // four times, and a function's call site table can have thousands of entries.
            let call_sites_size = self.call_sites.encoded_size();
            let actions_size = self.actions.encoded_size();
            let class_info_offset_no_padding =
                call_sites_size + actions_size + self.type_info.encoded_size(encoding);

            let type_info_is_aligned = |type_info_padding: u64| {
                (class_info_offset_field_offset
                    + gimli::leb128::write::uleb128_size(
                        class_info_offset_no_padding + type_info_padding,
                    ) as u64
                    + call_sites_size
                    + actions_size
                    + type_info_padding)
                    .is_multiple_of(4)
            };

            let mut type_info_padding = 0;
            while !type_info_is_aligned(type_info_padding) {
                type_info_padding += 1;
            }

            w.write_uleb128(class_info_offset_no_padding + type_info_padding)?;

            Some(type_info_padding)
        };

        // call site table
        self.call_sites.write(w)?;

        // action table
        self.actions.write(w)?;

        // align to 4 bytes
        if let Some(type_info_padding) = type_info_padding {
            for _ in 0..type_info_padding {
                w.write_u8(0)?;
            }
            // In this case we calculated the expected padding amount and used it to write the
            // classInfoOffset field. Assert that the expected value matched the actual value to catch
            // any inconsistency.
            assert!(w.len().is_multiple_of(4), "type_info must be aligned to 4 bytes");
        } else {
            while !w.len().is_multiple_of(4) {
                w.write_u8(0)?;
            }
        }

        // type_info
        self.type_info.write(w, encoding)?;

        // exception specs (unused for rust)

        // align to 4 bytes
        while !w.len().is_multiple_of(4) {
            w.write_u8(0)?;
        }

        Ok(())
    }
}

/// The call-site table and whether its last entry is closed (see [`CallSiteTable::end_run`]).
pub(super) struct CallSiteTable(pub Vec<CallSite>, pub bool);

impl CallSiteTable {
    /// Adds a call site, or extends the last entry over it when that entry has the same landing
    /// pad and action, as LLVM does: one entry per call made the tables of a crate about twice the
    /// size of LLVM's, and the linker keeps every table of the output. Call sites must come in
    /// order of their address, and every call that can unwind must have one: a merged entry also
    /// covers the instructions between its calls, but no other call.
    pub(super) fn push(&mut self, call_site: CallSite) {
        let closed = std::mem::replace(&mut self.1, false);
        if !closed
            && let Some(last) = self.0.last_mut()
            && last.landing_pad == call_site.landing_pad
            && last.action_entry.map(|action| action.0)
                == call_site.action_entry.map(|action| action.0)
            && call_site.start >= last.start + last.length
        {
            last.length = call_site.start + call_site.length - last.start;
            return;
        }
        self.0.push(call_site);
    }

    /// Keeps the next entry from extending the last one: a call between them is left out of
    /// the table on purpose (a personality terminates at a call site it doesn't find).
    pub(super) fn end_run(&mut self) {
        self.1 = true;
    }

    fn table_length(&self) -> u64 {
        self.0.iter().map(|call_site| call_site.encoded_size()).sum()
    }

    fn encoded_size(&self) -> u64 {
        let table_length = self.table_length();
        1 + gimli::leb128::write::uleb128_size(table_length) as u64 + table_length
    }

    fn write<W: Writer>(&self, w: &mut W) -> gimli::write::Result<()> {
        let callsite_table_length = self.table_length();

        // callsiteEncoding
        w.write_u8(DW_EH_PE_uleb128.0)?;
        // callsiteTableLength
        w.write_uleb128(callsite_table_length)?;

        for call_site in &self.0 {
            call_site.write(w)?;
        }

        Ok(())
    }
}

pub(super) struct CallSite {
    pub start: u64,
    pub length: u64,
    pub landing_pad: u64,
    pub action_entry: Option<ActionOffset>,
}

impl CallSite {
    fn encoded_size(&self) -> u64 {
        use gimli::leb128::write::uleb128_size;
        (uleb128_size(self.start)
            + uleb128_size(self.length)
            + uleb128_size(self.landing_pad)
            + uleb128_size(self.action_entry.map_or(0, |action_offset| action_offset.0 + 1)))
            as u64
    }

    fn write<W: Writer>(&self, w: &mut W) -> gimli::write::Result<()> {
        w.write_uleb128(self.start)?;
        w.write_uleb128(self.length)?;
        w.write_uleb128(self.landing_pad)?;
        w.write_uleb128(match self.action_entry {
            Some(action_offset) => action_offset.0 + 1,
            None => 0,
        })?;
        Ok(())
    }
}

pub(super) struct ActionTable {
    actions: Vec<Action>,
    encoded_length: u64,
}

impl ActionTable {
    pub(super) fn new() -> ActionTable {
        ActionTable { actions: vec![], encoded_length: 0 }
    }

    pub(super) fn add(&mut self, action: Action) -> ActionOffset {
        let id = ActionOffset(self.encoded_length);
        self.encoded_length += action.encoded_size(self.encoded_length);
        self.actions.push(action);
        id
    }

    fn encoded_size(&self) -> u64 {
        let mut len = LenWriter(0);
        self.write(&mut len).unwrap();
        len.0 as u64
    }

    fn write<W: Writer>(&self, w: &mut W) -> gimli::write::Result<()> {
        let action_table_start = w.len() as u64;
        for action in &self.actions {
            action.write(w, w.len() as u64 - action_table_start)?;
        }

        Ok(())
    }
}

#[derive(Copy, Clone)]
pub(super) struct ActionOffset(u64);

pub(super) struct Action {
    pub(super) kind: ActionKind,
    pub(super) next_action: Option<ActionOffset>,
}

impl Action {
    fn encoded_size(&self, action_table_offset: u64) -> u64 {
        let mut len = LenWriter(0);
        self.write(&mut len, action_table_offset).unwrap();
        len.0 as u64
    }

    fn write<W: Writer>(&self, w: &mut W, action_table_offset: u64) -> gimli::write::Result<()> {
        // ttypeIndex
        let ttype_index = match self.kind {
            ActionKind::Catch(type_info_id) => type_info_id.0 as i64 + 1,
        };
        w.write_sleb128(ttype_index)?;
        // actionOffset
        let action_offset_field_offset =
            action_table_offset + gimli::leb128::write::sleb128_size(ttype_index) as u64;
        w.write_sleb128(match self.next_action {
            Some(next_action_offset) => {
                next_action_offset.0 as i64 - action_offset_field_offset as i64
            }
            None => 0,
        })?;
        Ok(())
    }
}

#[derive(Copy, Clone)]
pub(super) enum ActionKind {
    Catch(TypeInfoId),
}

pub(super) struct TypeInfoTable {
    ttype_encoding: gimli::DwEhPe,
    type_info: Vec<Address>,
}

impl TypeInfoTable {
    pub(super) fn new(ttype_encoding: gimli::DwEhPe) -> TypeInfoTable {
        TypeInfoTable { ttype_encoding, type_info: vec![] }
    }

    pub(super) fn add(&mut self, type_info: Address) -> TypeInfoId {
        let id = TypeInfoId(self.type_info.len() as u64);
        self.type_info.push(type_info);
        id
    }

    fn encoded_size(&self, encoding: Encoding) -> u64 {
        let mut len = LenWriter(0);
        self.write(&mut len, encoding).unwrap();
        len.0 as u64
    }

    fn write<W: Writer>(&self, w: &mut W, encoding: Encoding) -> gimli::write::Result<()> {
        for &type_info in self.type_info.iter().rev() {
            w.write_eh_pointer(type_info, self.ttype_encoding, encoding.address_size)?;
        }

        Ok(())
    }
}

#[derive(Copy, Clone)]
pub(super) struct TypeInfoId(u64);

struct LenWriter(usize);

impl Writer for LenWriter {
    type Endian = LittleEndian;

    fn endian(&self) -> LittleEndian {
        LittleEndian
    }

    fn len(&self) -> usize {
        self.0
    }

    fn write(&mut self, bytes: &[u8]) -> gimli::write::Result<()> {
        self.0 += bytes.len();
        Ok(())
    }

    fn write_uleb128(&mut self, val: u64) -> gimli::write::Result<()> {
        self.0 += gimli::leb128::write::uleb128_size(val);
        Ok(())
    }

    fn write_sleb128(&mut self, val: i64) -> gimli::write::Result<()> {
        self.0 += gimli::leb128::write::sleb128_size(val);
        Ok(())
    }

    fn write_at(&mut self, offset: usize, bytes: &[u8]) -> gimli::write::Result<()> {
        assert!(offset + bytes.len() < self.0);
        Ok(())
    }
}
