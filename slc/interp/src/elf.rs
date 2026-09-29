//! Minimal ELF64 reader (untrusted tooling: symbols and segments).

pub struct Segment {
    pub vaddr: u64,
    pub offset: u64,
    pub filesz: u64,
    pub memsz: u64,
    pub flags: u32,
}

pub struct Symbol {
    pub name: String,
    pub value: u64,
    pub size: u64,
}

pub struct Elf {
    pub data: Vec<u8>,
    pub entry: u64,
    pub segments: Vec<Segment>,
    pub symbols: Vec<Symbol>,
}

fn u16_at(d: &[u8], o: usize) -> Option<u64> {
    Some(u16::from_le_bytes(d.get(o..o + 2)?.try_into().ok()?) as u64)
}
fn u32_at(d: &[u8], o: usize) -> Option<u64> {
    Some(u32::from_le_bytes(d.get(o..o + 4)?.try_into().ok()?) as u64)
}
fn u64_at(d: &[u8], o: usize) -> Option<u64> {
    Some(u64::from_le_bytes(d.get(o..o + 8)?.try_into().ok()?))
}

impl Elf {
    pub fn parse(data: Vec<u8>) -> Result<Elf, String> {
        let bad = || "not a little-endian ELF64 file".to_string();
        if data.get(0..4) != Some(b"\x7fELF") || data.get(4) != Some(&2) || data.get(5) != Some(&1) {
            return Err(bad());
        }
        let entry = u64_at(&data, 0x18).ok_or_else(bad)?;
        let phoff = u64_at(&data, 0x20).ok_or_else(bad)? as usize;
        let shoff = u64_at(&data, 0x28).ok_or_else(bad)? as usize;
        let phentsize = u16_at(&data, 0x36).ok_or_else(bad)? as usize;
        let phnum = u16_at(&data, 0x38).ok_or_else(bad)? as usize;
        let shentsize = u16_at(&data, 0x3a).ok_or_else(bad)? as usize;
        let shnum = u16_at(&data, 0x3c).ok_or_else(bad)? as usize;
        let mut segments = Vec::new();
        for i in 0..phnum {
            let o = phoff + i * phentsize;
            if u32_at(&data, o) == Some(1) {
                segments.push(Segment {
                    flags: u32_at(&data, o + 4).ok_or_else(bad)? as u32,
                    offset: u64_at(&data, o + 8).ok_or_else(bad)?,
                    vaddr: u64_at(&data, o + 0x10).ok_or_else(bad)?,
                    filesz: u64_at(&data, o + 0x20).ok_or_else(bad)?,
                    memsz: u64_at(&data, o + 0x28).ok_or_else(bad)?,
                });
            }
        }
        let mut symbols = Vec::new();
        for i in 0..shnum {
            let o = shoff + i * shentsize;
            if u32_at(&data, o + 4) != Some(2) {
                continue; // SHT_SYMTAB only
            }
            let off = u64_at(&data, o + 0x18).ok_or_else(bad)? as usize;
            let size = u64_at(&data, o + 0x20).ok_or_else(bad)? as usize;
            let link = u32_at(&data, o + 0x28).ok_or_else(bad)? as usize;
            let so = shoff + link * shentsize;
            let stroff = u64_at(&data, so + 0x18).ok_or_else(bad)? as usize;
            for k in 0..size / 24 {
                let e = off + k * 24;
                let name_off = u32_at(&data, e).ok_or_else(bad)? as usize;
                let name_end = data[stroff + name_off..].iter().position(|&c| c == 0).unwrap_or(0);
                let name = String::from_utf8_lossy(&data[stroff + name_off..stroff + name_off + name_end]).to_string();
                symbols.push(Symbol { name, value: u64_at(&data, e + 8).ok_or_else(bad)?, size: u64_at(&data, e + 16).ok_or_else(bad)? });
            }
        }
        Ok(Elf { data, entry, segments, symbols })
    }

    pub fn symbol(&self, name: &str) -> Option<&Symbol> {
        self.symbols.iter().find(|s| s.name == name && s.value != 0)
    }

    /// Symbols whose range contains `addr`.
    pub fn symbol_at(&self, addr: u64) -> Option<&Symbol> {
        self.symbols.iter().filter(|s| s.value <= addr && addr < s.value + s.size.max(1) && !s.name.is_empty()).min_by_key(|s| s.size)
    }

    /// File bytes mapped at `vaddr` (up to `n`, within one segment).
    pub fn bytes_at(&self, vaddr: u64, n: usize) -> Option<&[u8]> {
        for s in &self.segments {
            if s.vaddr <= vaddr && vaddr < s.vaddr + s.filesz {
                let off = (s.offset + vaddr - s.vaddr) as usize;
                let end = (s.offset + s.filesz) as usize;
                return Some(&self.data[off..end.min(off + n)]);
            }
        }
        None
    }
}
