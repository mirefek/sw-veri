//! Types from DWARF debug info, read from `readelf --debug-dump=info`
//! output: struct layouts (member offsets, bitfields), arrays, typedefs,
//! and the declared types of variables and functions.

use std::collections::HashMap;

#[derive(Clone, Debug)]
pub enum DType {
    Base { name: String, size: u64, signed: bool },
    Pointer { to: Option<u64> },
    Struct { size: u64, members: Vec<Member> },
    Array { elem: u64, dims: Vec<u64> },
    Typedef { to: Option<u64> },
    Qual { to: Option<u64> }, // const, volatile, restrict, atomic
    Enum { size: u64 },
    Func,
    Void,
}

#[derive(Clone, Debug)]
pub struct Member {
    pub name: String,
    /// offset of the first bit from the start of the struct
    pub bit_off: u64,
    /// Some(n): a bitfield of n bits
    pub bit_size: Option<u64>,
    pub ty: u64,
}

#[derive(Default)]
pub struct Dwarf {
    pub dies: HashMap<u64, DType>,
    /// struct / union tags
    pub structs: HashMap<String, u64>,
    pub typedefs: HashMap<String, u64>,
    pub bases: HashMap<String, u64>,
    /// variables and functions: name -> type (functions: return type) ...
    pub vars: HashMap<String, u64>,
    /// ... and parameter types of functions
    pub params: HashMap<String, Vec<u64>>,
}

struct Die {
    depth: u32,
    off: u64,
    tag: String,
    attrs: HashMap<String, String>,
    children: Vec<usize>,
}

/// the value without readelf's form annotations: `(data1) 40` -> `40`,
/// `(strp) (offset: 0xdc): meta` -> `meta`
fn value(v: &str) -> &str {
    let mut v = v.trim();
    while v.starts_with('(') {
        match v.find(')') {
            Some(i) if !v[1..i].contains(' ') => v = v[i + 1..].trim_start(),
            _ => break,
        }
    }
    match v.find("): ") {
        Some(i) if v.starts_with('(') => v[i + 3..].trim(),
        _ => v,
    }
}

fn attr_ref(v: &str) -> Option<u64> {
    let i = v.find("<0x")?;
    let j = v[i..].find('>')? + i;
    u64::from_str_radix(&v[i + 3..j], 16).ok()
}

fn attr_num(v: &str) -> Option<u64> {
    let t = v.split_whitespace().next()?;
    if let Some(h) = t.strip_prefix("0x") {
        u64::from_str_radix(h, 16).ok()
    } else {
        t.parse().ok()
    }
}

fn attr_name(v: &str) -> String {
    // "(indirect string, offset: 0xe2): meta" or "pad"
    match v.rfind("): ") {
        Some(i) if v.starts_with('(') => v[i + 3..].trim().to_string(),
        _ => v.trim().to_string(),
    }
}

impl Dwarf {
    pub fn from_object(obj: &str) -> Result<Dwarf, String> {
        let out = std::process::Command::new("readelf")
            .args(["--debug-dump=info", "-W", obj])
            .output()
            .map_err(|e| format!("readelf: {}", e))?;
        if !out.status.success() {
            return Err(format!("readelf failed on {}", obj));
        }
        Ok(Dwarf::parse(&String::from_utf8_lossy(&out.stdout)))
    }

    pub fn parse(text: &str) -> Dwarf {
        let mut dies: Vec<Die> = Vec::new();
        let mut stack: Vec<(u32, usize)> = Vec::new();
        for line in text.lines() {
            let l = line.trim_start();
            if l.starts_with('<') && l.contains("Abbrev Number:") {
                // " <1><2c0>: Abbrev Number: 24 (DW_TAG_structure_type)"
                let depth: u32 = l[1..l.find('>').unwrap_or(1)].parse().unwrap_or(0);
                let rest = &l[l.find('>').unwrap_or(0) + 1..];
                let off = rest.get(1..rest.find('>').unwrap_or(1)).and_then(|h| u64::from_str_radix(h, 16).ok()).unwrap_or(0);
                let Some(t0) = l.find("(DW_TAG_") else {
                    continue; // end of children
                };
                let tag = l[t0 + 1..l.len() - 1].to_string();
                while stack.last().map_or(false, |&(d, _)| d >= depth) {
                    stack.pop();
                }
                let idx = dies.len();
                if let Some(&(_, p)) = stack.last() {
                    dies[p].children.push(idx);
                }
                dies.push(Die { depth, off, tag, attrs: HashMap::new(), children: Vec::new() });
                stack.push((depth, idx));
            } else if let Some(i) = l.find("DW_AT_") {
                if let (Some(d), Some(c)) = (dies.last_mut(), l[i..].find(':')) {
                    let name = l[i..i + c].trim().to_string();
                    let val = value(&l[i + c + 1..]).to_string();
                    d.attrs.insert(name, val);
                }
            }
        }
        let mut dw = Dwarf::default();
        for d in &dies {
            let a = |k: &str| d.attrs.get(k).map(|s| s.as_str());
            let name = a("DW_AT_name").map(attr_name).unwrap_or_default();
            let to = a("DW_AT_type").and_then(attr_ref);
            let size = a("DW_AT_byte_size").and_then(attr_num).unwrap_or(0);
            let ty = match d.tag.as_str() {
                "DW_TAG_base_type" => {
                    let enc = a("DW_AT_encoding").unwrap_or("");
                    let signed = enc.contains("(signed") && !enc.contains("unsigned");
                    dw.bases.insert(name.clone(), d.off);
                    DType::Base { name: name.clone(), size, signed }
                }
                "DW_TAG_pointer_type" => DType::Pointer { to },
                "DW_TAG_structure_type" | "DW_TAG_union_type" => {
                    let mut members = Vec::new();
                    for &c in &d.children {
                        let m = &dies[c];
                        if m.tag != "DW_TAG_member" {
                            continue;
                        }
                        let ma = |k: &str| m.attrs.get(k).map(|s| s.as_str());
                        let bit_off = match (ma("DW_AT_data_bit_offset"), ma("DW_AT_data_member_location")) {
                            (Some(b), _) => attr_num(b).unwrap_or(0),
                            (None, Some(l)) => 8 * attr_num(l).unwrap_or(0),
                            (None, None) => 0,
                        };
                        members.push(Member {
                            name: ma("DW_AT_name").map(attr_name).unwrap_or_default(),
                            bit_off,
                            bit_size: ma("DW_AT_bit_size").and_then(attr_num),
                            ty: ma("DW_AT_type").and_then(attr_ref).unwrap_or(0),
                        });
                    }
                    if !name.is_empty() && a("DW_AT_declaration").is_none() {
                        dw.structs.insert(name.clone(), d.off);
                    }
                    DType::Struct { size, members }
                }
                "DW_TAG_array_type" => {
                    let dims = d
                        .children
                        .iter()
                        .filter(|&&c| dies[c].tag == "DW_TAG_subrange_type")
                        .map(|&c| {
                            let s = &dies[c].attrs;
                            match (s.get("DW_AT_count"), s.get("DW_AT_upper_bound")) {
                                (Some(n), _) => attr_num(n).unwrap_or(0),
                                (None, Some(u)) => attr_num(u).map(|u| u + 1).unwrap_or(0),
                                _ => 0,
                            }
                        })
                        .collect();
                    DType::Array { elem: to.unwrap_or(0), dims }
                }
                "DW_TAG_typedef" => {
                    dw.typedefs.insert(name.clone(), d.off);
                    DType::Typedef { to }
                }
                "DW_TAG_const_type" | "DW_TAG_volatile_type" | "DW_TAG_restrict_type" | "DW_TAG_atomic_type" => DType::Qual { to },
                "DW_TAG_enumeration_type" => DType::Enum { size },
                "DW_TAG_subroutine_type" => DType::Func,
                "DW_TAG_unspecified_type" => DType::Void,
                "DW_TAG_variable" => {
                    if d.depth == 1 {
                        if let Some(t) = to {
                            dw.vars.entry(name.clone()).or_insert(t);
                        }
                    }
                    continue;
                }
                "DW_TAG_subprogram" => {
                    if let Some(t) = to {
                        dw.vars.entry(name.clone()).or_insert(t);
                    }
                    let ps: Vec<u64> = d
                        .children
                        .iter()
                        .filter(|&&c| dies[c].tag == "DW_TAG_formal_parameter")
                        .filter_map(|&c| dies[c].attrs.get("DW_AT_type").and_then(|v| attr_ref(v)))
                        .collect();
                    dw.params.entry(name.clone()).or_insert(ps);
                    continue;
                }
                _ => continue,
            };
            dw.dies.insert(d.off, ty);
        }
        dw
    }

    /// strips typedefs and qualifiers
    pub fn strip(&self, mut t: u64) -> Option<u64> {
        for _ in 0..64 {
            match self.dies.get(&t)? {
                DType::Typedef { to, .. } | DType::Qual { to } => t = (*to)?,
                _ => return Some(t),
            }
        }
        None
    }

    pub fn get(&self, t: u64) -> Option<&DType> {
        self.dies.get(&self.strip(t)?)
    }

    pub fn size(&self, t: u64) -> Option<u64> {
        match self.get(t)? {
            DType::Base { size, .. } | DType::Struct { size, .. } | DType::Enum { size } => Some(*size),
            DType::Pointer { .. } => Some(8),
            DType::Array { elem, dims } => Some(self.size(*elem)? * dims.iter().product::<u64>()),
            _ => None,
        }
    }
}
