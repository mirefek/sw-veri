//! Decoding with the spec's own instruction table.

use sl_elab::globals::Globals;
use sl_interp::{Interp, V};
use sl_syntax::{collect_files, parse_files, SourceMap};
use std::path::Path;

fn globals() -> Globals {
    let repo = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let paths = collect_files(&[repo.join("spec")]).unwrap();
    let mut sm = SourceMap::default();
    let (files, diags) = parse_files(&mut sm, &paths);
    assert!(diags.is_empty());
    Globals::build(files).unwrap()
}

fn bind<'a>(m: &'a sl_interp::Match, n: &str) -> &'a V {
    &m.binds.iter().find(|b| b.0 == n).unwrap_or_else(|| panic!("no binding {}", n)).1
}

#[test]
fn decodes_common_instructions() {
    let g = globals();
    let it = Interp::new(&g, "x86").unwrap();
    // sub rsp, 0x10
    let m = it.decode(&[0x48, 0x83, 0xec, 0x10]);
    assert_eq!(m.len(), 1);
    assert_eq!(m[0].len, 4);
    assert_eq!(bind(&m[0], "op").num().unwrap(), 5);
    assert_eq!(bind(&m[0], "n").num().unwrap(), 8);
    assert_eq!(bind(&m[0], "rm").render(), "gp(4)");
    // mov eax, [rbp-8]
    let m = it.decode(&[0x8b, 0x45, 0xf8]);
    assert_eq!(m.len(), 1);
    assert_eq!(m[0].len, 3);
    assert_eq!(bind(&m[0], "n").num().unwrap(), 4);
    assert!(bind(&m[0], "rm").render().contains("base(5)"));
    // ret and rep ret
    assert_eq!(it.decode(&[0xc3]).len(), 1);
    assert_eq!(it.decode(&[0xf3, 0xc3]).len(), 1);
    // gcc padding: data16 data16 cs nopw [rax+rax*1+0]
    let m = it.decode(&[0x66, 0x66, 0x2e, 0x0f, 0x1f, 0x84, 0, 0, 0, 0, 0]);
    assert_eq!(m.len(), 1);
    assert_eq!(m[0].len, 11);
}

#[test]
fn unused_rex_bits_are_not_modelled() {
    let g = globals();
    let it = Interp::new(&g, "x86").unwrap();
    assert_eq!(it.decode(&[0x90]).len(), 1); // nop
    assert_eq!(it.decode(&[0x41, 0x90]).len(), 0); // xchg r8, rax: not the nop row
    // push r12 uses REX.B
    let m = it.decode(&[0x41, 0x54]);
    assert_eq!(m.len(), 1);
    assert_eq!(bind(&m[0], "r").num().unwrap(), 12);
}

#[test]
fn rip_relative_and_sib() {
    let g = globals();
    let it = Interp::new(&g, "x86").unwrap();
    // lea rdi, [rip+0x10]
    let m = it.decode(&[0x48, 0x8d, 0x3d, 0x10, 0, 0, 0]);
    assert_eq!(m.len(), 1);
    assert!(bind(&m[0], "rm").render().contains("rip_rel"));
    // mov edx, [r12+rbx*4]
    let m = it.decode(&[0x41, 0x8b, 0x14, 0x9c]);
    assert_eq!(m.len(), 1);
    let rm = bind(&m[0], "rm").render();
    assert!(rm.contains("base(12)") && rm.contains("some(3)") && rm.contains("scale: 4"), "{}", rm);
}

#[test]
fn allocator_instructions() {
    let g = globals();
    let it = Interp::new(&g, "x86").unwrap();
    let one = |b: &[u8]| {
        let m = it.decode(b);
        assert_eq!(m.len(), 1, "{:02x?} should match exactly one row", b);
        assert_eq!(m[0].len, b.len(), "{:02x?}", b);
    };
    one(&[0x66, 0x0f, 0xef, 0xc0]); // pxor xmm0, xmm0
    one(&[0x41, 0x0f, 0x11, 0x43, 0x10]); // movups [r11+0x10], xmm0
    one(&[0x0f, 0x29, 0x04, 0x24]); // movaps [rsp], xmm0
    one(&[0xf3, 0x0f, 0x6f, 0x47, 0xf0]); // movdqu xmm0, [rdi-0x10]
    one(&[0x66, 0x0f, 0x73, 0xd9, 0x08]); // psrldq xmm1, 8
    one(&[0x66, 0x48, 0x0f, 0x7e, 0xc2]); // movq rdx, xmm0
    one(&[0xf3, 0x0f, 0xbc, 0xc0]); // tzcnt eax, eax
    one(&[0x44, 0x0f, 0xa3, 0xc1]); // bt ecx, r8d
    one(&[0x48, 0x98]); // cdqe
    one(&[0x48, 0x69, 0xc1, 0x6d, 0x4e, 0xc6, 0x41]); // imul rax, rcx, imm32
    one(&[0xf0, 0x0f, 0xb1, 0x37]); // lock cmpxchg [rdi], esi
    one(&[0xf0, 0x0f, 0xc1, 0x07]); // lock xadd [rdi], eax
    one(&[0xf0, 0x44, 0x09, 0x47, 0x1c]); // lock or [rdi+0x1c], r8d
    one(&[0xc0, 0xe8, 0x05]); // shr al, 5
    one(&[0xa4]); // movsb
}

#[test]
fn invalid_lock_and_sse_forms_are_not_modelled() {
    let g = globals();
    let it = Interp::new(&g, "x86").unwrap();
    assert!(it.decode(&[0xf0, 0x01, 0xc0]).is_empty()); // lock add eax, eax: #UD
    assert!(it.decode(&[0xf0, 0x39, 0x07]).is_empty()); // lock cmp: #UD
    assert!(it.decode(&[0xf0, 0x90]).is_empty()); // lock nop: #UD
    assert!(it.decode(&[0x0f, 0xef, 0xc0]).is_empty()); // pxor mm0, mm0 (MMX): not modelled
}
