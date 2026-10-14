layer mallocng_specs uses gimple, abi, mallocng

// Specs of mallocng's internal functions on the C world (readable GIMPLE's
// world: memory a partial byte map, `usable` its domain), as contracts
// (layers/abi.sl): a named precondition (`require`: outside it the spec
// allows anything), then a stack overflow or the effect, stated as a
// function of the world. C2 shows the function's readable GIMPLE refines
// its spec (proofs/mallocng_c2.core, proofs/mallocng_bits.core). Each as a
// C function value too (its register wrapper, as readable GIMPLE has C
// functions): what its callers' calls rely on. The wrappers are written as
// the code's are (a result through `result[w]`), so one lemma per shape
// relates the two (proofs/translate_effects.core, `g.fun_*`).

///////////////////////////////////////////////////////////////////////
//  Words

// the 8-byte word at a, as GIMPLE reads it
fn rd64(vm: Vm, a: Addr) -> bits[64] = bits[64](bytes_at(vm, a, 8))

// ... and writes it
fn wr64(vm: Vm, a: Addr, v: bits[64]) -> Vm = vm with { bytes: store_le(vm.bytes, a, 8, uint(v)) }

// the word at p + off: GIMPLE may read and write it (p not null, in the
// address space, usable for reading and writing)
pred word_ok(vm: Vm, objs: Set[nat], p: Addr, off: nat) =
  nonnull: p != 0 && bound: uint(p) + off + 8 <= 2^64 &&
  read: usable(vm, objs, uint(p) + off, 8, false) && write: usable(vm, objs, uint(p) + off, 8, true)

pred al8(p: Addr) = uint(p) % 8 = 0

///////////////////////////////////////////////////////////////////////
//  The active lists: circular, doubly linked through the metas' first two
//  words (struct meta: prev at 0, next at 8)

fn mprev(vm: Vm, m: Addr) -> bits[64] = rd64(vm, m)
fn mnext(vm: Vm, m: Addr) -> bits[64] = rd64(vm, m + 8)

// dequeue's effect as its code has it (`ms.dq_run`; its spec, by its
// purpose: layers/mallocng_purpose.sl's dequeue_purpose).
// dequeue(phead, m): m leaves the list *phead -- its neighbours linked to
// each other (if it has any), the head moved past it, its links cleared.
// The words involved: usable, 8-aligned, and apart (the head pointer, m's
// links, and its neighbours' links to it).
pred dequeue_pre(vm: Vm, objs: Set[nat], phead: Addr, m: Addr) =
  word_ok(vm, objs, phead, 0) && word_ok(vm, objs, m, 0) && word_ok(vm, objs, m, 8) &&
  al8(phead) && al8(m) && uint(phead) != uint(m) && uint(phead) != uint(m) + 8 &&
  (mnext(vm, m) != m ->
     word_ok(vm, objs, mprev(vm, m), 8) && word_ok(vm, objs, mnext(vm, m), 0) &&
     al8(mprev(vm, m)) && al8(mnext(vm, m)) && mprev(vm, m) != m &&
     uint(mprev(vm, m)) + 8 != uint(m) && uint(mnext(vm, m)) != uint(m) + 8 &&
     uint(mprev(vm, m)) + 8 != uint(phead) && uint(mnext(vm, m)) != uint(phead) &&
     uint(mprev(vm, m)) + 8 != uint(mnext(vm, m)))

// (its effect, step by step: m's neighbours linked -- or the list emptied;
// the head moved past m; m's links cleared)
fn dq_links(vm: Vm, phead: Addr, m: Addr) -> Vm =
  if mnext(vm, m) != m { wr64(wr64(vm, mprev(vm, m) + 8, mnext(vm, m)), mnext(vm, m), mprev(vm, m)) } else { wr64(vm, phead, 0) }
fn dq_head(v1: Vm, vm: Vm, phead: Addr, m: Addr) -> Vm =
  if mnext(vm, m) != m && rd64(v1, phead) = m { wr64(v1, phead, mnext(vm, m)) } else { v1 }
fn dequeue_vm(vm: Vm, phead: Addr, m: Addr) -> Vm = wr64(wr64(dq_head(dq_links(vm, phead, m), vm, phead, m), m + 8, 0), m, 0)

// queue's conditions and effect as its code has it (`ms.qu_run`; its spec,
// by its purpose: mallocng_purpose's queue_purpose).
// queue(phead, m): m, unlinked (its links 0 -- else a_crash, a bug),
// joins the list *phead: before its head H (at the circular list's end,
// after H's prev P), or as the list's only element. The words involved:
// usable, 8-aligned, and the ones written apart from those read after.
pred queue_pre(vm: Vm, objs: Set[nat], phead: Addr, m: Addr) =
  word_ok(vm, objs, phead, 0) && word_ok(vm, objs, m, 0) && word_ok(vm, objs, m, 8) && al8(phead) && al8(m) &&
  mnext(vm, m) = 0 && mprev(vm, m) = 0 &&
  (rd64(vm, phead) != 0 ->
     word_ok(vm, objs, rd64(vm, phead), 0) && al8(rd64(vm, phead)) &&
     word_ok(vm, objs, mprev(vm, rd64(vm, phead)), 8) && al8(mprev(vm, rd64(vm, phead))) &&
     uint(rd64(vm, phead)) != uint(m) + 8 && mprev(vm, rd64(vm, phead)) != m)

// (its effect: m between P and H; or m alone, the head)
fn queue_vm(vm: Vm, phead: Addr, m: Addr) -> Vm =
  if rd64(vm, phead) != 0 {
    wr64(wr64(wr64(wr64(vm, m + 8, rd64(vm, phead)), m, mprev(vm, rd64(vm, phead))), mprev(vm, rd64(vm, phead)) + 8, m), rd64(vm, phead), m)
  } else {
    wr64(wr64(wr64(vm, m + 8, m), m, m), phead, m)
  }

// free_meta's first step as its code has it: m's 40 bytes (its struct
// meta) zeroed (its spec, by its purpose: mallocng_purpose's
// free_meta_purpose)
fn zero_meta(vm: Vm, m: Addr) -> Vm = vm with { bytes: store_le(vm.bytes, m, 40, 0) }

///////////////////////////////////////////////////////////////////////
//  Slots

// a byte, a 32-bit word written
fn wr8(vm: Vm, a: Addr, v: nat) -> Vm = vm with { bytes: store_le(vm.bytes, a, 1, v) }
fn wr32(vm: Vm, a: Addr, v: nat) -> Vm = vm with { bytes: store_le(vm.bytes, a, 4, v) }

// set_size's conditions and effect (`ms.ss_run`; its spec by purpose in
// layers/mallocng_purpose.sl). set_size(p, end, n): a slot's n bytes at p, its end at end; the r = end -
// p - n bytes after them reserved, recorded: the header byte at p - 3 keeps
// its low 5 bits, its top 3 the count -- r, or 5 for r >= 5, the count then
// the 32-bit word at end - 4 and a 0 byte before it; the first reserved
// byte (at p + n), if any, 0. The pointers: below 2^63 (their difference
// signed), p past its header; r below 2^31 (an int).
fn reserved(p: Addr, end: Addr, n: bits[64]) -> int = uint(end) - uint(p) - uint(n)

pred set_size_pre(vm: Vm, objs: Set[nat], p: Addr, end: Addr, n: bits[64]) =
  4 <= uint(p) && uint(p) + uint(n) <= uint(end) && uint(end) < 2^63 && reserved(p, end, n) < 2^31 &&
  usable(vm, objs, uint(p) - 3, 1, false) && usable(vm, objs, uint(p) - 3, 1, true) &&
  (reserved(p, end, n) > 0 -> usable(vm, objs, uint(p) + uint(n), 1, true)) &&
  (reserved(p, end, n) >= 5 -> usable(vm, objs, uint(end) - 5, 5, true))

fn set_size_vm(vm: Vm, p: Addr, end: Addr, n: bits[64]) -> Vm {
  let r = reserved(p, end, n)
  let v1 = if r > 0 { wr8(vm, p + n, 0) } else { vm }
  let v2 = if r >= 5 { wr8(wr32(v1, end - 4, r), end - 5, 0) } else { v1 }
  return wr8(v2, p - 3, bytes_at(vm, p - 3, 1) % 32 + 32 * (if r >= 5 { 5 } else { r }))
}

// a_crash (a trap: hlt): calling it is a bug -- its contract undefined, so
// a caller's spec excludes the calls by its precondition
fn a_crash_spec_fun() -> CFun2[World] = (args: Args) => {
  undefined
}

// errno: this libc's, a 4-byte cell in the thread descriptor (musl on
// x86_64: `errno_val`, the thread pointer + 0x34; layers/malloc.sl's
// errno_offset). Not the kernel's: library code writes it (a syscall
// wrapper on failure, size_overflows on a size too large).
fn errno_at(fs: Addr) -> Addr = fs + 0x34

// ___errno_location(): errno's address (the thread pointer's), nothing
// changed
proc[World] errno_location_spec() -> Addr {
  either { overflow() } or { return errno_at(fs_base) }
}

fn errno_location_spec_fun() -> CFun2[World] = (args: Args) => {
  let r = errno_location_spec()
  let w = result[64](r)
  return (w, any bits[64])
}

// size_overflows(n): a size beyond the allocator's (n > 2^63 - 4098):
// errno ENOMEM (12), 1; else 0. Errno's cell writable then, the thread
// pointer sound (the call to ___errno_location).
pred size_overflows_pre(vm: Vm, objs: Set[nat], fs: Addr, n: bits[64]) =
  uint(n) > 0x7fffffffffffeffe -> uint(fs) + 0x38 <= 2^64 && usable(vm, objs, uint(errno_at(fs)), 4, true) && thread_ok(vm, fs)

proc[World] size_overflows_spec(n: bits[64]) -> bits[32] {
  require size_overflows_pre(vm, objs, fs_base, n)
  either { overflow() } or {
    if uint(n) > 0x7fffffffffffeffe {
      vm := wr32(vm, errno_at(fs_base), 12)
      return 1
    }
    return 0
  }
}

fn size_overflows_spec_fun() -> CFun2[World] = (args: Args) => {
  require len(args) >= 1
  let r = size_overflows_spec(bits[64](args[0]))
  let w = result[32](r)
  return (w, any bits[64])
}

// a_cas(p, t, s): the 4-byte word at p, s written if it holds t; its old
// value returned (a locked compare-and-swap: one thread, so one step). The
// word usable for reading and writing: the instruction writes it either
// way (its old value back when it is not t).
pred a_cas_pre(vm: Vm, objs: Set[nat], p: Addr) =
  p != 0 && uint(p) + 4 <= 2^64 && usable(vm, objs, uint(p), 4, false) && usable(vm, objs, uint(p), 4, true)

proc[World] a_cas_spec(p: bits[64], t: bits[32], s: bits[32]) -> bits[32] {
  require a_cas_pre(vm, objs, p)
  either { overflow() } or {
    let old = bytes_at(vm, p, 4)
    vm := wr32(vm, p, if old = uint(t) { uint(s) } else { old })
    return bits[32](old)
  }
}

fn a_cas_spec_fun() -> CFun2[World] = (args: Args) => {
  require len(args) >= 3
  let r = a_cas_spec(bits[64](args[0]), bits[32](args[1]), bits[32](args[2]))
  let w = result[32](r)
  return (w, any bits[64])
}

///////////////////////////////////////////////////////////////////////
//  Read-only tables: a function reading one requires its bytes in the
//  world to be the program's (callers show it from the loaded program)

// n-byte entries, little-endian, at t: the list's
pred table_ok(vm: Vm, objs: Set[nat], t: Addr, n: nat, tab: List[nat]) =
  all i: nat. i < len(tab) ->
    usable(vm, objs, uint(t) + n * i, n, false) && bytes_at(vm, bits[64](uint(t) + n * i), n) = tab[i]

// malloc.c's debruijn32 (a_ctz_32's, at a de Bruijn sequence's positions)
const debruijn32_tab : List[nat] = [
  0, 1, 23, 2, 29, 24, 19, 3, 30, 27, 25, 11, 20, 8, 4, 13,
  31, 22, 28, 18, 26, 10, 7, 12, 21, 17, 9, 6, 16, 5, 15, 14]

///////////////////////////////////////////////////////////////////////
//  Bit counts (C2: proofs/mallocng_bits.core); their callers' C2 use
//  these contracts.

// a_ctz_32(x): x's trailing zeros (x not 0); tbl: debruijn32's address
proc[World] a_ctz_32_spec(tbl: bits[64], x: bits[32]) -> bits[32] {
  require x != 0 && table_ok(vm, objs, tbl, 1, debruijn32_tab)
  either { overflow() } or { return bits[32](tz(uint(x))) }
}

fn a_ctz_32_spec_fun(tbl: bits[64]) -> CFun2[World] = (args: Args) => {
  require len(args) >= 1
  let r = a_ctz_32_spec(tbl, bits[32](args[0]))
  let w = result[32](r)
  return (w, any bits[64])
}

// a_clz_32(x): x's leading zeros r (x not 0): 2^(31 - r) <= x < 2^(32 - r)
// (it calls a_ctz_32: the thread pointer valid)
pred clz_of(x: nat, r: nat) = r < 32 && 2^(31 - r) <= x && x < 2^(32 - r)

proc[World] a_clz_32_spec(tbl: bits[64], x: bits[32]) -> bits[32] {
  require x != 0 && table_ok(vm, objs, tbl, 1, debruijn32_tab) && thread_ok(vm, fs_base)
  either { overflow() } or { return any r: bits[32] where clz_of(uint(x), uint(r)) }
}

fn a_clz_32_spec_fun(tbl: bits[64]) -> CFun2[World] = (args: Args) => {
  require len(args) >= 1
  let r = a_clz_32_spec(tbl, bits[32](args[0]))
  let w = result[32](r)
  return (w, any bits[64])
}

///////////////////////////////////////////////////////////////////////
//  Size classes

// size_to_class(n): the least size class whose slots hold n bytes and the
// slot's 4-byte header (in 16-byte units: size_classes[c] >= (n + 4) / 16,
// rounded up), for n up to the largest class (131052 bytes); sct, tbl:
// the tables' addresses (and the thread pointer, for its call)
pred class_of(n: nat, c: nat) =
  c < 48 && (n + 19) / 16 <= size_classes[c] && (all j: nat. j < c -> size_classes[j] < (n + 19) / 16)

proc[World] size_to_class_spec(sct: bits[64], tbl: bits[64], n: bits[64]) -> bits[32] {
  require uint(n) <= 131052 && table_ok(vm, objs, sct, 2, size_classes) && table_ok(vm, objs, tbl, 1, debruijn32_tab) && thread_ok(vm, fs_base)
  either { overflow() } or { return any c: bits[32] where class_of(uint(n), uint(c)) }
}

fn size_to_class_spec_fun(sct: bits[64], tbl: bits[64]) -> CFun2[World] = (args: Args) => {
  require len(args) >= 1
  let r = size_to_class_spec(sct, tbl, bits[64](args[0]))
  let w = result[32](r)
  return (w, any bits[64])
}

///////////////////////////////////////////////////////////////////////
//  A group's slots

// struct meta's bitfield word at g + 32: last_idx (bits 0-4), freeable (5),
// sizeclass (6-11), maplen (12-63)
fn mword(vm: Vm, g: Addr) -> nat = bytes_at(vm, g + 32, 8)

// a group of one slot in a mapping of its own (last_idx 0, maplen not 0)
pred mapped_single(vm: Vm, g: Addr) = mword(vm, g) % 32 = 0 && mword(vm, g) / 4096 != 0

// get_stride's conditions and effect (`ms.gs_run`; its spec by purpose in
// layers/mallocng_purpose.sl). get_stride(g): the slot size of g's group (mallocng's `stride` of the
// meta at g): its mapping less the group's header (a unit) for a group of
// one slot mapped on its own, else a unit times its size class's entry
// (the class one of the 48); sct: the class table's address
pred get_stride_pre(vm: Vm, objs: Set[nat], sct: Addr, g: Addr) =
  g != 0 && uint(g) + 40 <= 2^64 && usable(vm, objs, uint(g) + 32, 8, false) &&
  (!mapped_single(vm, g) -> mword(vm, g) / 64 % 64 < 48 && table_ok(vm, objs, sct, 2, size_classes))

fn stride_w(vm: Vm, g: Addr) -> nat =
  if mapped_single(vm, g) { mword(vm, g) / 4096 * 4096 - UNIT } else { UNIT * size_classes[mword(vm, g) / 64 % 64] }

// a 16-bit word written
fn wr16(vm: Vm, a: Addr, v: nat) -> Vm = vm with { bytes: store_le(vm.bytes, a, 2, v) }

// the start of slot idx of the group of meta g (its storage a unit past the
// group's header, at the meta's mem word)
fn eslot(vm: Vm, g: Addr, idx: bits[32]) -> nat = uint(rd64(vm, g + 16)) + UNIT + stride_w(vm, g) * uint(idx)

// enframe's conditions and effect (`ms.ef_run`; its spec by purpose in
// layers/mallocng_purpose.sl). enframe(g, idx, n, ctr): slot idx of g's group framed for n bytes at some
// p (mallocng's frame_ok): 16-byte aligned from the slot's start, the n
// bytes before the slot's end (IB bytes short of the next slot). The code's
// p is an offset cycled from the slot's previous one (or ctr) and reduced
// to fit; any such p meets the spec. The frame: past the slot's start, the
// slot's header records the offset (in units, tag 7 << 5) and p's check
// byte is 0; p's header its offset from the storage (in units) and idx;
// then set_size's reserved count. The whole slot, its header included, is
// usable, apart from the meta's mem word (read again after the writes) and
// the thread pointer's word (sound for the calls), and past null; its check
// byte is 0 (else the code traps).
pred enframe_pre(vm: Vm, objs: Set[nat], fs: Addr, sct: Addr, g: Addr, idx: bits[32], n: bits[64]) =
  get_stride_pre(vm, objs, sct, g) && usable(vm, objs, uint(g) + 16, 8, false) &&
  uint(idx) < 2^31 && uint(n) + IB <= stride_w(vm, g) && stride_w(vm, g) < 2^31 &&
  IB < eslot(vm, g, idx) && eslot(vm, g, idx) + stride_w(vm, g) < 2^63 &&
  (uint(g) + 24 <= eslot(vm, g, idx) - IB || eslot(vm, g, idx) - IB + stride_w(vm, g) <= uint(g) + 16) &&
  (uint(fs) + 8 <= eslot(vm, g, idx) - IB || eslot(vm, g, idx) - IB + stride_w(vm, g) <= uint(fs)) &&
  usable(vm, objs, eslot(vm, g, idx) - IB, stride_w(vm, g), false) &&
  usable(vm, objs, eslot(vm, g, idx) - IB, stride_w(vm, g), true) &&
  bytes_at(vm, bits[64](eslot(vm, g, idx) - IB), 1) = 0 && thread_ok(vm, fs)

pred enframe_at(vm: Vm, g: Addr, idx: bits[32], n: bits[64], p: nat) =
  eslot(vm, g, idx) <= p && (p - eslot(vm, g, idx)) % UNIT = 0 && p + uint(n) + IB <= eslot(vm, g, idx) + stride_w(vm, g)

// enframe's header writes before its set_size call: the slot's offset
// record (past its start), p's offset from the storage and its index
fn enframe_hdr(vm: Vm, g: Addr, idx: bits[32], p: Addr) -> Vm {
  let s = eslot(vm, g, idx)
  let v1 = if uint(p) > s { wr8(wr8(wr16(vm, bits[64](s - 2), (uint(p) - s) / UNIT), bits[64](s - 3), 7 * 32), p - 4, 0) } else { vm }
  return wr8(wr16(v1, p - 2, (uint(p) - (uint(rd64(vm, g + 16)) + UNIT)) / UNIT % 2^16), p - 3, uint(idx) % 256)
}

// the slot's end, set_size's `end`
fn eend(vm: Vm, g: Addr, idx: bits[32]) -> bits[64] = bits[64](eslot(vm, g, idx) + stride_w(vm, g) - IB)

// get_meta's effect (proofs/mallocng_slots.core's `ms.gm_run`; its spec
// by purpose in layers/mallocng_purpose.sl): the meta of p's group. p's
// offset from the group's storage,
// in units: the 16-bit word at p - 2, or the 32-bit one at p - 8 when the
// byte at p - 4 is set; the group's header a unit before the storage, its
// first word the meta.
fn gm_off(vm: Vm, p: Addr) -> nat =
  if bytes_at(vm, p - 4, 1) != 0 { bytes_at(vm, p - 8, 4) } else { bytes_at(vm, p - 2, 2) }
fn gm_base(vm: Vm, p: Addr) -> nat = uint(p) - UNIT * gm_off(vm, p) - UNIT
fn gm_meta(vm: Vm, p: Addr) -> bits[64] = rd64(vm, bits[64](gm_base(vm, p)))
fn gm_idx(vm: Vm, p: Addr) -> nat = bytes_at(vm, p - 3, 1) % 32

// malloc's checks there (a failed one: a_crash, undefined -- excluded
// here): p 16-byte aligned, its 4 header bytes usable; a 32-bit offset
// (at p - 8, usable then) past 16 bits (the 16-bit one then 0), small enough for the code's
// 32-bit product with a unit; the header within the address space, its
// meta's mem word, mask words and bitfield word usable, the mem word the
// header; p's index (get_slot_index's) within the group's last, its slot
// neither available nor freed; the meta's page's first word (its meta
// area's check) the context's secret (its first word); the offset within
// slot idx for a size class (else the class 63), within the mapping when
// there is one (maplen); the thread pointer sound for the call.
pred get_meta_pre(vm: Vm, objs: Set[nat], fs: Addr, ctx: Addr, sct: Addr, p: Addr) =
  uint(p) % 16 = 0 && 16 <= uint(p) && usable(vm, objs, uint(p) - 4, 4, false) &&
  (bytes_at(vm, p - 4, 1) != 0 -> usable(vm, objs, uint(p) - 8, 4, false) &&
     bytes_at(vm, p - 2, 2) = 0 && 65535 < bytes_at(vm, p - 8, 4) && bytes_at(vm, p - 8, 4) < 2^27) &&
  UNIT * gm_off(vm, p) + UNIT < uint(p) && usable(vm, objs, gm_base(vm, p), 8, false) &&
  gm_meta(vm, p) != 0 && uint(gm_meta(vm, p)) + 40 <= 2^64 && usable(vm, objs, uint(gm_meta(vm, p)) + 16, 24, false) &&
  uint(rd64(vm, gm_meta(vm, p) + 16)) = gm_base(vm, p) &&
  gm_idx(vm, p) <= mword(vm, gm_meta(vm, p)) % 32 &&
  bytes_at(vm, gm_meta(vm, p) + 24, 4) / 2^gm_idx(vm, p) % 2 = 0 &&
  bytes_at(vm, gm_meta(vm, p) + 28, 4) / 2^gm_idx(vm, p) % 2 = 0 &&
  uint(gm_meta(vm, p)) / 4096 * 4096 != 0 && usable(vm, objs, uint(gm_meta(vm, p)) / 4096 * 4096, 8, false) &&
  ctx != 0 && uint(ctx) + 8 <= 2^64 && usable(vm, objs, uint(ctx), 8, false) &&
  rd64(vm, bits[64](uint(gm_meta(vm, p)) / 4096 * 4096)) = rd64(vm, ctx) &&
  (mword(vm, gm_meta(vm, p)) / 64 % 64 < 48 ->
     table_ok(vm, objs, sct, 2, size_classes) &&
     size_classes[mword(vm, gm_meta(vm, p)) / 64 % 64] * gm_idx(vm, p) <= gm_off(vm, p) &&
     gm_off(vm, p) < size_classes[mword(vm, gm_meta(vm, p)) / 64 % 64] * (gm_idx(vm, p) + 1)) &&
  (48 <= mword(vm, gm_meta(vm, p)) / 64 % 64 -> mword(vm, gm_meta(vm, p)) / 64 % 64 = 63) &&
  (mword(vm, gm_meta(vm, p)) / 4096 != 0 -> gm_off(vm, p) < mword(vm, gm_meta(vm, p)) / 4096 * 256) &&
  thread_ok(vm, fs)

// activate_group's effect (`ms.ag_run`; its spec by purpose in
// layers/mallocng_purpose.sl): the slots of m's group up to its active
// index idx (act: the low idx + 1 bits; idx the low 5 bits of the byte at
// the group's header + 8, the header at m's mem word) leave the freed mask
// and become the available one (0 before: else a_crash). The masks at
// m + 24 (available) and m + 28 (freed), the mem word at m + 16; the freed
// mask changed by a_cas (one thread: in one step), the thread pointer
// sound for that call.
fn ag_act(vm: Vm, m: Addr) -> bits[32] = bits[32](2 * 2^(bytes_at(vm, rd64(vm, m + 16) + 8, 1) % 32) - 1)
fn ag_freed(vm: Vm, m: Addr) -> bits[32] = bits[32](bytes_at(vm, m + 28, 4))

pred activate_group_pre(vm: Vm, objs: Set[nat], fs: Addr, m: Addr) =
  m != 0 && uint(m) + 32 <= 2^64 && usable(vm, objs, uint(m) + 16, 16, false) && usable(vm, objs, uint(m) + 24, 8, true) &&
  bytes_at(vm, m + 24, 4) = 0 &&
  rd64(vm, m + 16) != 0 && uint(rd64(vm, m + 16)) + 9 <= 2^64 && usable(vm, objs, uint(rd64(vm, m + 16)) + 8, 1, false) &&
  thread_ok(vm, fs)

fn activate_group_vm(vm: Vm, m: Addr) -> Vm =
  wr32(wr32(vm, m + 28, uint(ag_freed(vm, m) & ~ag_act(vm, m))), m + 24, uint(ag_freed(vm, m) & ag_act(vm, m)))

// __malloc_allzerop's effect (`ms.az_run`; its spec by purpose in
// layers/mallocng_purpose.sl): whether p's slot is known zero-filled
// (calloc then skips zeroing it): its group without a size class (63:
// mapped on its own), or its stride below its class's (a group of one slot
// mapped on its own).
pred allzero(vm: Vm, m: Addr) =
  48 <= mword(vm, m) / 64 % 64 || stride_w(vm, m) < UNIT * size_classes[mword(vm, m) / 64 % 64]

///////////////////////////////////////////////////////////////////////
//  The malloc context's counters (struct malloc_context at ctx: the
//  classes' unmap sequence bytes at ctx + 848, their bounce counters at
//  ctx + 880, both for the size classes 7 .. 38, and the sequence byte at
//  ctx + 912); the lock word

// size class sc's bounce counter: for sc 7 .. 38
pred bouncing_class(sc: bits[32]) = 7 <= uint(sc) && uint(sc) <= 38
fn bounce_at(ctx: Addr, sc: bits[32]) -> Addr = bits[64](uint(ctx) + 880 + uint(sc) - 7)

// (its byte usable: for reading, and for writing if w)
pred bounce_pre(vm: Vm, objs: Set[nat], ctx: Addr, sc: bits[32], w: bool) =
  ctx != 0 && uint(ctx) + 913 <= 2^64 &&
  (bouncing_class(sc) -> usable(vm, objs, uint(bounce_at(ctx, sc)), 1, false) && (w -> usable(vm, objs, uint(bounce_at(ctx, sc)), 1, true)))

// is_bouncing(sc): whether sc's counter is above 99 (no counter: not)
proc[World] is_bouncing_spec(ctx: bits[64], sc: bits[32]) -> bits[32] {
  require bounce_pre(vm, objs, ctx, sc, false)
  either { overflow() } or { return if bouncing_class(sc) && bytes_at(vm, bounce_at(ctx, sc), 1) > 99 { 1 } else { 0 } }
}

fn is_bouncing_spec_fun(ctx: bits[64]) -> CFun2[World] = (args: Args) => {
  require len(args) >= 1
  let r = is_bouncing_spec(ctx, bits[32](args[0]))
  let w = result[32](r)
  return (w, any bits[64])
}

// decay_bounces(sc): sc's counter, if not 0, less 1
fn decay_vm(vm: Vm, ctx: Addr, sc: bits[32]) -> Vm =
  if bouncing_class(sc) && bytes_at(vm, bounce_at(ctx, sc), 1) != 0 {
    wr8(vm, bounce_at(ctx, sc), bytes_at(vm, bounce_at(ctx, sc), 1) - 1)
  } else { vm }

proc[World] decay_bounces_spec(ctx: bits[64], sc: bits[32]) {
  require bounce_pre(vm, objs, ctx, sc, true)
  either { overflow() } or { vm := decay_vm(vm, ctx, sc) }
}

fn decay_bounces_spec_fun(ctx: bits[64]) -> CFun2[World] = (args: Args) => {
  require len(args) >= 1
  decay_bounces_spec(ctx, bits[32](args[0]))
  return (any bits[64], any bits[64])
}

fn seq_at(ctx: Addr) -> Addr = ctx + 912
fn unmap_seqs_at(ctx: Addr) -> Addr = ctx + 848

// account_bounce(sc): a size class unmapped lately (its unmap sequence
// byte set, the sequence at most 9 past it) bounced once more: its counter
// up by 1 below 99, else 150. The bytes: usable (the counter for writing).
fn unmap_seq_at(ctx: Addr, sc: bits[32]) -> Addr = bits[64](uint(ctx) + 848 + uint(sc) - 7)

pred account_bounce_pre(vm: Vm, objs: Set[nat], ctx: Addr, sc: bits[32]) =
  bounce_pre(vm, objs, ctx, sc, true) &&
  (bouncing_class(sc) -> usable(vm, objs, uint(unmap_seq_at(ctx, sc)), 1, false) && usable(vm, objs, uint(ctx) + 912, 1, false))

pred bounced(vm: Vm, ctx: Addr, sc: bits[32]) =
  bouncing_class(sc) && bytes_at(vm, unmap_seq_at(ctx, sc), 1) != 0 && bytes_at(vm, seq_at(ctx), 1) <= bytes_at(vm, unmap_seq_at(ctx, sc), 1) + 9

proc[World] account_bounce_spec(ctx: bits[64], sc: bits[32]) {
  require account_bounce_pre(vm, objs, ctx, sc)
  either { overflow() } or {
    if bounced(vm, ctx, sc) {
      let b = bytes_at(vm, bounce_at(ctx, sc), 1)
      vm := wr8(vm, bounce_at(ctx, sc), if b <= 98 { b + 1 } else { 150 })
    }
  }
}

fn account_bounce_spec_fun(ctx: bits[64]) -> CFun2[World] = (args: Args) => {
  require len(args) >= 1
  account_bounce_spec(ctx, bits[32](args[0]))
  return (any bits[64], any bits[64])
}

// step_seq(): the sequence byte counted up -- at 255, the unmap sequence
// bytes zeroed and the count restarted at 1

pred step_seq_pre(vm: Vm, objs: Set[nat], ctx: Addr) =
  ctx != 0 && uint(ctx) + 913 <= 2^64 &&
  usable(vm, objs, uint(ctx) + 912, 1, false) && usable(vm, objs, uint(ctx) + 912, 1, true) &&
  (bytes_at(vm, seq_at(ctx), 1) = 255 -> usable(vm, objs, uint(ctx) + 848, 32, true))

fn step_seq_vm(vm: Vm, ctx: Addr) -> Vm =
  if bytes_at(vm, seq_at(ctx), 1) != 255 { wr8(vm, seq_at(ctx), bytes_at(vm, seq_at(ctx), 1) + 1) }
  else { wr8(vm with { bytes: store_le(vm.bytes, unmap_seqs_at(ctx), 32, 0) }, seq_at(ctx), 1) }

proc[World] step_seq_spec(ctx: bits[64]) {
  require step_seq_pre(vm, objs, ctx)
  either { overflow() } or { vm := step_seq_vm(vm, ctx) }
}

fn step_seq_spec_fun(ctx: bits[64]) -> CFun2[World] = (args: Args) => {
  step_seq_spec(ctx)
  return (any bits[64], any bits[64])
}

// resetlock(): the lock word (at lk) 0
pred resetlock_pre(vm: Vm, objs: Set[nat], lk: Addr) = lk != 0 && uint(lk) + 4 <= 2^64 && usable(vm, objs, uint(lk), 4, true)

proc[World] resetlock_spec(lk: bits[64]) {
  require resetlock_pre(vm, objs, lk)
  either { overflow() } or { vm := wr32(vm, lk, 0) }
}

fn resetlock_spec_fun(lk: bits[64]) -> CFun2[World] = (args: Args) => {
  resetlock_spec(lk)
  return (any bits[64], any bits[64])
}

// upgradelock(): nothing (single-threaded)
proc[World] upgradelock_spec() {
  either { overflow() } or { vm := vm }
}

fn upgradelock_spec_fun() -> CFun2[World] = (args: Args) => {
  upgradelock_spec()
  return (any bits[64], any bits[64])
}
