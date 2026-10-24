layer mallocng uses malloc

// The allocator invariant of musl's mallocng (musl 1.2.6,
// src/malloc/mallocng), x86_64, single-threaded: `alloc_inv` and
// `alloc_owned` of the malloc layer for a given binary.
//
// Design:
//
// * An abstract state `Abs` records what the invariant is about: the ctx
//   fields that matter, the meta areas, the metas in use with their field
//   values, the free-meta list, the active lists, and what each slot of
//   each group holds (nothing, a client block, or a nested group).
// * `footprint(c, A, blocks)` -- the bytes the allocator owns -- is computed
//   from `A` (and the live blocks, which it excludes) alone.
// * `holds(c, A, m, blocks, brk)` states that memory, seen only through
//   `m = mview(vm, held)` -- the footprint but the context's free bytes,
//   musl's counters and heuristics (`ctx_free`) -- agrees with `A`, and
//   that `A` satisfies mallocng's structural invariants.
// * `inv(c)`: some `A` holds; `owned(c)`: its footprint.
//
// Because the invariant reads memory only through the view, it depends only
// on the owned bytes and their pages (the `frame` law), provided `A` is
// determined by the memory (`abs_unique`, a lemma to prove).
//
// Deliberately weak: only what mallocng's code relies on, not what it
// happens to maintain (heuristic counters, zeroed free metas, which groups
// sit on active lists, ...). Strengthened when the function proofs need it.

///////////////////////////////////////////////////////////////////////
//  The binary

record Cfg {
  file : File     // the executable
  ctx  : nat      // __malloc_context
  lock : nat      // __malloc_lock
  libc : nat      // __libc
  sct  : nat      // __malloc_size_classes (read-only)
  dbj  : nat      // a_ctz_32's debruijn32 (read-only)
  scnt : nat      // alloc_group's small_cnt_tab (read-only)
  mcnt : nat      // alloc_group's med_cnt_tab (read-only)
}

///////////////////////////////////////////////////////////////////////
//  Memory as the invariant sees it

type Mem = nat -> Option[(bits[8], Option[Page])]

// the bytes and pages of `fp`; nothing elsewhere
fn mview(vm: Vm, fp: Set[nat]) -> Mem =
  (a: nat) => if a in fp { some((vm.bytes[bits[64](a)], vm.pages[a / PAGE])) } else { none }

fn b8(m: Mem, a: nat) -> nat = uint(m[a].value[0])

// little-endian unsigned, n bytes
fn rd(m: Mem, a: nat, n: nat) -> nat = sum i in 0..n. b8(m, a + i) * 256^i

fn pg(m: Mem, a: nat) -> Option[Page] = m[a].value[1]

pred m_mapped(m: Mem, a: nat) = a / PAGE < TASK_SIZE / PAGE && pg(m, a) != none
pred m_rw(m: Mem, a: nat) = m_mapped(m, a) && pg(m, a).value.prot.r && pg(m, a).value.prot.w

fn bit(x: nat, i: nat) -> nat = x / 2^i % 2

///////////////////////////////////////////////////////////////////////
//  Layouts (musl 1.2.6, x86_64: PAGESIZE is 4096, no ctx.pagesize)

const UNIT : nat = 16
const IB   : nat = 4

// struct malloc_context
const C_SECRET      : nat = 0
const C_INIT_DONE   : nat = 8
const C_FREE_META   : nat = 16
const C_AVAIL_META  : nat = 24
const C_AVAIL_CNT   : nat = 32
const C_AREA_CNT    : nat = 40
const C_AREA_HEAD   : nat = 56
const C_AREA_TAIL   : nat = 64
const C_AVAIL_AREAS : nat = 72
const C_ACTIVE      : nat = 80      // struct meta *active[48]
const C_BRK         : nat = 920
const CTX_SIZE      : nat = 928
// (the counters and heuristics: unsigned mmap_counter; size_t
// usage_by_class[48], then uint8_t unmap_seq[32], bounces[32], seq up to
// brk; and size_t meta_alloc_shift, the meta areas' mapping size)
const C_MMAP_CNT    : nat = 12
const C_META_SHIFT  : nat = 48
const C_USAGE       : nat = 464

// struct meta: prev, next, mem, avail_mask, freed_mask, then one word with
// last_idx:5, freeable:1, sizeclass:6, maplen:52
const META_SIZE : nat = 40

// struct meta_area: check, next, nslots, then the metas
const AREA_HDR : nat = 24
const NSLOTS   : nat = 101         // (4096 - 24) / 40

// struct __libc: need_locks at 3, auxv at 8
const L_NEED_LOCKS : nat = 3
const L_AUXV       : nat = 8

const size_classes : List[nat] = [
  1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 15, 18, 20, 25, 31,
  36, 42, 50, 63, 72, 84, 102, 127, 146, 170, 204, 255, 292, 340, 409, 511,
  584, 682, 818, 1023, 1169, 1364, 1637, 2047, 2340, 2730, 3276, 4095, 4680, 5460, 6552, 8191]

// malloc.c's slot counts for a new group (alloc_group's): small_cnt_tab's
// rows of 3 for the classes up to 8, med_cnt_tab's by the class mod 4
const small_cnt_tab : List[nat] = [
  30, 30, 30, 31, 15, 15, 20, 10, 10, 31, 15, 7, 25, 12, 6, 21, 10, 5, 18, 8, 4, 31, 15, 7, 28, 14, 6]
const med_cnt_tab : List[nat] = [28, 24, 20, 32]

// malloc.c's debruijn32 (a_ctz_32's, at a de Bruijn sequence's positions)
const debruijn32_tab : List[nat] = [
  0, 1, 23, 2, 29, 24, 19, 3, 30, 27, 25, 11, 20, 8, 4, 13,
  31, 22, 28, 18, 26, 10, 7, 12, 21, 17, 9, 6, 16, 5, 15, 14]

///////////////////////////////////////////////////////////////////////
//  The abstract state

record MetaV {
  prev: nat, next: nat, mem: nat, avail: nat, freed: nat,
  last_idx: nat, freeable: nat, sizeclass: nat, maplen: nat
}

const ZERO_META : MetaV = MetaV { prev: 0, next: 0, mem: 0, avail: 0, freed: 0,
                                  last_idx: 0, freeable: 0, sizeclass: 0, maplen: 0 }

type Use = unused                 // available or freed slot
         | block(p: nat)          // a client block starting at p
         | nested(g: nat)         // the group of meta g
         | reserved               // handed out (alloc_slot), its block not yet framed (malloc)

record Abs {
  secret      : nat
  init_done   : nat
  auxv_at     : nat                // while init_done = 0: libc.auxv ...
  auxv        : List[(nat, nat)]   // ... and its entries
  areas       : List[nat]          // meta areas, in list order
  avail_cnt   : nat                // ctx.avail_meta_count: unused metas at the end of the last area
  reserve     : nat                // ctx.avail_meta_areas: reserved pages for areas ...
  reserve_cnt : nat                // ... and their number (ctx.avail_meta_area_count)
  free_metas  : List[nat]          // from ctx.free_meta_head along next
  used        : List[nat]          // metas describing a group, ascending
  metas       : nat -> MetaV       // their fields
  active      : List[List[nat]]    // for each of the 48 size classes: the list from ctx.active[sc] along next
  slots       : nat -> List[Use]   // for a used meta: what each slot holds
  brk         : nat                // ctx.brk
  taken       : List[nat]          // metas handed out (alloc_meta), their groups not yet made (alloc_group)
}

pred is_used(A: Abs, g: nat) = ex k: nat. k < len(A.used) && A.used[k] = g

///////////////////////////////////////////////////////////////////////
//  Geometry (from the abstract state)

fn meta_at(area: nat, j: nat) -> nat = area + AREA_HDR + META_SIZE * j

// every meta slot of every area
pred meta_slot(A: Abs, g: nat) = ex k: nat, j: nat. k < len(A.areas) && j < NSLOTS && g = meta_at(A.areas[k], j)

// the metas not yet handed out, at the end of the last area
pred avail_meta(A: Abs, g: nat) =
  len(A.areas) > 0 && ex j: nat. NSLOTS - A.avail_cnt <= j && j < NSLOTS && g = meta_at(A.areas[len(A.areas) - 1], j)

fn stride(v: MetaV) -> nat =
  if v.last_idx = 0 && v.maplen > 0 { v.maplen * 4096 - UNIT } else { UNIT * size_classes[v.sizeclass] }

fn storage(v: MetaV) -> nat = v.mem + UNIT
fn slot_start(v: MetaV, i: nat) -> nat = storage(v) + stride(v) * i
fn slot_end(v: MetaV, i: nat) -> nat = slot_start(v, i) + stride(v) - IB      // `end` in meta.h

// Address ranges (start, length).
pred in_range(a: nat, r: (nat, nat)) = r[0] <= a && a < r[0] + r[1]
pred in_ranges(a: nat, rs: List[(nat, nat)]) = ex k: nat. k < len(rs) && in_range(a, rs[k])
pred apart(r: (nat, nat), q: (nat, nat)) = r[1] = 0 || q[1] = 0 || r[0] + r[1] <= q[0] || q[0] + q[1] <= r[0]

// the bytes of a group: its mapping, or the nested group's part of a slot
fn group_range(v: MetaV) -> (nat, nat) =
  if v.maplen > 0 { (v.mem, v.maplen * 4096) } else { (v.mem, UNIT + stride(v) * (v.last_idx + 1) - IB + 1) }

// read-only segments of the image: code and constants
fn ro_ranges(f: File) -> List[(nat, nat)] =
  [if is_load(f, i) && !segment(f, i).flags[1] { (segment(f, i).vaddr, segment(f, i).memsz) } else { (0, 0) }
   for i in 0..phnum(f)]

// libc's auxiliary vector and the AT_RANDOM bytes read at initialization
// (both empty once initialized: `normal`)
fn auxv_ranges(A: Abs) -> List[(nat, nat)] =
  [(A.auxv_at, 16 * len(A.auxv))] ++
  [if A.auxv[k][0] = AT_RANDOM { (A.auxv[k][1] + 8, 8) } else { (0, 0) } for k in 0..len(A.auxv)]

fn data_ranges(c: Cfg) -> List[(nat, nat)] = [(c.ctx, CTX_SIZE), (c.lock, 4), (c.libc, 16)]

// the allocator's fixed regions: the image, its data, the auxiliary
// vector, the meta areas, the reserve, the class table
fn fixed_ranges(c: Cfg, A: Abs) -> List[(nat, nat)] =
  ro_ranges(c.file) ++ data_ranges(c) ++ auxv_ranges(A) ++
  [(A.areas[k], 4096) for k in 0..len(A.areas)] ++ [(A.reserve, 4096 * A.reserve_cnt)] ++
  [(c.sct, 2 * 48)] ++ [(c.dbj, 32)]

// everything the allocator owns (before taking out the live blocks): its
// fixed regions and its groups
fn fp_ranges(c: Cfg, A: Abs) -> List[(nat, nat)] =
  fixed_ranges(c, A) ++ [group_range(A.metas[A.used[k]]) for k in 0..len(A.used)]

fn fp_set(rs: List[(nat, nat)], blocks: Addr -> Option[nat]) -> Set[nat] =
  {a: nat | in_ranges(a, rs) && a notin live_of(blocks)}

// the interior of slot i of a group: all but the first of its in-band
// header's bytes (the previous slot's end check), up to its end
pred in_slot(v: MetaV, i: nat, a: nat) = slot_start(v, i) - IB < a && a < slot_end(v, i)

// a reserved slot's interior: handed out (`alloc_slot`), whoever reserved
// it frames it (`enframe`) -- no longer the allocator's
pred in_reserved(A: Abs, a: nat) =
  ex g: nat, i: nat. is_used(A, g) && i < len(A.slots[g]) && A.slots[g][i] = reserved && in_slot(A.metas[g], i, a)

// a taken meta's bytes: handed out (`alloc_meta`), whoever took it makes
// its group (`alloc_group`) -- no longer the allocator's
pred in_taken(A: Abs, a: nat) = ex k: nat. k < len(A.taken) && A.taken[k] <= a && a < A.taken[k] + META_SIZE

// the bytes the allocator owns
fn footprint(c: Cfg, A: Abs, blocks: Addr -> Option[nat]) -> Set[nat] =
  {a: nat | a in fp_set(fp_ranges(c, A), blocks) && !in_reserved(A, a) && !in_taken(A, a)}

// the context's bytes the invariant leaves free: musl's counters and
// heuristics -- the allocator's (in the footprint), of any value
pred ctx_free(c: Cfg, a: nat) =
  (c.ctx + C_MMAP_CNT <= a && a < c.ctx + C_MMAP_CNT + 4) || (c.ctx + C_USAGE <= a && a < c.ctx + C_BRK)

// the bytes the invariant reads: the footprint but the free ones
fn held(c: Cfg, A: Abs, blocks: Addr -> Option[nat]) -> Set[nat] =
  {a: nat | a in footprint(c, A, blocks) && !ctx_free(c, a)}

// the free bytes accessible (out of the invariant's view: on the
// footprint's, m)
pred free_rw(c: Cfg, m: Mem) =
  all a: nat. ctx_free(c, a) -> m_rw(m, a) && pg(m, a).value.kind != stack

// every byte (memory as a whole, seen as the invariant sees it)
fn all_bytes() -> Set[nat] = {a: nat | true}

// the bytes of slot i (its check byte, its interior) accessible: readable
// and writable, not the stack
pred slot_rw(vm: Vm, v: MetaV, i: nat) =
  all a: nat. slot_start(v, i) - IB <= a && a < slot_end(v, i) ->
    m_rw(mview(vm, all_bytes()), a) && pg(mview(vm, all_bytes()), a).value.kind != stack

///////////////////////////////////////////////////////////////////////
//  Memory agrees with the abstract state

pred meta_in_memory(m: Mem, g: nat, v: MetaV) =
  prev: rd(m, g, 8) = v.prev && next: rd(m, g + 8, 8) = v.next && mem: rd(m, g + 16, 8) = v.mem &&
  avail: rd(m, g + 24, 4) = v.avail && freed: rd(m, g + 28, 4) = v.freed &&
  word: rd(m, g + 32, 8) = v.last_idx + 32 * v.freeable + 64 * v.sizeclass + 4096 * v.maplen &&
  last: v.last_idx < 32 && freeable: v.freeable < 2 && sclass: v.sizeclass < 64

fn ctx_word(c: Cfg, m: Mem, off: nat) -> nat = rd(m, c.ctx + off, 8)

// a list linked by `next` (offset 8) and `prev` (offset 0), cyclic, from `head`
pred cyclic(m: Mem, head: nat, l: List[nat]) =
  first: head = (if len(l) = 0 { 0 } else { l[0] }) &&
  distinct: (all i: nat, j: nat. i < len(l) && j < len(l) && l[i] = l[j] -> i = j) &&
  links: (all i: nat. i < len(l) ->
     rd(m, l[i] + 8, 8) = l[(i + 1) % len(l)] && rd(m, l[i], 8) = l[(i + len(l) - 1) % len(l)])

pred ctx_ok(c: Cfg, A: Abs, m: Mem) =
  secret: ctx_word(c, m, C_SECRET) = A.secret &&
  init: rd(m, c.ctx + C_INIT_DONE, 4) = A.init_done && init_lt: A.init_done < 2 &&
  avail_cnt: ctx_word(c, m, C_AVAIL_CNT) = A.avail_cnt && avail_le: A.avail_cnt <= NSLOTS &&
  avail_meta: (A.avail_cnt > 0 -> len(A.areas) > 0 &&
     ctx_word(c, m, C_AVAIL_META) = meta_at(A.areas[len(A.areas) - 1], NSLOTS - A.avail_cnt)) &&
  area_cnt: ctx_word(c, m, C_AREA_CNT) = A.reserve_cnt &&
  avail_areas: (A.reserve_cnt > 0 -> ctx_word(c, m, C_AVAIL_AREAS) = A.reserve && A.reserve % 4096 = 0) &&
  brk: ctx_word(c, m, C_BRK) = A.brk &&
  free_metas: cyclic(m, ctx_word(c, m, C_FREE_META), A.free_metas) &&
  nactive: len(A.active) = 48 &&
  active: (all sc: nat. sc < 48 -> cyclic(m, ctx_word(c, m, C_ACTIVE + 8 * sc), A.active[sc])) &&
  // (the meta areas' mappings, 2 << shift pages each, doubling: one of
  // 2^35 pages is past the user space, so never made)
  shift: ctx_word(c, m, C_META_SHIFT) <= 34

// before the first allocation: nothing yet, and libc's auxv is readable
pred fresh_ok(c: Cfg, A: Abs, m: Mem) =
  A.init_done = 0 ->
    areas: len(A.areas) = 0 && reserve: A.reserve_cnt = 0 && free_metas: len(A.free_metas) = 0 && used: len(A.used) = 0 &&
    avail: A.avail_cnt = 0 && active: (all sc: nat. sc < 48 -> len(A.active[sc]) = 0) &&
    auxv_at: rd(m, c.libc + L_AUXV, 8) = A.auxv_at &&
    auxv_len: len(A.auxv) >= 1 &&
    auxv: (all k: nat. k < len(A.auxv) ->
       rd(m, A.auxv_at + 16 * k, 8) = A.auxv[k][0] && rd(m, A.auxv_at + 16 * k + 8, 8) = A.auxv[k][1]) &&
    auxv_end: A.auxv[len(A.auxv) - 1][0] = AT_NULL && auxv_null: (all k: nat. k + 1 < len(A.auxv) -> A.auxv[k][0] != AT_NULL) &&
    // (on the initial stack, apart from the context)
    auxv_ctx: (all k: nat, a: nat. k < len(auxv_ranges(A)) && auxv_ranges(A)[k][0] <= a && a < auxv_ranges(A)[k][0] + auxv_ranges(A)[k][1] ->
       !(c.ctx <= a && a < c.ctx + CTX_SIZE))

pred areas_ok(c: Cfg, A: Abs, m: Mem) =
  head: ctx_word(c, m, C_AREA_HEAD) = (if len(A.areas) = 0 { 0 } else { A.areas[0] }) &&
  tail: ctx_word(c, m, C_AREA_TAIL) = (if len(A.areas) = 0 { 0 } else { A.areas[len(A.areas) - 1] }) &&
  each: (all k: nat. k < len(A.areas) ->
     A.areas[k] % 4096 = 0 && A.areas[k] > 0 &&
     rd(m, A.areas[k], 8) = A.secret &&
     rd(m, A.areas[k] + 8, 8) = (if k + 1 < len(A.areas) { A.areas[k + 1] } else { 0 }) &&
     rd(m, A.areas[k] + 16, 4) = NSLOTS &&
     (all a: nat. A.areas[k] <= a && a < A.areas[k] + 4096 && !in_taken(A, a) -> m_rw(m, a) && pg(m, a).value.kind != stack)) &&
  distinct: (all k: nat, l: nat. k < len(A.areas) && l < len(A.areas) && A.areas[k] = A.areas[l] -> k = l) &&
  // reserved pages: mapped (maybe PROT_NONE), zero
  reserve: (all a: nat. A.reserve <= a && a < A.reserve + 4096 * A.reserve_cnt -> m_mapped(m, a) && pg(m, a).value.kind != stack && b8(m, a) = 0)

// every meta slot is used, free, not yet handed out, or taken (handed out,
// its group not yet made) -- exactly one
pred metas_partition(A: Abs) =
  sorted: (all k: nat. k + 1 < len(A.used) -> A.used[k] < A.used[k + 1]) &&
  used_slots: (all k: nat. k < len(A.used) -> meta_slot(A, A.used[k])) &&
  free_slots: (all k: nat. k < len(A.free_metas) -> meta_slot(A, A.free_metas[k]) && !is_used(A, A.free_metas[k])) &&
  cover: (all k: nat, j: nat. k < len(A.areas) && j < NSLOTS ->
     is_used(A, meta_at(A.areas[k], j)) ||
     (ex i: nat. i < len(A.free_metas) && A.free_metas[i] = meta_at(A.areas[k], j)) ||
     avail_meta(A, meta_at(A.areas[k], j)) ||
     (ex i: nat. i < len(A.taken) && A.taken[i] = meta_at(A.areas[k], j))) &&
  taken: (all i: nat. i < len(A.taken) ->
     meta_slot(A, A.taken[i]) && !is_used(A, A.taken[i]) && !avail_meta(A, A.taken[i]) &&
     (all k: nat. k < len(A.free_metas) -> A.free_metas[k] != A.taken[i]) &&
     (all k: nat. k < len(A.taken) && A.taken[k] = A.taken[i] -> k = i)) &&
  fresh: (all j: nat. len(A.areas) > 0 && NSLOTS - A.avail_cnt <= j && j < NSLOTS ->
     !is_used(A, meta_at(A.areas[len(A.areas) - 1], j)) &&
     (all i: nat. i < len(A.free_metas) -> A.free_metas[i] != meta_at(A.areas[len(A.areas) - 1], j)))

// the reserved-size encoding (`set_size`) of the n bytes at p in a slot
// ending at end: the r = end - p - n bytes after them recorded in the top 3
// bits of the header byte at p - 3 -- r, or 5 for r >= 5, the count then in
// the 32-bit word at end - 4 and a 0 byte before it; the first of them 0
pred size_ok(m: Mem, p: nat, end: nat, n: nat) =
  (end - p - n >= 5 -> b8(m, p - 3) / 32 = 5 && rd(m, end - 4, 4) = end - p - n && b8(m, end - 5) = 0) &&
  (end - p - n < 5 -> b8(m, p - 3) / 32 = end - p - n) &&
  (end - p - n > 0 -> b8(m, p + n) = 0)

// the slot of a client block or nested group starting at p (`enframe`): the
// in-band header before p, the reserved-size encoding up to the slot end
pred frame_ok(m: Mem, v: MetaV, i: nat, p: nat, n: nat, tag: nat) =
  start: slot_start(v, i) <= p && unit: (p - slot_start(v, i)) % UNIT = 0 && fits: p + n <= slot_end(v, i) &&
  check: b8(m, p - 4) = 0 &&
  index: b8(m, p - 3) % 32 = i &&
  offset: rd(m, p - 2, 2) = (p - storage(v)) / UNIT &&
  moved: (p > slot_start(v, i) ->
     rd(m, slot_start(v, i) - 2, 2) = (p - slot_start(v, i)) / UNIT && b8(m, slot_start(v, i) - 3) = 7 * 32) &&
  nested: (tag = 6 -> b8(m, p - 3) / 32 = 6) &&
  sized: (tag != 6 -> size_ok(m, p, slot_end(v, i), n) && b8(m, slot_end(v, i)) = 0) &&
  // (within its class's slot, as get_meta checks: a group of one slot
  // mapped on its own has a larger stride)
  in_class: (v.sizeclass < 48 -> p - storage(v) < UNIT * size_classes[v.sizeclass] * (i + 1))

// the in-band header before p (its IB bytes): no client's
pred hdr_free(blocks: Addr -> Option[nat], p: nat) = all a: nat. p - IB <= a && a < p -> a notin live_of(blocks)

// what slot i of the group g holds (a nested group framed like a block:
// at a unit offset in the slot -- enframe's, the slot's slack cycled --,
// its slots and their end within it)
pred slot_ok(A: Abs, m: Mem, blocks: Addr -> Option[nat], g: nat, i: nat, u: Use) =
  match u {
    unused    => true,
    block(p)  => blocks[bits[64](p)] != none && hdr_free(blocks, p) &&
                 frame_ok(m, A.metas[g], i, p, blocks[bits[64](p)].value, 0),
    nested(h) => is_used(A, h) && A.metas[h].maplen = 0 &&
                 hdr_free(blocks, A.metas[h].mem) &&
                 frame_ok(m, A.metas[g], i, A.metas[h].mem, UNIT + stride(A.metas[h]) * (A.metas[h].last_idx + 1) - IB, 6),
    reserved  => true
  }

// a group's masks: its free slots in exactly one, the available ones up to
// the active index (the group header's), the slots above it freed (never
// handed out)
pred masks_ok(A: Abs, m: Mem, g: nat) =
  all i: nat. i < 32 ->
    (bit(A.metas[g].avail, i) = 1 -> i <= b8(m, A.metas[g].mem + 8) % 32 && bit(A.metas[g].freed, i) = 0) &&
    (bit(A.metas[g].avail, i) + bit(A.metas[g].freed, i) > 0 -> i <= A.metas[g].last_idx) &&
    (i <= A.metas[g].last_idx ->
       (A.slots[g][i] = unused <-> bit(A.metas[g].avail, i) + bit(A.metas[g].freed, i) > 0) &&
       b8(m, slot_start(A.metas[g], i) - 4) = 0) &&
    (b8(m, A.metas[g].mem + 8) % 32 < i && i <= A.metas[g].last_idx -> bit(A.metas[g].freed, i) = 1)

// a big allocation's group: one slot, in use
pred big_ok(A: Abs, g: nat) =
  A.metas[g].sizeclass = 63 -> A.metas[g].last_idx = 0 && A.metas[g].maplen > 0 && A.metas[g].avail = 0 && A.metas[g].freed = 0

pred group_ok(A: Abs, m: Mem, blocks: Addr -> Option[nat], g: nat) =
  mim: meta_in_memory(m, g, A.metas[g]) &&
  cls: (A.metas[g].sizeclass < 48 || A.metas[g].sizeclass = 63) &&
  // the group header points back (and is not client memory); active_idx
  hdr: (rd(m, A.metas[g].mem, 8) = g && A.metas[g].mem % UNIT = 0 && A.metas[g].mem > 0) &&
  hdr_own: (all a: nat. A.metas[g].mem <= a && a < A.metas[g].mem + UNIT -> a notin live_of(blocks)) &&
  act: b8(m, A.metas[g].mem + 8) % 32 <= A.metas[g].last_idx &&
  nslots: len(A.slots[g]) = A.metas[g].last_idx + 1 &&
  masks: masks_ok(A, m, g) &&
  // a group of 16-byte slots fully active (more would never reach a page
  // boundary: try_avail's growth would not end)
  small: (stride(A.metas[g]) = UNIT -> b8(m, A.metas[g].mem + 8) % 32 = A.metas[g].last_idx) &&
  // an individually mapped group, or one nested in a slot of another
  mapped: (A.metas[g].maplen > 0 ->
     page: A.metas[g].mem % 4096 = 0 &&
     fits: UNIT + stride(A.metas[g]) * (A.metas[g].last_idx + 1) <= A.metas[g].maplen * 4096) &&
  nested: (A.metas[g].maplen = 0 ->
     ex k: nat, i: nat. k < len(A.used) && i < len(A.slots[A.used[k]]) && A.slots[A.used[k]][i] = nested(g)) &&
  big: big_ok(A, g) &&
  // on an active list exactly when linked
  linked: (A.metas[g].next != 0 <->
     A.metas[g].sizeclass < 48 &&
     (ex k: nat. k < len(A.active[A.metas[g].sizeclass]) && A.active[A.metas[g].sizeclass][k] = g)) &&
  unlinked: (A.metas[g].next = 0 -> A.metas[g].prev = 0) &&
  // the slots in use
  slots: (all i: nat. i < len(A.slots[g]) -> slot_ok(A, m, blocks, g, i, A.slots[g][i])) &&
  // the byte after the last slot 0 (its end check: the next slot's header
  // byte for the others; `alloc_group` writes it for a nested group)
  sentinel: b8(m, slot_end(A.metas[g], A.metas[g].last_idx)) = 0 &&
  // each slot's check byte (its in-band header's first, the previous
  // slot's end), the last's end too: no client's
  chk_own: (all i: nat. i <= A.metas[g].last_idx + 1 -> slot_start(A.metas[g], i) - IB notin live_of(blocks)) &&
  // a group of several slots: their offsets in units within 16 bits (the
  // in-band header's; `alloc_group` keeps it so)
  offs: (A.metas[g].last_idx > 0 -> stride(A.metas[g]) * (A.metas[g].last_idx + 1) <= 2^16 * UNIT) &&
  // a class's group: its slots shorter than two of the class's (`enframe`
  // frames within the class's slot -- get_meta's check -- what a slot of a
  // group mapped on its own leaves past it; `alloc_group` maps one slot
  // only for a class past half a page)
  span: (A.metas[g].sizeclass < 48 -> stride(A.metas[g]) < 2 * (UNIT * size_classes[A.metas[g].sizeclass]))

pred used_ok(A: Abs, m: Mem, blocks: Addr -> Option[nat]) =
  all k: nat. k < len(A.used) -> group_ok(A, m, blocks, A.used[k])

// Only the head of an active list has available slots (`activate_group`
// asserts it for a new head); a full group still linked is the head
// (`queue` in nontrivial_free asserts the group is not linked).
pred active_ok(A: Abs) =
  all sc: nat, k: nat. sc < 48 && k < len(A.active[sc]) ->
    is_used(A, A.active[sc][k]) && A.metas[A.active[sc][k]].sizeclass = sc &&
    (k > 0 -> A.metas[A.active[sc][k]].avail = 0 && A.metas[A.active[sc][k]].freed != 0)

// on a class's active list, at most one group with slots never handed out
// (its active index below its last slot): only alloc_group makes such a
// group, queued on an empty list (try_avail's `assert(mask)` rests on it);
// such a group's slots reach past its first page (alloc_group activates the
// slots within it; try_avail activates more up to a page's end)
pred partial(m: Mem, A: Abs, g: nat) = b8(m, A.metas[g].mem + 8) % 32 < A.metas[g].last_idx

pred partial_ok(A: Abs, m: Mem) =
  (all sc: nat, g: nat, g2: nat. sc < 48 && on_list(A.active[sc], g) && on_list(A.active[sc], g2) &&
     partial(m, A, g) && partial(m, A, g2) -> g = g2) &&
  (all sc: nat, g: nat. sc < 48 && on_list(A.active[sc], g) && partial(m, A, g) ->
     4096 < UNIT + stride(A.metas[g]) * (A.metas[g].last_idx + 1))

// a group on a class's list with an unused slot fits the class's requests:
// not one mapped on its own shorter than the class's slots (free unmaps
// those as soon as a slot is free: musl's okay_to_free)
pred reuse_ok(A: Abs) =
  all sc: nat, g: nat. sc < 48 && on_list(A.active[sc], g) && has_unused(A, g) -> !own_mapping(A.metas[g])

// every live block is in a slot (in only one: slots and groups do not overlap)
pred blocks_ok(A: Abs, blocks: Addr -> Option[nat]) =
  all p: Addr. blocks[p] != none ->
    ex k: nat, i: nat. k < len(A.used) && i < len(A.slots[A.used[k]]) && A.slots[A.used[k]][i] = block(uint(p))

// the abstract state is normalized where memory says nothing
pred normal(A: Abs) =
  unused: (all g: nat. !is_used(A, g) -> A.metas[g] = ZERO_META && len(A.slots[g]) = 0) &&
  init: (A.init_done != 0 -> len(A.auxv) = 0 && A.auxv_at = 0) &&
  reserve: (A.reserve_cnt = 0 <-> A.reserve = 0) &&
  zero: !is_used(A, 0)

// musl's code and constant tables are intact; single-threaded; the lock is free
pred image_ok(c: Cfg, m: Mem) =
  ro: (all i: nat. i < phnum(c.file) && is_load(c.file, i) -> ro_segment_ok(c.file, i, segment(c.file, i), m)) &&
  need_locks: b8(m, c.libc + L_NEED_LOCKS) = 0 && lock: rd(m, c.lock, 4) = 0

// segment i (= sg) of f, if read-only, is in memory as exec maps it: its
// bytes, and the protection of the pages it is the last segment on (seen
// at its own bytes there)
pred ro_segment_ok(f: File, i: nat, sg: Segment, m: Mem) =
  !sg.flags[1] ->
    (all a: nat. sg.vaddr <= a && a < sg.vaddr + sg.memsz ->
       b8(m, a) = (if a < sg.vaddr + sg.filesz { uint(f[sg.offset + (a - sg.vaddr)]) } else { 0 })) &&
    (all a: nat. sg.vaddr <= a && a < sg.vaddr + sg.memsz && last_on_page(f, i, a / PAGE) ->
       pg(m, a) = some(Page { prot: seg_prot(sg), kind: anon }))

// the allocator's memory can be accessed as the code does (its groups:
// not on the stack, where GIMPLE's accesses are to stack objects only)
pred perms_ok(c: Cfg, A: Abs, m: Mem, blocks: Addr -> Option[nat]) =
  data: (all k: nat, a: nat. k < 3 && data_ranges(c)[k][0] <= a && a < data_ranges(c)[k][0] + data_ranges(c)[k][1] && !ctx_free(c, a) ->
     m_rw(m, a) && pg(m, a).value.kind != stack) &&
  groups: (all k: nat, a: nat. k < len(A.used) &&
     group_range(A.metas[A.used[k]])[0] <= a && a < group_range(A.metas[A.used[k]])[0] + group_range(A.metas[A.used[k]])[1] &&
     a notin live_of(blocks) && !in_reserved(A, a) -> m_rw(m, a) && pg(m, a).value.kind != stack) &&
  auxv: (all k: nat, a: nat. k < len(auxv_ranges(A)) &&
     auxv_ranges(A)[k][0] <= a && a < auxv_ranges(A)[k][0] + auxv_ranges(A)[k][1] ->
       m_mapped(m, a) && pg(m, a).value.prot.r && pg(m, a).value.kind != stack)

// Separate regions: the data symbols, the image, the meta areas, the
// reserved pages and the individually mapped groups do not overlap (nested
// groups lie in slots of their parent).
fn regions(c: Cfg, A: Abs) -> List[(nat, nat)] =
  data_ranges(c) ++ ro_ranges(c.file) ++ [(A.areas[k], 4096) for k in 0..len(A.areas)] ++
  [(A.reserve, 4096 * A.reserve_cnt)] ++
  [if A.metas[A.used[k]].maplen > 0 { group_range(A.metas[A.used[k]]) } else { (0, 0) } for k in 0..len(A.used)]

pred separate(rs: List[(nat, nat)]) =
  all k: nat, l: nat. k < len(rs) && l < len(rs) && k != l -> apart(rs[k], rs[l])

// the program break: not used yet (the kernel's in the user space: only
// malloc moves it, musl's brk() refuses), given up, or where the kernel
// has it
pred brk_ok(A: Abs, brk: Addr) =
  (A.brk = 0 && uint(brk) <= TASK_SIZE) || A.brk = 2^64 - 1 || (A.brk = uint(brk) && A.brk % 4096 = 0)

// the size classes' table (the code reads it): readable, as the source has
// it, one of the image's constants (in a read-only segment)
pred classes_ok(c: Cfg, m: Mem) =
  (all i: nat. i < 48 -> rd(m, c.sct + 2 * i, 2) = size_classes[i]) &&
  (all a: nat. c.sct <= a && a < c.sct + 2 * 48 -> m_mapped(m, a) && pg(m, a).value.prot.r && pg(m, a).value.kind != stack) &&
  (ex i: nat. i < phnum(c.file) && ro_ranges(c.file)[i][0] <= c.sct && c.sct + 2 * 48 <= ro_ranges(c.file)[i][0] + ro_ranges(c.file)[i][1]) &&
  counts: counts_ok(c, m)

// the slot counts' tables: the same
pred counts_ok(c: Cfg, m: Mem) =
  small: (all i: nat. i < 27 -> b8(m, c.scnt + i) = small_cnt_tab[i]) && med: (all i: nat. i < 4 -> b8(m, c.mcnt + i) = med_cnt_tab[i]) &&
  read: (all a: nat. (c.scnt <= a && a < c.scnt + 27) || (c.mcnt <= a && a < c.mcnt + 4) ->
     m_mapped(m, a) && pg(m, a).value.prot.r && pg(m, a).value.kind != stack) &&
  ro_small: (ex i: nat. i < phnum(c.file) && ro_ranges(c.file)[i][0] <= c.scnt && c.scnt + 27 <= ro_ranges(c.file)[i][0] + ro_ranges(c.file)[i][1]) &&
  ro_med: (ex i: nat. i < phnum(c.file) && ro_ranges(c.file)[i][0] <= c.mcnt && c.mcnt + 4 <= ro_ranges(c.file)[i][0] + ro_ranges(c.file)[i][1])

// a_ctz_32's table (the code reads it): the same
pred debruijn_ok(c: Cfg, m: Mem) =
  (all i: nat. i < 32 -> rd(m, c.dbj + i, 1) = debruijn32_tab[i]) &&
  (all a: nat. c.dbj <= a && a < c.dbj + 32 -> m_mapped(m, a) && pg(m, a).value.prot.r && pg(m, a).value.kind != stack) &&
  (ex i: nat. i < phnum(c.file) && ro_ranges(c.file)[i][0] <= c.dbj && c.dbj + 32 <= ro_ranges(c.file)[i][0] + ro_ranges(c.file)[i][1])

// the meta areas, the reserve, the tables and the context: no client's bytes
pred fixed_free(c: Cfg, A: Abs, blocks: Addr -> Option[nat]) =
  areas: (all k: nat, a: nat. k < len(A.areas) && A.areas[k] <= a && a < A.areas[k] + 4096 -> a notin live_of(blocks)) &&
  reserve: (all a: nat. A.reserve <= a && a < A.reserve + 4096 * A.reserve_cnt -> a notin live_of(blocks)) &&
  classes: (all a: nat. c.sct <= a && a < c.sct + 2 * 48 -> a notin live_of(blocks)) &&
  debruijn: (all a: nat. c.dbj <= a && a < c.dbj + 32 -> a notin live_of(blocks)) &&
  context: (all a: nat. c.ctx <= a && a < c.ctx + CTX_SIZE -> a notin live_of(blocks))

// the groups (nested ones too: inside their parent's slot) apart from the
// fixed regions -- a group's slot written is none of those
pred groups_apart(c: Cfg, A: Abs) =
  all k: nat, a: nat. k < len(A.used) && in_range(a, group_range(A.metas[A.used[k]])) -> !in_ranges(a, fixed_ranges(c, A))

pred holds(c: Cfg, A: Abs, m: Mem, blocks: Addr -> Option[nat], brk: Addr) =
  image: image_ok(c, m) && ctx: ctx_ok(c, A, m) && fresh: fresh_ok(c, A, m) && areas: areas_ok(c, A, m) &&
  part: metas_partition(A) && used: used_ok(A, m, blocks) && active: active_ok(A) && partial: partial_ok(A, m) && reuse: reuse_ok(A) && in_slots: blocks_ok(A, blocks) &&
  normal: normal(A) && brk: brk_ok(A, brk) && perms: perms_ok(c, A, m, blocks) && sep: separate(regions(c, A)) &&
  wf: blocks_wf(blocks) &&       // (what the law inv_wf needs, stated directly)
  classes: classes_ok(c, m) && debruijn: debruijn_ok(c, m) && fixed: fixed_free(c, A, blocks) && apart: groups_apart(c, A)

///////////////////////////////////////////////////////////////////////
//  The invariant and the owned bytes

// the owned bytes are mapped (for the law owned_mapped)
pred fp_mapped(rs: List[(nat, nat)], blocks: Addr -> Option[nat], vm: Vm) =
  all k: nat, a: nat. k < len(rs) && rs[k][0] <= a && a < rs[k][0] + rs[k][1] && a notin live_of(blocks) ->
    mapped(vm, a / PAGE)

// no slot handed out and not yet framed (between the allocator's calls)
pred no_reserved(A: Abs) = all g: nat, i: nat. i < len(A.slots[g]) -> A.slots[g][i] != reserved

// the allocator's memory the C world's: its bytes the C world's (its
// data may share a page with what is not: the thread's descriptor), the
// reserve's pages all of them (the kernel's to reprotect: valid pages)
pred fp_shown(rs: List[(nat, nat)], objs: Objs) = all a: nat. in_ranges(a, rs) -> a in objs.c_bytes
pred shown_in(c: Cfg, A: Abs, objs: Objs) =
  fp: fp_shown(fp_ranges(c, A), objs) &&
  rsv: (A.reserve_cnt > 0 -> all a: nat. A.reserve / PAGE <= a / PAGE && a / PAGE < A.reserve / PAGE + A.reserve_cnt -> a in objs.c_bytes)

pred rep(c: Cfg, A: Abs, s: Heap) =
  inv: holds(c, A, mview(s.vm, held(c, A, s.blocks)), s.blocks, s.vm.brk) && unres: no_reserved(A) && untaken: len(A.taken) = 0 &&
  mapped: fp_mapped(fp_ranges(c, A), s.blocks, s.vm) && free: free_rw(c, mview(s.vm, footprint(c, A, s.blocks))) &&
  rw: grp_rw(c, A, s.vm, s.blocks) &&
  live: live_rw(s)           // (what the law inv_wf needs, stated directly)

fn inv(c: Cfg) -> Set[Heap] = {s: Heap | ex A: Abs. rep(c, A, s)}

// the footprints of all abstract states that hold: by `abs_unique`, there
// is just one
fn owned_of(c: Cfg, s: Heap) -> Set[nat] = {a: nat | ex A: Abs. rep(c, A, s) && a in footprint(c, A, s.blocks)}

fn owned(c: Cfg) -> Heap -> Set[nat] = (s: Heap) => owned_of(c, s)

///////////////////////////////////////////////////////////////////////
//  Internal steps by their purpose
//
// What an internal function is for, in the abstract state: a step from a
// state A that holds to one A2 that holds (the client's blocks the same),
// the memory outside the allocator's untouched. Which of musl's choices it
// makes -- its heuristics -- is left free.

// the allocator's memory, as the invariant sees it, mapped (user space:
// no byte's address wraps)
// a group in use: its bytes accessible -- the allocator's, a client's
// block's, a slot's handed out (whose caller frames it: `slot_rw`); every
// byte of the group one of these
pred grp_rw(c: Cfg, A: Abs, vm: Vm, blocks: Addr -> Option[nat]) =
  all g: nat, a: nat. is_used(A, g) && in_range(a, group_range(A.metas[g])) &&
    (a in footprint(c, A, blocks) || a in live_of(blocks) || in_reserved(A, a)) ->
    m_rw(mview(vm, all_bytes()), a) && pg(mview(vm, all_bytes()), a).value.kind != stack

pred holds_m(c: Cfg, A: Abs, vm: Vm, blocks: Addr -> Option[nat]) =
  inv: holds(c, A, mview(vm, held(c, A, blocks)), blocks, vm.brk) && mapped: fp_mapped(fp_ranges(c, A), blocks, vm) && free: free_rw(c, mview(vm, footprint(c, A, blocks))) &&
  rw: grp_rw(c, A, vm, blocks) &&
  // the reserve's pages: ones the kernel may reprotect (mapped, off the
  // stack's space, not executable -- as mmap and brk made them)
  rsv: (A.reserve_cnt > 0 -> off_stack_space(vm, A.reserve / PAGE, A.reserve_cnt) &&
    (all q: nat. A.reserve / PAGE <= q && q < A.reserve / PAGE + A.reserve_cnt -> mapped(vm, q) && !vm.pages[q].value.prot.x))

// ... in the C world: the memory's (holds_m), the allocator's bytes the
// world's (shown_in)
pred holds_in(c: Cfg, A: Abs, vm: Vm, objs: Objs, blocks: Addr -> Option[nat]) =
  mem: holds_m(c, A, vm, blocks) && shown: shown_in(c, A, objs)

pred has_unused(A: Abs, g: nat) = ex i: nat. i < len(A.slots[g]) && A.slots[g][i] = unused
pred on_list(l: List[nat], g: nat) = ex k: nat. k < len(l) && l[k] = g

// a group that is one slot mapped on its own, the mapping shorter than its
// class's slots (or no class): musl's test (`__malloc_allzerop`) that a
// slot's memory came fresh from the kernel, so calloc need not clear it
pred own_mapping(v: MetaV) = v.sizeclass >= 48 || stride(v) < UNIT * size_classes[v.sizeclass]

// slot i of the group g: where what starts at p lies (a client block, or a
// nested group)
pred starts_at(A: Abs, g: nat, i: nat, p: nat) =
  is_used(A, g) && i < len(A.slots[g]) &&
  (A.slots[g][i] = block(p) || (ex h: nat. A.slots[g][i] = nested(h) && A.metas[h].mem = p))

// the only reserved slot: slot i of g
pred reserved_only(A: Abs, g: nat, i: nat) =
  i < len(A.slots[g]) && A.slots[g][i] = reserved &&
  (all h: nat, j: nat. j < len(A.slots[h]) && A.slots[h][j] = reserved -> h = g && j = i)

// A2: A with class sc's active list reorganised -- its order, its groups'
// links and masks (which free slots are available, which freed) -- and
// groups without an unused slot dropped from it; nothing else
pred reorganised(A: Abs, A2: Abs, sc: nat) =
  (A2 with { metas: A.metas, active: A.active, slots: A.slots }) = A &&
  (all g: nat. (A2.metas[g] with { prev: 0, next: 0, avail: 0, freed: 0 }) = (A.metas[g] with { prev: 0, next: 0, avail: 0, freed: 0 })) &&
  len(A2.active) = len(A.active) && (all s: nat. s != sc -> A2.active[s] = A.active[s]) &&
  (all g: nat. on_list(A2.active[sc], g) -> on_list(A.active[sc], g)) &&
  (all g: nat. on_list(A.active[sc], g) && !on_list(A2.active[sc], g) -> !has_unused(A, g))

// A2: A with slot i of g, unused in A, reserved; the other slots the same
pred reserves(A: Abs, A2: Abs, g: nat, i: nat) =
  i < len(A.slots[g]) && A.slots[g][i] = unused &&
  len(A2.slots[g]) = len(A.slots[g]) && A2.slots[g][i] = reserved &&
  (all j: nat. j != i -> A2.slots[g][j] = A.slots[g][j]) &&
  (all h: nat. h != g -> A2.slots[h] = A.slots[h])

// the memory outside the allocator's (in A) untouched, but for `extra` and
// what was unmapped; the program break's start kept
pred untouched(c: Cfg, A: Abs, blocks: Addr -> Option[nat], vm: Vm, vm2: Vm, extra: Set[nat]) =
  (all a: nat. a notin footprint(c, A, blocks) && a notin extra && mapped(vm, a / PAGE) ->
     vm2.bytes[bits[64](a)] = vm.bytes[bits[64](a)] && vm2.pages[a / PAGE] = vm.pages[a / PAGE]) &&
  vm2.brk_start = vm.brk_start
