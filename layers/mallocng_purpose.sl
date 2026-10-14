layer mallocng_purpose uses gimple, abi, mallocng, mallocng_specs

// Specs of mallocng's internal functions by their purpose: what each is
// for in the abstract state (layers/mallocng.sl's `Abs`, a ghost of the C
// world), not how musl's code does it. Each a contract (layers/abi.sl): a
// precondition, then a stack overflow or the effect. Their C2: the code
// refines them directly, `refines_ghost` (proofs/mallocng_purpose.core).

// The state of the allocator's internal functions: the C world, the
// client's blocks (malloc's ghost), and the abstract state A (a ghost the
// specs update; the invariant, where a spec requires it, ties it to memory).
// A spec may read both: the memory where that is its purpose, A where
// that is.
state MallocAbs extends Heap {
  ghost A : Abs
}

// The lists (a class's active groups, the free metas): cyclic through the
// metas' first two words (`cyclic`)

// l without its k-th element, the others' order kept
fn rm_at(l: List[nat], k: nat) -> List[nat] = [l[if j < k { j } else { j + 1 }] for j in 0..len(l) - 1]

// the list l at *phead: linked cyclically, its elements' links accessible,
// 8-aligned, apart from each other and from the head word
pred list_at(vm: Vm, objs: Set[nat], phead: bits[64], l: List[nat]) =
  word_ok(vm, objs, phead, 0) && al8(phead) &&
  cyclic(mview(vm, all_bytes()), uint(rd64(vm, phead)), l) &&
  (all i: nat. i < len(l) -> l[i] + 16 <= 2^64 && word_ok(vm, objs, bits[64](l[i]), 0) && word_ok(vm, objs, bits[64](l[i]), 8) && l[i] % 8 = 0 &&
     (uint(phead) + 8 <= l[i] || l[i] + 16 <= uint(phead))) &&
  (all i: nat, j: nat. i < len(l) && j < len(l) && i != j -> l[i] + 16 <= l[j] || l[j] + 16 <= l[i])

// no byte but the head word and l's link words changed, nothing else
pred links_only(before: Vm, vm: Vm, phead: bits[64], l: List[nat]) =
  (vm with { bytes: before.bytes }) = before &&
  (all a: nat. a < 2^64 && !(uint(phead) <= a && a < uint(phead) + 8) && (all i: nat. i < len(l) -> !(l[i] <= a && a < l[i] + 16)) ->
     vm.bytes[bits[64](a)] = before.bytes[bits[64](a)])

// dequeue(phead, m), m in the list at phead: m out of it, the others'
// order kept, m's links cleared
pred dequeued(before: Vm, vm: Vm, objs: Set[nat], phead: bits[64], m: bits[64]) =
  all l: List[nat], k: nat. list_at(before, objs, phead, l) && k < len(l) && l[k] = uint(m) ->
    list_at(vm, objs, phead, rm_at(l, k)) && rd64(vm, m) = 0 && rd64(vm, m + 8) = 0 && links_only(before, vm, phead, l)

proc[World] dequeue_purpose(phead: bits[64], m: bits[64]) {
  require ex l: List[nat], k: nat. list_at(vm, objs, phead, l) && k < len(l) && l[k] = uint(m)
  either { overflow() } or {
    let before = vm
    havoc vm where dequeued(before, vm, objs, phead, m)
  }
}

// dequeue_head(phead): the list at *phead's first element (0 for an empty
// list) out of it and returned. Its call to dequeue needs the thread
// pointer sound (the ABI's, at every call).
pred is_head(vm: Vm, objs: Set[nat], phead: bits[64], h: bits[64]) =
  all l: List[nat]. list_at(vm, objs, phead, l) -> uint(h) = (if len(l) = 0 { 0 } else { l[0] })
pred head_taken(before: Vm, vm: Vm, objs: Set[nat], phead: bits[64], h: bits[64]) =
  (h = 0 -> vm = before) && (h != 0 -> dequeued(before, vm, objs, phead, h))

proc[World] dequeue_head_purpose(phead: bits[64]) -> bits[64] {
  require (ex l: List[nat]. list_at(vm, objs, phead, l)) && thread_ok(vm, fs_base)
  either { overflow() } or {
    let before = vm
    let h = any bits[64] where is_head(before, objs, phead, h)
    havoc vm where head_taken(before, vm, objs, phead, h)
    return h
  }
}

// set_size(p, end, n), the n bytes at p a block's (or a nested group's) in
// a slot ending at end: the slack after them recorded (`size_ok`), the
// header byte's low 5 bits (the slot's index) kept, no byte but the header
// byte and the slack written. The bytes it writes accessible
// (`set_size_pre`, as its code writes them).
pred size_set(before: Vm, vm: Vm, p: bits[64], end: bits[64], n: bits[64]) =
  (vm with { bytes: before.bytes }) = before &&
  size_ok(mview(vm, all_bytes()), uint(p), uint(end), uint(n)) &&
  bytes_at(vm, p - 3, 1) % 32 = bytes_at(before, p - 3, 1) % 32 &&
  (all a: nat. a < 2^64 && a != uint(p) - 3 && !(uint(p) + uint(n) <= a && a < uint(end)) ->
     vm.bytes[bits[64](a)] = before.bytes[bits[64](a)])

proc[World] set_size_purpose(p: bits[64], end: bits[64], n: bits[64]) {
  require set_size_pre(vm, objs, p, end, n)
  either { overflow() } or {
    let before = vm
    havoc vm where size_set(before, vm, p, end, n)
  }
}

// get_slot_index(p), p where a client block or a nested group starts: the
// index of its slot in its group
proc[MallocAbs] get_slot_index_purpose(c: Cfg, p: bits[64]) -> bits[32] {
  require holds_in(c, A, vm, blocks) && no_reserved(A) && (ex g: nat, i: nat. starts_at(A, g, i, uint(p)))
  either { overflow() } or {
    return any i: bits[32] where ex g: nat. starts_at(A, g, uint(i), uint(p))
  }
}

// get_meta(p), p where a client block or a nested group starts: the meta
// of its group (the thread pointer sound: get_meta's checks may call
// a_crash)
proc[MallocAbs] get_meta_purpose(c: Cfg, p: bits[64]) -> bits[64] {
  require holds_in(c, A, vm, blocks) && no_reserved(A) && thread_ok(vm, fs_base) && (ex g: nat, i: nat. starts_at(A, g, i, uint(p)))
  either { overflow() } or {
    return any m: bits[64] where ex i: nat. starts_at(A, uint(m), i, uint(p))
  }
}

// __malloc_allzerop(p), p where a client block or a nested group starts:
// whether its group is one slot mapped on its own (`own_mapping`)
proc[MallocAbs] allzerop_purpose(c: Cfg, p: bits[64]) -> bits[32] {
  require holds_in(c, A, vm, blocks) && no_reserved(A) && thread_ok(vm, fs_base) && (ex g: nat, i: nat. starts_at(A, g, i, uint(p)))
  either { overflow() } or {
    return any r: bits[32] where ex g: nat, i: nat. starts_at(A, g, i, uint(p)) &&
      (own_mapping(A.metas[g]) && r = 1 || !own_mapping(A.metas[g]) && r = 0)
  }
}

// slot i of the group v framed for n bytes at p: the frame (`frame_ok`),
// no byte outside the slot's interior written, nothing else changed
pred framed(before: Vm, vm: Vm, v: MetaV, i: nat, p: nat, n: nat) =
  (vm with { bytes: before.bytes }) = before &&
  frame_ok(mview(vm, all_bytes()), v, i, p, n, 0) &&
  (all a: nat. a < 2^64 && !in_slot(v, i, a) -> vm.bytes[bits[64](a)] = before.bytes[bits[64](a)])

// enframe(g, idx, n, ctr), slot idx of the group g the one reserved, its
// bytes accessible to the caller (`slot_rw`), room in it for n bytes and
// the in-band header: the slot framed for a block of n bytes at some p in
// it (`frame_ok`), p returned; only the slot's interior written. Which p
// -- the offset, in units, a byte musl cycles -- left free. The caller's
// part: for a size class, p within the class's slot wherever it lies; the
// thread pointer's word apart from the slot; a stride below 2^31.
proc[MallocAbs] enframe_purpose(c: Cfg, g: bits[64], idx: bits[32], n: bits[64]) -> bits[64] {
  require holds_in(c, A, vm, blocks) && thread_ok(vm, fs_base) && is_used(A, uint(g)) && reserved_only(A, uint(g), uint(idx)) &&
    slot_rw(vm, A.metas[uint(g)], uint(idx)) &&
    uint(n) + IB <= stride(A.metas[uint(g)]) && stride(A.metas[uint(g)]) < 2^31 &&
    (A.metas[uint(g)].sizeclass < 48 ->
       slot_end(A.metas[uint(g)], uint(idx)) - uint(n) - storage(A.metas[uint(g)]) < UNIT * size_classes[A.metas[uint(g)].sizeclass] * (uint(idx) + 1)) &&
    (uint(fs_base) + 8 <= slot_start(A.metas[uint(g)], uint(idx)) - IB || slot_end(A.metas[uint(g)], uint(idx)) <= uint(fs_base))
  either { overflow() } or {
    let before = vm
    let p = any q: bits[64] where slot_start(A.metas[uint(g)], uint(idx)) <= uint(q) &&
      (uint(q) - slot_start(A.metas[uint(g)], uint(idx))) % UNIT = 0 && uint(q) < slot_start(A.metas[uint(g)], uint(idx)) + 256 * UNIT &&
      uint(q) + uint(n) <= slot_end(A.metas[uint(g)], uint(idx))
    havoc vm where framed(before, vm, A.metas[uint(g)], uint(idx), uint(p), uint(n))
    return p
  }
}

// get_stride(g), g a group in use: its slots' size
proc[MallocAbs] get_stride_purpose(c: Cfg, g: bits[64]) -> bits[64] {
  require holds_in(c, A, vm, blocks) && is_used(A, uint(g))
  either { overflow() } or { return bits[64](stride(A.metas[uint(g)])) }
}

// try_avail(pm), pm class sc's active list: a free slot of a group already
// there. Its bit (1 << i) returned, slot i of the list's head reserved --
// the head now, if need be: the list reorganised --; or 0, no group of the
// list with a free slot (the list then empty). A runs out of stack, if it
// does, with the memory arbitrary.
proc[MallocAbs] try_avail_purpose(c: Cfg, sc: nat, pm: bits[64]) -> bits[32] {
  require holds_in(c, A, vm, blocks) && no_reserved(A) && thread_ok(vm, fs_base) &&
    sc < 48 && uint(pm) = c.ctx + C_ACTIVE + 8 * sc
  either { overflow() } or {
    let A0 = A
    let before = vm
    ghost A := any A2: Abs where reorganised(A0, A2, sc)
    let r = any r: bits[32] where (
      (r = 0 && len(A.active[sc]) = 0 && (all g: nat. on_list(A0.active[sc], g) -> !has_unused(A0, g))) ||
      (ex i: nat. i < 32 && uint(r) = 2^i && len(A.active[sc]) > 0 && reserves(A0, A, A.active[sc][0], i)))
    havoc vm where holds_in(c, A, vm, blocks) && untouched(c, A0, blocks, before, vm, {})
    return r
  }
}

// alloc_slot(sc, req): a slot for a block of req bytes in class sc. Its
// index i returned, slot i of the head of class sc's active list reserved
// (an existing group's free slot, or a new group's: mapped, or nested in a
// slot of a larger class), room in it for req bytes and the in-band
// header; or -1, out of memory. The allocator may take memory that was
// unmapped (a new group, a meta area) and set errno (a failed mmap).
proc[MallocAbs] alloc_slot_purpose(c: Cfg, sc: bits[32], req: bits[64]) -> bits[32] {
  require holds_in(c, A, vm, blocks) && no_reserved(A) && thread_ok(vm, fs_base) &&
    uint(sc) < 48 && uint(req) + IB <= UNIT * size_classes[uint(sc)]
  either { overflow() } or {
    let A0 = A
    let before = vm
    let errno = {a: nat | uint(fs_base) + 0x34 <= a && a < uint(fs_base) + 0x38}
    ghost A := any A2: Abs where true
    let r = any r: bits[32] where (
      (r = bits[32](2^32 - 1) && no_reserved(A)) ||
      (uint(r) < 32 && len(A.active[uint(sc)]) > 0 && reserved_only(A, A.active[uint(sc)][0], uint(r)) &&
       A.metas[A.active[uint(sc)][0]].sizeclass = uint(sc) &&
       uint(req) + IB <= stride(A.metas[A.active[uint(sc)][0]])))
    havoc vm where holds_in(c, A, vm, blocks) && untouched(c, A0, blocks, before, vm, errno) &&
      (all a: nat. a in footprint(c, A, blocks) -> a in footprint(c, A0, blocks) || !mapped(before, a / PAGE))
    return r
  }
}

// ... as C function values (the result as GIMPLE returns it: `result`)
fn set_size_purpose_fun() -> CFun2[World] = (args: Args) => {
  require len(args) >= 3
  set_size_purpose(bits[64](args[0]), bits[64](args[1]), bits[64](args[2]))
  return (any bits[64], any bits[64])
}

fn dequeue_purpose_fun() -> CFun2[World] = (args: Args) => {
  require len(args) >= 2
  dequeue_purpose(bits[64](args[0]), bits[64](args[1]))
  return (any bits[64], any bits[64])
}

fn dequeue_head_purpose_fun() -> CFun2[World] = (args: Args) => {
  require len(args) >= 1
  let r = dequeue_head_purpose(bits[64](args[0]))
  let w = result[64](r)
  return (w, any bits[64])
}

fn get_slot_index_purpose_fun(c: Cfg) -> CFun2[MallocAbs] = (args: Args) => {
  require len(args) >= 1
  let r = get_slot_index_purpose(c, bits[64](args[0]))
  let w = result[32](r)
  return (w, any bits[64])
}

fn get_meta_purpose_fun(c: Cfg) -> CFun2[MallocAbs] = (args: Args) => {
  require len(args) >= 1
  let r = get_meta_purpose(c, bits[64](args[0]))
  let w = result[64](r)
  return (w, any bits[64])
}

fn allzerop_purpose_fun(c: Cfg) -> CFun2[MallocAbs] = (args: Args) => {
  require len(args) >= 1
  let r = allzerop_purpose(c, bits[64](args[0]))
  let w = result[32](r)
  return (w, any bits[64])
}

fn enframe_purpose_fun(c: Cfg) -> CFun2[MallocAbs] = (args: Args) => {
  require len(args) >= 4
  let r = enframe_purpose(c, bits[64](args[0]), bits[32](args[1]), bits[64](args[2]))
  let w = result[64](r)
  return (w, any bits[64])
}

fn get_stride_purpose_fun(c: Cfg) -> CFun2[MallocAbs] = (args: Args) => {
  require len(args) >= 1
  let r = get_stride_purpose(c, bits[64](args[0]))
  let w = result[64](r)
  return (w, any bits[64])
}

fn try_avail_purpose_fun(c: Cfg) -> CFun2[MallocAbs] = (args: Args) => {
  require len(args) >= 1 && (uint(args[0]) - c.ctx - C_ACTIVE) % 8 = 0
  let r = try_avail_purpose(c, (uint(args[0]) - c.ctx - C_ACTIVE) / 8, args[0])
  let w = result[32](r)
  return (w, any bits[64])
}

fn alloc_slot_purpose_fun(c: Cfg) -> CFun2[MallocAbs] = (args: Args) => {
  require len(args) >= 2
  let r = alloc_slot_purpose(c, bits[32](args[0]), args[1])
  let w = result[32](r)
  return (w, any bits[64])
}
