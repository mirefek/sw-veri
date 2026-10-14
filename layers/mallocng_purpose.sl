layer mallocng_purpose uses gimple, abi, mallocng

// Specs of mallocng's internal functions by their purpose: what each is
// for in the abstract state (layers/mallocng.sl's `Abs`, a ghost of the C
// world), not how musl's code does it. Each a contract (layers/abi.sl): a
// precondition, then a stack overflow or the effect. Their C2: from the
// function's memory-level spec (layers/mallocng_specs.sl, or the code's
// effect), `refines_ghost` (proofs/mallocng_purpose.core).

// The state of the allocator's internal functions: the C world, the
// client's blocks (malloc's ghost), and the abstract state A (a ghost the
// specs update; the invariant, where a spec requires it, ties it to memory).
// A spec may read both: the memory where that is its purpose, A where
// that is.
state MallocAbs extends Heap {
  ghost A : Abs
}

// get_slot_index(p), p where a client block or a nested group starts: the
// index of its slot in its group
proc[MallocAbs] get_slot_index_purpose(c: Cfg, p: bits[64]) -> bits[32] {
  require holds_in(c, A, vm, blocks) && (ex g: nat, i: nat. starts_at(A, g, i, uint(p)))
  either { overflow() } or {
    return any i: bits[32] where ex g: nat. starts_at(A, g, uint(i), uint(p))
  }
}

// get_meta(p), p where a client block or a nested group starts: the meta
// of its group (the thread pointer sound: get_meta's checks may call
// a_crash)
proc[MallocAbs] get_meta_purpose(c: Cfg, p: bits[64]) -> bits[64] {
  require holds_in(c, A, vm, blocks) && thread_ok(vm, fs_base) && (ex g: nat, i: nat. starts_at(A, g, i, uint(p)))
  either { overflow() } or {
    return any m: bits[64] where ex i: nat. starts_at(A, uint(m), i, uint(p))
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
