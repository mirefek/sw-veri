layer mallocng_specs uses gimple, abi

// Specs of mallocng's internal functions on the C world (readable GIMPLE's
// world: memory a partial byte map, `usable` its domain), as contracts
// (layers/abi.sl): a named precondition (`require`: outside it the spec
// allows anything), then a stack overflow or the effect, stated as a
// function of the world. C2 shows the function's readable GIMPLE refines
// its spec (proofs/*_c2.core).

///////////////////////////////////////////////////////////////////////
//  Words

// the 8-byte word at a, as GIMPLE reads it
fn rd64(vm: Vm, a: Addr) -> bits[64] = bits[64](bytes_at(vm, a, 8))

// ... and writes it
fn wr64(vm: Vm, a: Addr, v: bits[64]) -> Vm = vm with { bytes: store_le(vm.bytes, a, 8, uint(v)) }

// the word at p + off: GIMPLE may read and write it (p not null, in the
// address space, usable for reading and writing)
pred word_ok(vm: Vm, objs: Set[nat], p: Addr, off: nat) =
  p != 0 && uint(p) + off + 8 <= 2^64 && usable(vm, objs, uint(p) + off, 8, false) && usable(vm, objs, uint(p) + off, 8, true)

pred al8(p: Addr) = uint(p) % 8 = 0

///////////////////////////////////////////////////////////////////////
//  The active lists: circular, doubly linked through the metas' first two
//  words (struct meta: prev at 0, next at 8)

fn mprev(vm: Vm, m: Addr) -> bits[64] = rd64(vm, m)
fn mnext(vm: Vm, m: Addr) -> bits[64] = rd64(vm, m + 8)

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

proc[World] dequeue_spec(phead: bits[64], m: bits[64]) {
  require dequeue_pre(vm, objs, phead, m)
  either { overflow() } or { vm := dequeue_vm(vm, phead, m) }
}

// ... as a C function value (its register wrapper, as readable GIMPLE has
// C functions: c_mallocng_malloc's dequeue_fun): what its callers' calls
// rely on
fn dequeue_spec_fun() -> CFun2[World] = (args: Args) => {
  require len(args) >= 2
  dequeue_spec(bits[64](args[0]), bits[64](args[1]))
  return (any bits[64], any bits[64])
}

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

proc[World] queue_spec(phead: bits[64], m: bits[64]) {
  require queue_pre(vm, objs, phead, m)
  either { overflow() } or { vm := queue_vm(vm, phead, m) }
}

// ... as a C function value
fn queue_spec_fun() -> CFun2[World] = (args: Args) => {
  require len(args) >= 2
  queue_spec(bits[64](args[0]), bits[64](args[1]))
  return (any bits[64], any bits[64])
}

// dequeue_head(phead): the list's head, dequeued (if any), returned. The
// call to dequeue needs the thread pointer sound (the ABI's, at every
// call).
pred dequeue_head_pre(vm: Vm, objs: Set[nat], fs: Addr, phead: Addr) =
  word_ok(vm, objs, phead, 0) &&
  (rd64(vm, phead) != 0 -> dequeue_pre(vm, objs, phead, rd64(vm, phead)) && thread_ok(vm, fs))
fn dequeue_head_vm(vm: Vm, phead: Addr) -> Vm =
  if rd64(vm, phead) != 0 { dequeue_vm(vm, phead, rd64(vm, phead)) } else { vm }

proc[World] dequeue_head_spec(phead: bits[64]) -> bits[64] {
  require dequeue_head_pre(vm, objs, fs_base, phead)
  either { overflow() } or {
    let m = rd64(vm, phead)
    vm := dequeue_head_vm(vm, phead)
    return m
  }
}

// ... as a C function value: the head in rax (rdx clobbered)
fn dequeue_head_spec_fun() -> CFun2[World] = (args: Args) => {
  require len(args) >= 1
  let r = dequeue_head_spec(bits[64](args[0]))
  return (r, any bits[64])
}

// a_crash (a trap: hlt): calling it is a bug -- its contract undefined, so
// a caller's spec excludes the calls by its precondition
fn a_crash_spec_fun() -> CFun2[World] = (args: Args) => {
  undefined
}
