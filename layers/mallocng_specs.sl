layer mallocng_specs uses gimple, abi

// Specs of mallocng's internal functions on the C world (readable GIMPLE's
// world: memory a partial byte map, `usable` its domain). Each spec is a
// named precondition (`require`: outside it the spec allows anything) and
// an effect, stated as a function of the world. C2 shows the function's
// readable GIMPLE refines its spec (proofs/*_c2.core).

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
  vm := dequeue_vm(vm, phead, m)
}
