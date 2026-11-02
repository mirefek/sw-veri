layer test_malloc uses gimple, abi, malloc

// Specs of the test program's functions (tests/test_malloc.c): each a
// contract (abi.sl) by its purpose. Block i of the test has size(i) bytes,
// filled with its pattern pat(i, j); main returns 0 when every block kept
// its pattern, 1 when malloc returned NULL -- never 42 (a pattern changed).

fn pat_of(i: nat, j: nat) -> nat = (31 * i + j) % 256
fn size_of(i: nat) -> nat = 16 + 40 * i

// the test's blocks are numbered 0 .. 7
const NBLK: nat = 8

///////////////////////////////////////////////////////////////////////
//  pat(i, j), size(i)

proc[World] pat_spec(i: bits[32], j: bits[32]) -> bits[32] {
  require uint(i) < NBLK && uint(j) < size_of(NBLK)
  either { overflow() } or { return bits[32](pat_of(uint(i), uint(j))) }
}

fn pat_spec_fun() -> CFun2[World] = (args: Args) => {
  require len(args) >= 2
  let r = pat_spec(bits[32](args[0]), bits[32](args[1]))
  let w = result[32](r)
  return (w, any bits[64])
}

proc[World] size_spec(i: bits[32]) -> bits[32] {
  require uint(i) < NBLK
  either { overflow() } or { return bits[32](size_of(uint(i))) }
}

fn size_spec_fun() -> CFun2[World] = (args: Args) => {
  require len(args) >= 1
  let r = size_spec(bits[32](args[0]))
  let w = result[32](r)
  return (w, any bits[64])
}

///////////////////////////////////////////////////////////////////////
//  fill(b, i), intact(b, i)

// block i's bytes at b: usable (for writing: w), low enough for pointer
// arithmetic
pred blk_usable(vm: Vm, objs: Objs, b: Addr, i: nat, w: bool) =
  b != 0 && uint(b) + size_of(i) < 2^63 && (all j: nat. j < size_of(i) -> usable(vm, objs, uint(b) + j, 1, w))

// block i's pattern at b
pred has_pat(vm: Vm, b: Addr, i: nat) = all j: nat. j < size_of(i) -> bytes_at(vm, b + bits[64](j), 1) = pat_of(i, j)

// fill(b, i): block i's pattern written at b, nothing else changed
proc[World] fill_spec(b: Addr, i: bits[32]) {
  require uint(i) < NBLK && blk_usable(vm, objs, b, uint(i), true)
  either { overflow() } or {
    let before = vm
    havoc vm where (vm with { bytes: before.bytes }) = before && has_pat(vm, b, uint(i)) &&
      (all a: nat. !(uint(b) <= a && a < uint(b) + size_of(uint(i))) -> vm.bytes[bits[64](a)] = before.bytes[bits[64](a)])
  }
}

fn fill_spec_fun() -> CFun2[World] = (args: Args) => {
  require len(args) >= 2
  fill_spec(bits[64](args[0]), bits[32](args[1]))
  return (any bits[64], any bits[64])
}

// intact(b, i): 1 when block i's pattern is at b, else 0
proc[World] intact_spec(b: Addr, i: bits[32]) -> bits[32] {
  require uint(i) < NBLK && blk_usable(vm, objs, b, uint(i), false)
  either { overflow() } or {
    if has_pat(vm, b, uint(i)) { return 1 }
    return 0
  }
}

fn intact_spec_fun() -> CFun2[World] = (args: Args) => {
  require len(args) >= 2
  let r = intact_spec(bits[64](args[0]), bits[32](args[1]))
  let w = result[32](r)
  return (w, any bits[64])
}

///////////////////////////////////////////////////////////////////////
//  main()

// what main leaves as it was: the memory outside the allocator's and
// errno (what the exit path reads -- its statics), its pages
pred main_frame(s0: Heap, t: Heap) =
  all a: nat. a notin alloc_owned(s0) && a notin errno_bytes(s0) && mapped(s0.vm, a / PAGE) ->
    t.vm.bytes[bits[64](a)] = s0.vm.bytes[bits[64](a)] && t.vm.pages[a / PAGE] = s0.vm.pages[a / PAGE]

// main(), from the allocator's start (no blocks, as startup leaves it):
// 0 or 1 -- never 42, no block's pattern changed --, the process as any
// call needs it, the memory outside the allocator's as it was
proc[Heap] main_spec() -> bits[32] {
  require alloc_inv(self) && errno_ok(self) && world_ok(self) && (all p: Addr. blocks[p] = none)
  either { overflow() } or {
    let before = self
    ghost blocks := any b: Addr -> Option[nat]
    havoc vm where world_ok(self) && main_frame(before, self)
    return any r: bits[32] where r = 0 || r = 1
  }
}

fn main_spec_fun() -> CFun2[Heap] = (args: Args) => {
  let r = main_spec()
  let w = result[32](r)
  return (w, any bits[64])
}
