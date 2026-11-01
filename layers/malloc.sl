layer malloc uses abi

// The glibc allocator interface: malloc, free, calloc (x86_64, single thread).
//
// The heap is ghost state: the set of live blocks. The allocator's own data
// (arenas, chunk headers, bins, free chunks) is hidden behind a *parameter*
// `alloc_inv`, constrained only by laws. Client proofs hold for any allocator
// satisfying the laws; proving glibc's machine code `implements` these specs
// supplies the concrete definition (`instance`).

///////////////////////////////////////////////////////////////////////
//  Abstract heap

state Heap extends World {
  ghost blocks : Addr -> Option[nat]      // live blocks: start -> usable size
}

fn range(p: Addr, n: nat) -> Set[nat] = {a: nat | uint(p) <= a && a < uint(p) + n}
pred disjoint(x: Set[nat], y: Set[nat]) = all a: nat. !(a in x && a in y)

// all bytes of live blocks
fn live_of(b: Addr -> Option[nat]) -> Set[nat] = {a: nat | ex p: Addr. b[p] != none && a in range(p, b[p].value)}
fn live(s: Heap) -> Set[nat] = live_of(s.blocks)

pred rw_mapped(vm: Vm, a: nat) =
  mapped(vm, a / PAGE) && vm.pages[a / PAGE].value.prot.r && vm.pages[a / PAGE].value.prot.w

// A block's place: its usable bytes, at least one -- a block of usable size
// 0 (malloc(0)'s, which C lets have no usable byte) still has a place of
// its own, so blocks live at once are distinct and none lies inside
// another. Its extra byte is not the client's (`live` is the usable bytes).
fn extent(n: nat) -> nat = if n = 0 { 1 } else { n }

// A live block at p of usable size n is well placed.
pred block_wf(b: Addr -> Option[nat], p: Addr, n: nat) =
  p != 0 && uint(p) % 16 = 0 &&                           // 16-byte aligned
  (all q: Addr. q != p && b[q] != none ->                  // blocks' places are disjoint
     disjoint(range(p, extent(n)), range(q, extent(b[q].value))))

pred blocks_wf(b: Addr -> Option[nat]) =
  all p: Addr. b[p] != none -> block_wf(b, p, b[p].value)

// every live block is mapped read-write
pred live_rw(s: Heap) =
  all p: Addr. s.blocks[p] != none -> all a: nat. uint(p) <= a && a < uint(p) + s.blocks[p].value -> rw_mapped(s.vm, a)

// What every valid heap satisfies: well-placed blocks, mapped read-write.
pred heap_wf(s: Heap) = blocks_wf(s.blocks) && live_rw(s)

///////////////////////////////////////////////////////////////////////
//  The allocator's private state: parameters and laws

// the allocator's data structures are intact and describe `blocks`
param pred alloc_inv(s: Heap)

// the bytes the allocator owns: its metadata and free memory (and code)
param fn alloc_owned(s: Heap) -> Set[nat]

// Where this libc keeps errno: an offset from the thread pointer (musl on
// x86_64: `errno_val` in `struct pthread`, 0x34). Fixed by the claim.
param fn errno_offset(u: ()) -> nat

// The program as loaded: its code (bytes `prog_code` at `prog_base`) and
// its static data (`prog_statics`, off the stack's space). Fixed by the
// claim.
param fn prog_base(u: ()) -> nat
param fn prog_code(u: ()) -> List[bits[8]]
param fn prog_statics(u: ()) -> Set[nat]

// What any allocator may assume of the world at its calls: the ABI's view
// of a caller's memory (no stack page among the world's; the C world's
// bytes all but the ABI's), and a process that keeps its thread (the
// thread pointer's descriptor, its stack protector's word in it), its
// break's start (above page 0) and its program loaded.
pred world_ok(s: Heap) =
  (all p: PageNo. s.vm.pages[p] != none -> s.vm.pages[p].value.kind != stack) &&
  s.objs.c_bytes = {a: nat | a notin canary(s.fs_base)} &&
  thread_ok(s.vm, s.fs_base) && canary_ok(s.vm, s.fs_base) && brk_start_ok(s.vm) &&
  loaded(s.vm, prog_base(()), prog_code(()), prog_statics(()))

law inv_wf(s: Heap): alloc_inv(s) -> heap_wf(s)

law owned_private(s: Heap): alloc_inv(s) -> disjoint(alloc_owned(s), live(s))

// (owned memory is mapped -- or a live stack object of the world: the
// program's data on the initial stack, which the C world sees only so)
law owned_mapped(s: Heap): alloc_inv(s) -> all a: nat. a in alloc_owned(s) -> mapped(s.vm, a / PAGE) || a in s.objs.live

// The invariant depends only on what the allocator controls: a client that
// changes other memory keeps it (and cannot corrupt the heap). The client
// may write the bytes of its blocks, but their mappings (pages) stay under
// the allocator's control, as does all of the allocator's own memory and
// the program break (an allocator may extend it; musl's sbrk refuses to
// move it). The thread pointer and the stack's place are the process's,
// no client's to change; owned bytes that are stack objects (the initial
// stack's data) stay live.
law frame(s: Heap, t: Heap):
  alloc_inv(s) && t.blocks = s.blocks && t.vm.brk = s.vm.brk &&
  t.fs_base = s.fs_base && t.vm.stack_top = s.vm.stack_top && t.vm.stack_limit = s.vm.stack_limit &&
  (all a: nat. a in alloc_owned(s) ->
     t.vm.bytes[bits[64](a)] = s.vm.bytes[bits[64](a)] &&
     t.vm.pages[a / PAGE] = s.vm.pages[a / PAGE]) &&
  (all a: nat. a in alloc_owned(s) && a in s.objs.live -> a in t.objs.live) &&
  (all a: nat. a in live(s) -> t.vm.pages[a / PAGE] = s.vm.pages[a / PAGE]) ->
  alloc_inv(t) && alloc_owned(t) = alloc_owned(s)

// A client write into allocator-owned memory (overflowing a block, writing a
// freed block), or an munmap / mprotect of a block's pages, is not forbidden
// by the machine; it may break `alloc_inv`, and the next allocator call is
// then `undefined` -- heap corruption.

///////////////////////////////////////////////////////////////////////
//  Allocator steps

fn errno_bytes(s: Heap) -> Set[nat] = range(s.fs_base + bits[64](errno_offset(())), 4)

// errno can be read and written (the allocator saves, restores and sets it)
pred errno_ok(s: Heap) = all a: nat. a in errno_bytes(s) -> rw_mapped(s.vm, a)

// Memory the allocator may touch in a call: what it owns, what was unmapped
// (it may map more with mmap/brk), and `extra` (a block being freed, errno).
// Everything else -- client memory, live blocks, the stack -- is unchanged.
pred alloc_frame(s: Heap, vm2: Vm, extra: Set[nat]) =
  (all a: nat. a notin alloc_owned(s) && a notin extra && mapped(s.vm, a / PAGE) ->
     vm2.bytes[bits[64](a)] = s.vm.bytes[bits[64](a)] &&
     vm2.pages[a / PAGE] = s.vm.pages[a / PAGE]) &&
  vm2.stack_top = s.vm.stack_top && vm2.stack_limit = s.vm.stack_limit &&
  vm2.brk_start = s.vm.brk_start

// A step of the allocator from `before` to `after`: it reorganises its
// memory; afterwards its invariant holds (so every live block, a new one
// too, is mapped read-write: inv_wf), and it owns nothing new except fresh
// mappings and `extra`.
pred step_ok(before: Heap, after: Heap, extra: Set[nat]) =
  alloc_frame(before, after.vm, extra) && alloc_inv(after) &&
  (all a: nat. a in alloc_owned(after) ->
     a in alloc_owned(before) || a in extra || !mapped(before.vm, a / PAGE))

proc allocator_step(before: Heap, extra: Set[nat]) {
  havoc vm where step_ok(before, self, extra)
}

// the blocks with p set to v
fn set_block(b: Addr -> Option[nat], p: Addr, v: Option[nat]) -> Addr -> Option[nat] =
  (q: Addr) => if q = p { v } else { b[q] }

// Freeing a live block is always possible: the allocator can take it back.
// (Without this, a free with no possible step would be `undefined`, and
// the implementation could do anything there.)
law free_step(s: Heap, p: Addr):
  alloc_inv(s) && s.blocks[p] != none ->
    ex vm: Vm. step_ok(s, (s with { blocks: set_block(s.blocks, p, none) }) with { vm: vm }, range(p, s.blocks[p].value))

proc set_errno(e: nat) {
  let a = fs_base + bits[64](errno_offset(()))
  for i in 0..4 { vm.bytes[a + bits[64](i)] := bits[8](e / 256^i) }
}

// a new block: not a live one, its place only from allocator memory or
// fresh mappings
pred fresh_block(s: Heap, p: Addr, n: nat) =
  s.blocks[p] = none &&
  (all a: nat. a in range(p, extent(n)) -> a in alloc_owned(s) || !mapped(s.vm, a / PAGE))

///////////////////////////////////////////////////////////////////////
//  malloc, free, calloc

// malloc and calloc may change errno (C allows it even on success); on
// failure it is ENOMEM. free preserves errno.

// failing: the allocator may still tidy up (memory unchanged is always a
// possible step: malloc.idle_step, proofs/malloc_client.core), errno is ENOMEM
proc out_of_memory(before: Heap) -> Addr {
  allocator_step(before, errno_bytes(before))
  set_errno(ENOMEM)
  return 0
}

// malloc may always fail; it must fail when no block can be handed out: a
// place for it (allocator memory or fresh mappings) and an allocator state
// that includes it.
proc malloc(n: bits[64]) -> Addr {
  require alloc_inv(self) && errno_ok(self) && world_ok(self)
  let before = self
  // malloc(0): a unique block (its place `extent`'s), maybe no usable byte
  let size  = any? nat where size >= uint(n) else { return out_of_memory(before) }
  let p     = any Addr where p != 0 && uint(p) % 16 = 0 && fresh_block(before, p, size)
                else { return out_of_memory(before) }
  let grown = before with { blocks: set_block(before.blocks, p, some(size)) }
  let vm2   = any Vm where step_ok(before, grown with { vm: vm2 }, errno_bytes(before))
                else { return out_of_memory(before) }
  ghost blocks := grown.blocks
  vm := vm2                                     // contents of the block: arbitrary
  return p
}

proc free(p: Addr) {
  require world_ok(self)                        // the process at any call (its program loaded)
  if p = 0 { return }
  require alloc_inv(self) && errno_ok(self)
  require blocks[p] != none                     // invalid or double free: undefined
  let before = self
  let freed  = range(p, blocks[p].value)
  ghost blocks := set_block(blocks, p, none)
  allocator_step(before, freed)                 // the block's memory returns to the allocator (law free_step)
}

proc calloc(count: bits[64], size: bits[64]) -> Addr {
  require alloc_inv(self) && errno_ok(self) && world_ok(self)
  let n = uint(count) * uint(size)
  if n >= 2^64 {                                // overflow
    set_errno(ENOMEM)
    return 0
  }
  let p = malloc(bits[64](n))
  if p != 0 {
    for i in 0..n { vm.bytes[p + bits[64](i)] := 0 }
  }
  return p
}

// realloc: next step (in-place growth vs. move-and-copy; realloc(p, 0) frees
// in glibc).

///////////////////////////////////////////////////////////////////////
//  Connection to machine code

// The C-level specs above, as ABI function specs (arguments from registers;
// a call passes them all -- with fewer, the registers read are no
// argument's: undefined).
fn malloc_fun() -> CFun[Heap] = (args: Args) => { require len(args) >= 1; return malloc(args[0]) }
fn free_fun()   -> CFun[Heap] = (args: Args) => { require len(args) >= 1; free(args[0]); return any bits[64] }
fn calloc_fun() -> CFun[Heap] = (args: Args) => { require len(args) >= 2; return calloc(args[0], args[1]) }

// What must be proven about a concrete libc binary (see claim_malloc.sl):
// malloc and free. (calloc's spec above is not claimed yet: musl's calloc
// skips clearing a block whose group has its own mapping, which needs
// malloc to promise such a block's bytes zero -- later, with realloc.)
pred allocator_correct(malloc_at: Addr, free_at: Addr) =
  implements(malloc_at, malloc_fun()) &&
  implements(free_at, free_fun())
