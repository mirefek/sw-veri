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

// A live block at p of usable size n is well placed.
pred block_wf(b: Addr -> Option[nat], p: Addr, n: nat) =
  p != 0 && uint(p) % 16 = 0 &&                           // 16-byte aligned
  (all q: Addr. q != p && b[q] != none ->                  // blocks are disjoint
     disjoint(range(p, n), range(q, b[q].value)))

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

law inv_wf(s: Heap): alloc_inv(s) -> heap_wf(s)

law owned_private(s: Heap): alloc_inv(s) -> disjoint(alloc_owned(s), live(s))

law owned_mapped(s: Heap): alloc_inv(s) -> all a: nat. a in alloc_owned(s) -> mapped(s.vm, a / PAGE)

// The invariant depends only on what the allocator controls: a client that
// changes other memory keeps it (and cannot corrupt the heap). The client
// may write the bytes of its blocks, but their mappings (pages) stay under
// the allocator's control, as does all of the allocator's own memory and
// the program break (an allocator may extend it; musl's sbrk refuses to
// move it).
law frame(s: Heap, t: Heap):
  alloc_inv(s) && t.blocks = s.blocks && t.vm.brk = s.vm.brk &&
  (all a: nat. a in alloc_owned(s) ->
     t.vm.bytes[bits[64](a)] = s.vm.bytes[bits[64](a)] &&
     t.vm.pages[a / PAGE] = s.vm.pages[a / PAGE]) &&
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

// the allocator reorganises its memory; afterwards its invariant holds (so
// every live block, a new one too, is mapped read-write: inv_wf), and it
// owns nothing new except fresh mappings and `extra`
proc allocator_step(before: Heap, extra: Set[nat]) {
  havoc vm where alloc_frame(before, vm, extra) && alloc_inv(self) &&
    (all a: nat. a in alloc_owned(self) ->
       a in alloc_owned(before) || a in extra || !mapped(before.vm, a / PAGE))
}

proc set_errno(e: nat) {
  let a = fs_base + bits[64](errno_offset(()))
  for i in 0..4 { vm.bytes[a + bits[64](i)] := bits[8](e / 256^i) }
}

// a new block may come only from allocator memory or fresh mappings
pred fresh_block(s: Heap, p: Addr, n: nat) =
  all a: nat. a in range(p, n) -> a in alloc_owned(s) || !mapped(s.vm, a / PAGE)

///////////////////////////////////////////////////////////////////////
//  malloc, free, calloc

// malloc and calloc may change errno (C allows it even on success); on
// failure it is ENOMEM. free preserves errno.

proc malloc(n: bits[64]) -> Addr {
  require alloc_inv(self) && errno_ok(self)
  let before = self
  either {
    allocator_step(before, errno_bytes(before))   // may always fail
    set_errno(ENOMEM)
    return 0
  } or {
    // even malloc(0) returns a unique block with usable bytes
    let size = any nat where size >= uint(n) && size >= 1
    let p    = any Addr where p != 0 && uint(p) % 16 = 0 && fresh_block(before, p, size)
    ghost blocks[p] := some(size)
    allocator_step(before, errno_bytes(before))   // contents: arbitrary
    return p
  }
}

proc free(p: Addr) {
  if p = 0 { return }
  require alloc_inv(self) && errno_ok(self)
  require blocks[p] != none                     // invalid or double free: undefined
  let before = self
  let freed  = range(p, blocks[p].value)
  ghost blocks[p] := none
  allocator_step(before, freed)                 // the block's memory returns to the allocator
}

proc calloc(count: bits[64], size: bits[64]) -> Addr {
  require alloc_inv(self) && errno_ok(self)
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

// The C-level specs above, as ABI function specs (arguments from registers).
fn malloc_fun() -> CFun[Heap] = (args: Args) => malloc(args[0])
fn free_fun()   -> CFun[Heap] = (args: Args) => { free(args[0]); return any bits[64] }
fn calloc_fun() -> CFun[Heap] = (args: Args) => calloc(args[0], args[1])

// What must be proven about a concrete libc binary (see claim_malloc.sl).
pred allocator_correct(malloc_at: Addr, free_at: Addr, calloc_at: Addr) =
  implements(malloc_at, malloc_fun()) &&
  implements(free_at, free_fun()) &&
  implements(calloc_at, calloc_fun())
