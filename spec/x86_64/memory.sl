spec x86_64_linux

// Virtual memory of a Linux process, as seen from user mode

const PAGE           : nat = 4096
const TASK_SIZE      : nat = 2^47 - PAGE      // highest user address + 1
const STACK_GUARD_GAP: nat = 256 * PAGE       // Linux default `stack_guard_gap`

type PageNo = {p: nat | p < TASK_SIZE / PAGE}

pred canonical(a: Addr) = uint(a) < 2^47 || uint(a) >= 2^64 - 2^47

record Prot { r, w, x : bool }
enum   Kind { anon, heap, stack }
record Page { prot: Prot, kind: Kind }

enum Access { read, write, exec }

record Vm {
  pages       : PageNo -> Option[Page]   // VMAs = maximal runs of equal pages
  bytes       : Addr -> bits[8]          // contents (irrelevant where unmapped)
  stack_top   : Addr                     // end of the main stack region, set at exec
  stack_limit : nat                      // RLIMIT_STACK in bytes
  brk_start   : Addr
  brk         : Addr
}

///////////////////////////////////////////////////////////////////////
//  Pure helpers

fn page_of(a: Addr) -> nat = uint(a) / PAGE

pred accessible(p: Prot) = p.r || p.w || p.x

// what the page tables allow for a mapping with protection p (the kernel
// maps any accessible memory readable)
pred hw_allows(p: Prot, acc: Access) = match acc { read => accessible(p), write => p.w, exec => p.x }

pred mapped(vm: Vm, p: nat) = p < TASK_SIZE / PAGE && vm.pages[p] != none

// the first mapped page >= p, if any
fn next_mapped(vm: Vm, p: nat) -> Option[nat] =
  if ex q: nat. q >= p && mapped(vm, q) { some(min({q: nat | q >= p && mapped(vm, q)})) } else { none }

// the last mapped page < p, if any
fn prev_mapped(vm: Vm, p: nat) -> Option[nat] =
  if ex q: nat. q < p && mapped(vm, q) { some(max({q: nat | q < p && mapped(vm, q)})) } else { none }

// end (exclusive, in pages) of the run of equal pages containing q
fn run_end(vm: Vm, q: nat) -> nat =
  min({e: nat | e > q && vm.pages[e] != vm.pages[q]})

// little-endian read of n bytes
fn le(b: Addr -> bits[8], a: Addr, n: nat) -> bits[8*n] =
  bits[8*n](sum i in 0..n. uint(b[a + bits[64](i)]) * 256^i)

///////////////////////////////////////////////////////////////////////
//  Stack space: for reasoning about faults, not used by the machine itself
//
//  The main stack may grow down to `stack_top - stack_limit`. Running out
//  of stack faults just below that floor, in the guard gap; the program can
//  compute both regions (initial rsp / /proc/self/maps, getrlimit).

fn stack_floor(vm: Vm) -> int = uint(vm.stack_top) - vm.stack_limit

// the addresses the main stack may ever occupy
pred stack_space(vm: Vm, a: Addr) =
  stack_floor(vm) <= uint(a) && uint(a) < uint(vm.stack_top)

// where a fault from exhausting the stack lands
pred below_stack_space(vm: Vm, a: Addr) =
  stack_floor(vm) - STACK_GUARD_GAP <= uint(a) && uint(a) < stack_floor(vm)

// Example of use in a contract (the exceptional outcome keeps the state):
//   raises segv(a, _) only if below_stack_space(vm, a)
// "this function may crash only by running out of stack".

///////////////////////////////////////////////////////////////////////
//  Page access, faults, and stack growth

// Make sure the page containing `a` can be accessed; grow the stack if
// Linux would. Fails with `segv`.
proc touch(a: Addr, acc: Access) {
  let p = page_of(a)
  if !mapped(vm, p) {
    if uint(a) >= 2^47 && uint(a) < 2^64 - 2^47 { raise segv(0, kernel) }  // non-canonical: #GP
    if p >= TASK_SIZE / PAGE { raise segv(a, maperr) }                      // kernel half
    grow_stack(a, p)
  }
  let prot = vm.pages[p].value.prot
  // x86 pages can be read whenever they are mapped with any permission;
  // execute-only mappings are made unreadable with a protection key
  if acc != exec && !prot.r && !prot.w && prot.x && cpu.pku { raise segv(a, pkuerr) }
  if !hw_allows(prot, acc) { raise segv(a, accerr) }
}

// Linux `expand_downwards`: an unmapped access just below a stack VMA
// extends the VMA down to the faulting page.
proc grow_stack(a: Addr, p: nat) {
  let above = next_mapped(vm, p)
  if above = none || vm.pages[above.value].value.kind != stack { raise segv(a, maperr) }
  let q   = above.value
  let top = run_end(vm, q)
  if (top - p) * PAGE > vm.stack_limit { raise segv(a, maperr) }
  match prev_mapped(vm, p) {
    some(b) => if accessible(vm.pages[b].value.prot) && (p - (b + 1)) * PAGE < STACK_GUARD_GAP {
                 raise segv(a, maperr)
               }
    none    => {}
  }
  either { raise segv(a, maperr) }                  // out of memory
  or {
    for i in p..q { vm.pages[i] := vm.pages[q] }
    for i in p * PAGE .. q * PAGE { vm.bytes[bits[64](i)] := 0 }
  }
}

proc touch_range(a: Addr, n: nat, acc: Access) {
  for i in 0..n { touch(a + bits[64](i), acc) }
}

// n bytes of memory at `a`, little-endian
view mem(a: Addr, n: nat) : bits[8*n] {
  get {
    touch_range(a, n, read)
    return le(vm.bytes, a, n)
  }
  set(v) {
    touch_range(a, n, write)
    for i in 0..n { vm.bytes[a + bits[64](i)] := v[8*i+7 : 8*i] }
  }
}
