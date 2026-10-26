layer mallocng_specs uses gimple, abi, mallocng

// Specs of mallocng's internal functions: what each is for (its purpose),
// in the abstract state (layers/mallocng.sl's `Abs`, a ghost of the C
// world: `MallocAbs`) or on the C world (readable GIMPLE's world: memory a
// partial byte map, `usable` its domain) -- not how musl's code does it.
// Each a contract (layers/abi.sl): a precondition (`require`: outside it
// the spec allows anything), then a stack overflow or the effect. The code
// refines them directly (proofs/mallocng/fun/; the leaf functions':
// proofs/mallocng/code/). Each as a C function value too (its register
// wrapper, as readable GIMPLE has C functions): what its callers' calls
// rely on; written as the code's are (a result through `result[w]`), so
// one lemma per shape relates the two (`g.fun_*`). First, what the code
// does where a proof needs it (its effect: `dequeue_vm`, `step_seq_vm`,
// ...), and the leaf functions.

///////////////////////////////////////////////////////////////////////
//  Words

// the 8-byte word at a, as GIMPLE reads it
fn rd64(vm: Vm, a: Addr) -> bits[64] = bits[64](bytes_at(vm, a, 8))

// ... and writes it
fn wr64(vm: Vm, a: Addr, v: bits[64]) -> Vm = vm with { bytes: store_le(vm.bytes, a, 8, uint(v)) }

// the word at p + off: GIMPLE may read and write it (p not null, in the
// address space, usable for reading and writing)
pred word_ok(vm: Vm, objs: Objs, p: Addr, off: nat) =
  nonnull: p != 0 && bound: uint(p) + off + 8 <= 2^64 &&
  read: usable(vm, objs, uint(p) + off, 8, false) && write: usable(vm, objs, uint(p) + off, 8, true)

pred al8(p: Addr) = uint(p) % 8 = 0

///////////////////////////////////////////////////////////////////////
//  The active lists: circular, doubly linked through the metas' first two
//  words (struct meta: prev at 0, next at 8)

fn mprev(vm: Vm, m: Addr) -> bits[64] = rd64(vm, m)
fn mnext(vm: Vm, m: Addr) -> bits[64] = rd64(vm, m + 8)

// dequeue's effect as its code has it (`ms.dq_run`; its spec:
// dequeue_spec below).
// dequeue(phead, m): m leaves the list *phead -- its neighbours linked to
// each other (if it has any), the head moved past it, its links cleared.
// The words involved: usable, 8-aligned, and apart (the head pointer, m's
// links, and its neighbours' links to it).
pred dequeue_pre(vm: Vm, objs: Objs, phead: Addr, m: Addr) =
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

// queue's conditions and effect as its code has it (`ms.qu_run`; its spec:
// queue_spec below).
// queue(phead, m): m, unlinked (its links 0 -- else a_crash, a bug),
// joins the list *phead: before its head H (at the circular list's end,
// after H's prev P), or as the list's only element. The words involved:
// usable, 8-aligned, and the ones written apart from those read after.
pred queue_pre(vm: Vm, objs: Objs, phead: Addr, m: Addr) =
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
// meta) zeroed (its spec: free_meta_spec
// below)
fn zero_meta(vm: Vm, m: Addr) -> Vm = vm with { bytes: store_le(vm.bytes, m, 40, 0) }

///////////////////////////////////////////////////////////////////////
//  Slots

// a byte, a 32-bit word written
fn wr8(vm: Vm, a: Addr, v: nat) -> Vm = vm with { bytes: store_le(vm.bytes, a, 1, v) }
fn wr32(vm: Vm, a: Addr, v: nat) -> Vm = vm with { bytes: store_le(vm.bytes, a, 4, v) }

// set_size's conditions and effect (`ms.ss_run`; its spec
// below). set_size(p, end, n): a slot's n bytes at p, its end at end; the r = end -
// p - n bytes after them reserved, recorded: the header byte at p - 3 keeps
// its low 5 bits, its top 3 the count -- r, or 5 for r >= 5, the count then
// the 32-bit word at end - 4 and a 0 byte before it; the first reserved
// byte (at p + n), if any, 0. The pointers: below 2^63 (their difference
// signed), p past its header; r below 2^31 (an int).
fn reserved(p: Addr, end: Addr, n: bits[64]) -> int = uint(end) - uint(p) - uint(n)

pred set_size_pre(vm: Vm, objs: Objs, p: Addr, end: Addr, n: bits[64]) =
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
// changed -- in a sound thread (`thread_ok`), errno's cell not wrapping
// around the address space
proc[World] errno_location_spec() -> Addr {
  require uint(fs_base) + 0x38 <= 2^64 && thread_ok(vm, fs_base)
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
pred size_overflows_pre(vm: Vm, objs: Objs, fs: Addr, n: bits[64]) =
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

///////////////////////////////////////////////////////////////////////
//  The system's memory calls, as malloc makes them: what Linux does
//  (spec/linux/process.sl's sys_brk, sys_mmap, sys_mprotect) seen from the
//  C world, through musl's wrappers (errno, -1 on failure)

// (the memory's changes -- fresh_pages, gone_pages, reprot -- are
// layers/gimple.sl's: its system calls' too)

// a 1-argument system call n, as malloc makes one: brk(new)
// (`__syscall1(SYS_brk, new)`): the break moved to new -- the pages up to
// it fresh readable, writable heap if they had to be had and could be
// (free, off the stack's space; the kernel may refuse), the pages above it
// gone if it went down --, or not; the break returned. Not below where it
// started. The pages it gives back the break's own (as the call's,
// `sys_call1`).
proc[World] syscall1_spec(n: bits[64], new: Addr) -> bits[64] {
  require uint(n) = 12 && (pages_for(uint(new)) < pages_for(uint(vm.brk)) -> new >= vm.brk_start ->
    pages_for(uint(vm.brk)) <= TASK_SIZE / PAGE &&
    sys_pages_ok(vm, objs, pages_for(uint(new)), pages_for(uint(vm.brk)) - pages_for(uint(new))) &&
    (all q: nat. pages_for(uint(new)) <= q && q < pages_for(uint(vm.brk)) -> mapped(vm, q) -> vm.pages[q].value.kind = heap))
  either { overflow() } or {
    let before = vm
    let old_end = pages_for(uint(before.brk))
    let new_end = pages_for(uint(new))
    if new < before.brk_start { return before.brk }
    if new_end > old_end {
      if !free_range(before, old_end, new_end - old_end) || !off_stack_space(before, old_end, new_end - old_end) { return before.brk }
      either { return before.brk } or {
        havoc vm where fresh_pages(before, vm, objs, old_end, new_end - old_end, Page { prot: Prot { r: true, w: true, x: false }, kind: heap }) && vm.brk = new else { return before.brk }
        return new
      }
    } else {
      havoc vm where gone_pages(before, vm, new_end, old_end - new_end) && vm.brk = new
      return new
    }
  }
}

fn syscall1_spec_fun() -> CFun2[World] = (args: Args) => {
  require len(args) >= 2
  let r = syscall1_spec(bits[64](args[0]), bits[64](args[1]))
  let w = result[64](r)
  return (w, any bits[64])
}

// a 3-argument system call n, as malloc makes one: mprotect(addr, len,
// prot) (`__syscall3(SYS_mprotect, ..)`) -- the kernel's: the pages from
// addr's for len reprotected up to the first unmapped one, 0 or -ENOMEM
// (addr not page-aligned: -EINVAL). The pages the kernel's to reprotect.
proc[World] syscall3_spec(n: bits[64], addr: Addr, len: bits[64], prot: bits[64]) -> bits[64] {
  require uint(n) = 10 && sys_pages_ok(vm, objs, page_of(addr), pages_for(uint(len)))
  either { overflow() } or { return os_mprotect(addr, len, prot) }
}

fn syscall3_spec_fun() -> CFun2[World] = (args: Args) => {
  require len(args) >= 4
  let r = syscall3_spec(bits[64](args[0]), bits[64](args[1]), bits[64](args[2]), bits[64](args[3]))
  let w = result[64](r)
  return (w, any bits[64])
}

// a 2-argument system call n, as malloc makes one: munmap(addr, len)
// (`__syscall2(SYS_munmap, ..)`) -- the kernel's: the pages from addr's
// for len gone, 0 (-EINVAL: addr not a page's start, len 0, the pages past
// the task's). The pages the kernel's to unmap.
proc[World] syscall2_spec(n: bits[64], addr: Addr, len: bits[64]) -> bits[64] {
  require uint(n) = 11 && sys_pages_ok(vm, objs, page_of(addr), pages_for(uint(len)))
  either { overflow() } or { return os_munmap(addr, len) }
}

fn syscall2_spec_fun() -> CFun2[World] = (args: Args) => {
  require len(args) >= 3
  let r = syscall2_spec(bits[64](args[0]), bits[64](args[1]), bits[64](args[2]))
  let w = result[64](r)
  return (w, any bits[64])
}

// errno's cell writable, the thread pointer sound (a failing call sets it)
pred errno_ok(vm: Vm, objs: Objs, fs: Addr) =
  uint(fs) + 0x38 <= 2^64 && usable(vm, objs, uint(errno_at(fs)), 4, true) && thread_ok(vm, fs)

// errno's value e (a failing allocator call's: ENOMEM)
pred errno_is(vm: Vm, fs: Addr, e: nat) = bytes_at(vm, errno_at(fs), 4) = e

// __syscall_ret(r): a system call's raw result as the C function's -- an
// error (r one of -4095 .. -1): its number -r to errno, -1 returned; else
// r itself. Errno's cell writable on an error.
proc[World] syscall_ret_spec(r: bits[64]) -> bits[64] {
  require uint(r) > 0xfffffffffffff000 -> errno_ok(vm, objs, fs_base)
  either { overflow() } or {
    if uint(r) > 0xfffffffffffff000 {
      vm := wr32(vm, errno_at(fs_base), 2^64 - uint(r))
      return bits[64](2^64 - 1)
    }
    return r
  }
}

fn syscall_ret_spec_fun() -> CFun2[World] = (args: Args) => {
  require len(args) >= 1
  let r = syscall_ret_spec(bits[64](args[0]))
  let w = result[64](r)
  return (w, any bits[64])
}

// a place for mmap's len bytes, page p: at addr if MAP_FIXED; else one
// Linux may pick -- free, off the stack's space when there is no hint,
// never page 0
pred mmap_place(before: Vm, addr: Addr, len: bits[64], flags: bits[32], p: nat) =
  uint(len) != 0 && uint(len) < 2^63 &&
  (if uint(flags) = MAP_PRIVATE + MAP_ANONYMOUS + MAP_FIXED { uint(addr) % PAGE = 0 && p = page_of(addr) && p + pages_for(uint(len)) <= TASK_SIZE / PAGE }
   else { p >= 1 && free_range(before, p, pages_for(uint(len))) && (addr != 0 || off_stack_space(before, p, pages_for(uint(len)))) })

// the pages [p, p + n) neither the thread pointer's nor errno's (a call
// changing them leaves both as they are)
pred tls_off(fs: Addr, p: nat, n: nat) =
  (all i: nat. i < 8 -> !(p <= (uint(fs) + i) / PAGE && (uint(fs) + i) / PAGE < p + n)) &&
  (all i: nat. i < 4 -> !(p <= (uint(errno_at(fs)) + i) / PAGE && (uint(errno_at(fs)) + i) / PAGE < p + n))

// mmap's errno on failure: EINVAL for no length (the kernel's check); else
// ENOMEM (no place, the kernel's refusal, musl's own length check) -- or,
// for a fixed address off a page's start, EINVAL (the kernel may refuse
// first)
pred mmap_err(addr: Addr, len: bits[64], flags: bits[32], e: nat) =
  if uint(len) = 0 { e = EINVAL } else { e = ENOMEM || (uint(flags) = MAP_PRIVATE + MAP_ANONYMOUS + MAP_FIXED && uint(addr) % PAGE != 0 && e = EINVAL) }

// mmap(addr, len, prot, flags, -1, 0), anonymous private memory (at addr
// if MAP_FIXED): len's pages fresh at a place for them (`mmap_place`),
// replacing what was there; or -1, errno as `mmap_err` (no place; the
// kernel may always refuse; musl's own checks), nothing else changed. A
// fixed mapping's pages ones the kernel may replace (sys_pages_ok), not
// the thread pointer's or errno's (`tls_off`: __mmap calls on); else no
// hint (addr 0: Linux places it).
proc[World] mmap_spec(addr: Addr, len: bits[64], prot: bits[32], flags: bits[32], off: bits[64]) -> bits[64] {
  require (uint(flags) = MAP_PRIVATE + MAP_ANONYMOUS || uint(flags) = MAP_PRIVATE + MAP_ANONYMOUS + MAP_FIXED) && uint(prot) < 8 && off = 0 &&
    errno_ok(vm, objs, fs_base) &&
    (if uint(flags) = MAP_PRIVATE + MAP_ANONYMOUS + MAP_FIXED { sys_pages_ok(vm, objs, page_of(addr), pages_for(uint(len))) && tls_off(fs_base, page_of(addr), pages_for(uint(len))) }
     else { uint(addr) = 0 })
  either { overflow() } or {
    let before = vm
    if ex p: nat. mmap_place(before, addr, len, flags, p) {
      either { } or {
        let n = pages_for(uint(len))
        let p = any p: nat where mmap_place(before, addr, len, flags, p)
        havoc vm where fresh_pages(before, vm, objs, p, n, Page { prot: prot_of(bits[64](uint(prot))), kind: anon }) && vm.brk = before.brk else {
          vm := wr32(vm, errno_at(fs_base), ENOMEM)
          return bits[64](2^64 - 1)
        }
        return bits[64](p * PAGE)
      }
    }
    vm := wr32(vm, errno_at(fs_base), any e: nat where mmap_err(addr, len, flags, e))
    return bits[64](2^64 - 1)
  }
}

fn mmap_spec_fun() -> CFun2[World] = (args: Args) => {
  require len(args) >= 6
  let r = mmap_spec(bits[64](args[0]), bits[64](args[1]), bits[32](args[2]), bits[32](args[3]), bits[64](args[5]))
  let w = result[64](r)
  return (w, any bits[64])
}

// __syscall6(9, ..): the kernel's mmap, as malloc makes it (its
// requirements GIMPLE's) -- its seventh argument on the stack
proc[World] syscall6_spec(n: bits[64], a1: Addr, a2: bits[64], a3: bits[64], a4: bits[64], a5: bits[64], a6: bits[64]) -> bits[64] {
  require uint(n) = 9 && (if a4[4] { sys_pages_ok(vm, objs, page_of(a1), pages_for(uint(a2))) } else { uint(a1) = 0 })
  either { overflow() } or { return os_mmap(a1, a2, a3, a4, a5, a6) }
}
fn syscall6_spec_fun() -> CFunS[World] = (args: ArgsS) => {
  require len(args) >= 7
  let r = syscall6_spec(bits[64](args[0]), bits[64](args[1]), bits[64](args[2]), bits[64](args[3]), bits[64](args[4]), bits[64](args[5]), bits[64](args[6]))
  let w = result[64](r)
  return (w, any bits[64])
}

// __vm_wait (musl's no-op without threads): nothing
proc[World] vm_wait_spec() {
  either { overflow() } or { }
}
fn vm_wait_spec_fun() -> CFun2[World] = (args: Args) => {
  vm_wait_spec()
  return (any bits[64], any bits[64])
}

// mprotect(addr, len, prot): the pages from addr's to addr + len's of
// protection prot, 0; or, at the first of them unmapped, -1, errno
// ENOMEM -- the pages before it changed already. The pages ones the kernel
// may reprotect (sys_pages_ok: off the stack's space, not executable),
// neither the thread's pointer's nor errno's (`tls_off`: errno is set
// after). (len + PAGE <= 2^63: addr + len + PAGE - 1 a defined pointer
// sum, as musl forms it.)
proc[World] mprotect_spec(addr: Addr, len: bits[64], prot: bits[32]) -> bits[32] {
  require uint(prot) < 8 && uint(addr) + uint(len) + PAGE <= 2^64 && uint(len) + PAGE <= 2^63 && errno_ok(vm, objs, fs_base) &&
    sys_pages_ok(vm, objs, uint(addr) / PAGE, (uint(addr) + uint(len) + PAGE - 1) / PAGE - uint(addr) / PAGE) &&
    tls_off(fs_base, uint(addr) / PAGE, (uint(addr) + uint(len) + PAGE - 1) / PAGE - uint(addr) / PAGE)
  either { overflow() } or {
    let before = vm
    let s = uint(addr) / PAGE
    let e = (uint(addr) + uint(len) + PAGE - 1) / PAGE
    if all q: nat. s <= q && q < e -> mapped(before, q) {
      havoc vm where reprot(before, vm, s, e - s, prot_of(bits[64](uint(prot))))
      return 0
    }
    let k = any k: nat where s <= k && k < e && !mapped(before, k) && (all q: nat. s <= q && q < k -> mapped(before, q))
    havoc vm where reprot(before, vm, s, k - s, prot_of(bits[64](uint(prot))))
    vm := wr32(vm, errno_at(fs_base), ENOMEM)
    return bits[32](2^32 - 1)
  }
}

fn mprotect_spec_fun() -> CFun2[World] = (args: Args) => {
  require len(args) >= 3
  let r = mprotect_spec(bits[64](args[0]), bits[64](args[1]), bits[32](args[2]))
  let w = result[32](r)
  return (w, any bits[64])
}

// munmap(addr, len): the pages from addr's for len gone, 0; or -1, errno
// EINVAL (addr not a page's start, len 0, the pages past the task's),
// nothing else changed. The pages ones the kernel may unmap (sys_pages_ok:
// off the stack's space, not executable), neither the thread pointer's
// nor errno's (`tls_off`: __syscall_ret runs after).
proc[World] munmap_spec(addr: Addr, len: bits[64]) -> bits[32] {
  require errno_ok(vm, objs, fs_base) && sys_pages_ok(vm, objs, page_of(addr), pages_for(uint(len))) &&
    tls_off(fs_base, page_of(addr), pages_for(uint(len)))
  either { overflow() } or {
    if uint(addr) % PAGE != 0 || len = 0 || page_of(addr) + pages_for(uint(len)) > TASK_SIZE / PAGE {
      vm := wr32(vm, errno_at(fs_base), EINVAL)
      return bits[32](2^32 - 1)
    }
    let before = vm
    havoc vm where gone_pages(before, vm, page_of(addr), pages_for(uint(len))) && vm.brk = before.brk
    return 0
  }
}

fn munmap_spec_fun() -> CFun2[World] = (args: Args) => {
  require len(args) >= 2
  let r = munmap_spec(bits[64](args[0]), bits[64](args[1]))
  let w = result[32](r)
  return (w, any bits[64])
}

// memcpy(d, s, n): the n bytes at s copied to d (apart), d returned
proc[World] memcpy_spec(d: Addr, s: Addr, n: bits[64]) -> bits[64] {
  require usable(vm, objs, uint(s), uint(n), false) && usable(vm, objs, uint(d), uint(n), true) &&
    (uint(d) + uint(n) <= uint(s) || uint(s) + uint(n) <= uint(d))
  either { overflow() } or {
    let before = vm
    vm := vm with { bytes: store_le(vm.bytes, d, uint(n), bytes_at(before, s, uint(n))) }
    return d
  }
}

fn memcpy_spec_fun() -> CFun2[World] = (args: Args) => {
  require len(args) >= 3
  let r = memcpy_spec(bits[64](args[0]), bits[64](args[1]), bits[64](args[2]))
  return (result(r), any bits[64])
}

// libc's auxiliary vector readable (`libc.auxv`, at libc + 8, not null):
// its pairs up to AT_NULL (below 2^63: an index into it a pointer's signed
// offset), the 8 bytes past AT_RANDOM's address
pred auxv_ok(vm: Vm, objs: Objs, libc: Addr) =
  usable(vm, objs, uint(libc) + 8, 8, false) && bytes_at(vm, libc + 8, 8) != 0 &&
  (ex auxv: List[(nat, nat)]. len(auxv) >= 1 &&
     (all k: nat. k < len(auxv) ->
        usable(vm, objs, bytes_at(vm, libc + 8, 8) + 16 * k, 16, false) && bytes_at(vm, libc + 8, 8) + 16 * k + 16 <= 2^63 &&
        bytes_at(vm, bits[64](bytes_at(vm, libc + 8, 8) + 16 * k), 8) = auxv[k][0] &&
        bytes_at(vm, bits[64](bytes_at(vm, libc + 8, 8) + 16 * k + 8), 8) = auxv[k][1] &&
        (auxv[k][0] = AT_RANDOM -> usable(vm, objs, auxv[k][1] + 8, 8, false))) &&
     auxv[len(auxv) - 1][0] = AT_NULL && (all k: nat. k + 1 < len(auxv) -> auxv[k][0] != AT_NULL))

// get_random_secret(): a secret -- any value (the kernel's random bytes,
// AT_RANDOM's, if any), nothing changed but the stack's free bytes (its
// own stack object's, dead after it: `stack_free`); the thread sound (the
// copy a call)
proc[World] random_secret_spec(libc: Addr) -> bits[64] {
  require auxv_ok(vm, objs, libc) && thread_ok(vm, fs_base)
  either { overflow() } or {
    let before = vm
    havoc vm where (vm with { bytes: before.bytes }) = before &&
      (all a: Addr. !stack_free(before, objs, uint(a)) -> vm.bytes[a] = before.bytes[a])
    return any bits[64]
  }
}

fn random_secret_spec_fun(libc: Addr) -> CFun2[World] = (args: Args) => {
  let r = random_secret_spec(libc)
  let w = result[64](r)
  return (w, any bits[64])
}

// a_cas(p, t, s): the 4-byte word at p, s written if it holds t; its old
// value returned (a locked compare-and-swap: one thread, so one step). The
// word usable for reading and writing: the instruction writes it either
// way (its old value back when it is not t).
pred a_cas_pre(vm: Vm, objs: Objs, p: Addr) =
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
pred table_ok(vm: Vm, objs: Objs, t: Addr, n: nat, tab: List[nat]) =
  all i: nat. i < len(tab) ->
    usable(vm, objs, uint(t) + n * i, n, false) && bytes_at(vm, bits[64](uint(t) + n * i), n) = tab[i]

///////////////////////////////////////////////////////////////////////
//  Bit counts (C2: proofs/mallocng/code/classes.core); their callers' C2 use
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

// get_stride's conditions and effect (`ms.gs_run`; its spec
// below). get_stride(g): the slot size of g's group (mallocng's `stride` of the
// meta at g): its mapping less the group's header (a unit) for a group of
// one slot mapped on its own, else a unit times its size class's entry
// (the class one of the 48); sct: the class table's address
pred get_stride_pre(vm: Vm, objs: Objs, sct: Addr, g: Addr) =
  g != 0 && uint(g) + 40 <= 2^64 && usable(vm, objs, uint(g) + 32, 8, false) &&
  (!mapped_single(vm, g) -> mword(vm, g) / 64 % 64 < 48 && table_ok(vm, objs, sct, 2, size_classes))

fn stride_w(vm: Vm, g: Addr) -> nat =
  if mapped_single(vm, g) { mword(vm, g) / 4096 * 4096 - UNIT } else { UNIT * size_classes[mword(vm, g) / 64 % 64] }

// a 16-bit word written
fn wr16(vm: Vm, a: Addr, v: nat) -> Vm = vm with { bytes: store_le(vm.bytes, a, 2, v) }

// the start of slot idx of the group of meta g (its storage a unit past the
// group's header, at the meta's mem word)
fn eslot(vm: Vm, g: Addr, idx: bits[32]) -> nat = uint(rd64(vm, g + 16)) + UNIT + stride_w(vm, g) * uint(idx)

// enframe's conditions and effect (`ms.ef_run`; its spec
// below). enframe(g, idx, n, ctr): slot idx of g's group framed for n bytes at some
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
pred enframe_pre(vm: Vm, objs: Objs, fs: Addr, sct: Addr, g: Addr, idx: bits[32], n: bits[64]) =
  get_stride_pre(vm, objs, sct, g) && usable(vm, objs, uint(g) + 16, 8, false) &&
  uint(idx) < 2^31 && uint(n) + IB <= stride_w(vm, g) && stride_w(vm, g) - uint(n) - IB < 2^31 &&
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

// get_meta's effect (proofs/mallocng/code/slots.core's `ms.gm_run`; its spec
// below): the meta of p's group. p's
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
pred get_meta_pre(vm: Vm, objs: Objs, fs: Addr, ctx: Addr, sct: Addr, p: Addr) =
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

// activate_group's effect (`ms.ag_run`; its spec
// below): the slots of m's group up to its active
// index idx (act: the low idx + 1 bits; idx the low 5 bits of the byte at
// the group's header + 8, the header at m's mem word) leave the freed mask
// and become the available one (0 before: else a_crash). The masks at
// m + 24 (available) and m + 28 (freed), the mem word at m + 16; the freed
// mask changed by a_cas (one thread: in one step), the thread pointer
// sound for that call.
fn ag_act(vm: Vm, m: Addr) -> bits[32] = bits[32](2 * 2^(bytes_at(vm, rd64(vm, m + 16) + 8, 1) % 32) - 1)
fn ag_freed(vm: Vm, m: Addr) -> bits[32] = bits[32](bytes_at(vm, m + 28, 4))

pred activate_group_pre(vm: Vm, objs: Objs, fs: Addr, m: Addr) =
  m != 0 && uint(m) + 32 <= 2^64 && usable(vm, objs, uint(m) + 16, 16, false) && usable(vm, objs, uint(m) + 24, 8, true) &&
  bytes_at(vm, m + 24, 4) = 0 &&
  rd64(vm, m + 16) != 0 && uint(rd64(vm, m + 16)) + 9 <= 2^64 && usable(vm, objs, uint(rd64(vm, m + 16)) + 8, 1, false) &&
  thread_ok(vm, fs)

fn activate_group_vm(vm: Vm, m: Addr) -> Vm =
  wr32(wr32(vm, m + 28, uint(ag_freed(vm, m) & ~ag_act(vm, m))), m + 24, uint(ag_freed(vm, m) & ag_act(vm, m)))

// __malloc_allzerop's effect (`ms.az_run`; its spec
// below): whether p's slot is known zero-filled
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
pred bounce_pre(vm: Vm, objs: Objs, ctx: Addr, sc: bits[32], w: bool) =
  ctx != 0 && uint(ctx) + 913 <= 2^64 &&
  (bouncing_class(sc) -> usable(vm, objs, uint(bounce_at(ctx, sc)), 1, false) && (w -> usable(vm, objs, uint(bounce_at(ctx, sc)), 1, true)))

// decay_bounces(sc): sc's counter, if not 0, less 1
fn decay_vm(vm: Vm, ctx: Addr, sc: bits[32]) -> Vm =
  if bouncing_class(sc) && bytes_at(vm, bounce_at(ctx, sc), 1) != 0 {
    wr8(vm, bounce_at(ctx, sc), bytes_at(vm, bounce_at(ctx, sc), 1) - 1)
  } else { vm }

fn seq_at(ctx: Addr) -> Addr = ctx + 912
fn unmap_seqs_at(ctx: Addr) -> Addr = ctx + 848

// account_bounce(sc): a size class unmapped lately (its unmap sequence
// byte set, the sequence at most 9 past it) bounced once more: its counter
// up by 1 below 99, else 150. The bytes: usable (the counter for writing).
fn unmap_seq_at(ctx: Addr, sc: bits[32]) -> Addr = bits[64](uint(ctx) + 848 + uint(sc) - 7)

pred account_bounce_pre(vm: Vm, objs: Objs, ctx: Addr, sc: bits[32]) =
  bounce_pre(vm, objs, ctx, sc, true) &&
  (bouncing_class(sc) -> usable(vm, objs, uint(unmap_seq_at(ctx, sc)), 1, false) && usable(vm, objs, uint(ctx) + 912, 1, false))

pred bounced(vm: Vm, ctx: Addr, sc: bits[32]) =
  bouncing_class(sc) && bytes_at(vm, unmap_seq_at(ctx, sc), 1) != 0 && bytes_at(vm, seq_at(ctx), 1) <= bytes_at(vm, unmap_seq_at(ctx, sc), 1) + 9

fn account_vm(vm: Vm, ctx: Addr, sc: bits[32]) -> Vm =
  if bounced(vm, ctx, sc) {
    wr8(vm, bounce_at(ctx, sc), if bytes_at(vm, bounce_at(ctx, sc), 1) <= 98 { bytes_at(vm, bounce_at(ctx, sc), 1) + 1 } else { 150 })
  } else { vm }

// step_seq(): the sequence byte counted up -- at 255, the unmap sequence
// bytes zeroed and the count restarted at 1

pred step_seq_pre(vm: Vm, objs: Objs, ctx: Addr) =
  ctx != 0 && uint(ctx) + 913 <= 2^64 &&
  usable(vm, objs, uint(ctx) + 912, 1, false) && usable(vm, objs, uint(ctx) + 912, 1, true) &&
  (bytes_at(vm, seq_at(ctx), 1) = 255 -> usable(vm, objs, uint(ctx) + 848, 32, true))

fn step_seq_vm(vm: Vm, ctx: Addr) -> Vm =
  if bytes_at(vm, seq_at(ctx), 1) != 255 { wr8(vm, seq_at(ctx), bytes_at(vm, seq_at(ctx), 1) + 1) }
  else { wr8(vm with { bytes: store_le(vm.bytes, unmap_seqs_at(ctx), 32, 0) }, seq_at(ctx), 1) }

// resetlock(): the lock word (at lk) 0
pred resetlock_pre(vm: Vm, objs: Objs, lk: Addr) = lk != 0 && uint(lk) + 4 <= 2^64 && usable(vm, objs, uint(lk), 4, true)

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

// rdlock(), wrlock(): nothing -- libc single-threaded (its need_locks, at
// libc + 3, 0: __lock never called)
pred need_locks_off(vm: Vm, objs: Objs, libc: Addr) =
  libc != 0 && uint(libc) + 4 <= 2^64 && usable(vm, objs, uint(libc) + 3, 1, false) && bytes_at(vm, libc + 3, 1) = 0

proc[World] lock_spec(libc: bits[64]) {
  require need_locks_off(vm, objs, libc)
  either { overflow() } or { vm := vm }
}

fn lock_spec_fun(libc: bits[64]) -> CFun2[World] = (args: Args) => {
  lock_spec(libc)
  return (any bits[64], any bits[64])
}

// unlock(), __unlock(lk): nothing -- the lock word at lk 0 (never taken:
// single-threaded); the thread sound (unlock's a call)
pred lock_free(vm: Vm, objs: Objs, lk: Addr) =
  lk != 0 && uint(lk) + 4 <= 2^64 && usable(vm, objs, uint(lk), 4, false) && bytes_at(vm, lk, 4) = 0

proc[World] unlock_spec(lk: bits[64]) {
  require lock_free(vm, objs, lk) && thread_ok(vm, fs_base)
  either { overflow() } or { vm := vm }
}

// (unlock(): of the lock lk, __malloc_lock)
fn unlock_spec_fun(lk: bits[64]) -> CFun2[World] = (args: Args) => {
  unlock_spec(lk)
  return (any bits[64], any bits[64])
}

// (__unlock(lk): of its argument)
fn unlock_arg_spec_fun() -> CFun2[World] = (args: Args) => {
  require len(args) >= 1
  unlock_spec(bits[64](args[0]))
  return (any bits[64], any bits[64])
}

///////////////////////////////////////////////////////////////////////
//  The functions by their purpose, over the abstract state

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
pred list_at(vm: Vm, objs: Objs, phead: bits[64], l: List[nat]) =
  head: word_ok(vm, objs, phead, 0) && head_al: al8(phead) &&
  linked: cyclic(mview(vm, all_bytes()), uint(rd64(vm, phead)), l) &&
  elems: (all i: nat. i < len(l) -> bound: l[i] + 16 <= 2^64 && prev_ok: word_ok(vm, objs, bits[64](l[i]), 0) &&
     next_ok: word_ok(vm, objs, bits[64](l[i]), 8) && al: l[i] % 8 = 0 &&
     off_head: (uint(phead) + 8 <= l[i] || l[i] + 16 <= uint(phead))) &&
  apart: (all i: nat, j: nat. i < len(l) && j < len(l) && i != j -> l[i] + 16 <= l[j] || l[j] + 16 <= l[i])

// no byte but the head word and l's link words changed, nothing else
pred links_only(before: Vm, vm: Vm, phead: bits[64], l: List[nat]) =
  (vm with { bytes: before.bytes }) = before &&
  (all a: nat. a < 2^64 && !(uint(phead) <= a && a < uint(phead) + 8) && (all i: nat. i < len(l) -> !(l[i] <= a && a < l[i] + 16)) ->
     vm.bytes[bits[64](a)] = before.bytes[bits[64](a)])

// dequeue(phead, m), m in the list at phead: m out of it, the others'
// order kept, m's links cleared
pred dequeued(before: Vm, vm: Vm, objs: Objs, phead: bits[64], m: bits[64]) =
  all l: List[nat], k: nat. list_at(before, objs, phead, l) && k < len(l) && l[k] = uint(m) ->
    list_at(vm, objs, phead, rm_at(l, k)) && rd64(vm, m) = 0 && rd64(vm, m + 8) = 0 && links_only(before, vm, phead, l)

proc[World] dequeue_spec(phead: bits[64], m: bits[64]) {
  require ex l: List[nat], k: nat. list_at(vm, objs, phead, l) && k < len(l) && l[k] = uint(m)
  either { overflow() } or {
    let before = vm
    havoc vm where dequeued(before, vm, objs, phead, m)
  }
}

// queue(phead, m): m, outside the list at *phead (its words accessible,
// 8-aligned, apart from the list's and the head word; its links 0 -- else
// musl's a_crash, a bug), joins it at the end; no byte but the head word
// and the links written
pred joinable(vm: Vm, objs: Objs, phead: bits[64], l: List[nat], m: bits[64]) =
  bound: uint(m) + 16 <= 2^64 && prev_ok: word_ok(vm, objs, m, 0) && next_ok: word_ok(vm, objs, m, 8) && al: uint(m) % 8 = 0 &&
  off_head: (uint(phead) + 8 <= uint(m) || uint(m) + 16 <= uint(phead)) &&
  off_list: (all i: nat. i < len(l) -> l[i] + 16 <= uint(m) || uint(m) + 16 <= l[i]) &&
  prev0: rd64(vm, m) = 0 && next0: rd64(vm, m + 8) = 0
pred queued(before: Vm, vm: Vm, objs: Objs, phead: bits[64], m: bits[64]) =
  all l: List[nat]. list_at(before, objs, phead, l) && joinable(before, objs, phead, l, m) ->
    list_at(vm, objs, phead, l ++ [uint(m)]) && links_only(before, vm, phead, l ++ [uint(m)])

proc[World] queue_spec(phead: bits[64], m: bits[64]) {
  require ex l: List[nat]. list_at(vm, objs, phead, l) && joinable(vm, objs, phead, l, m)
  either { overflow() } or {
    let before = vm
    havoc vm where queued(before, vm, objs, phead, m)
  }
}

// free_meta(m): m's meta (its 40 bytes: accessible, 8-aligned, apart from
// the free metas' list at ctx + 16 and its head word) cleared and m
// appended to that list -- its links the list's, its other bytes 0; no
// byte but those, the head word and the list's links written. Its call to
// queue needs the thread pointer sound, its word not m's.
pred meta_joinable(vm: Vm, objs: Objs, phead: bits[64], l: List[nat], m: bits[64]) =
  nonnull: m != 0 && bound: uint(m) + 40 <= 2^64 && al: uint(m) % 8 = 0 &&
  read: usable(vm, objs, uint(m), 40, false) && write: usable(vm, objs, uint(m), 40, true) &&
  off_head: (uint(phead) + 8 <= uint(m) || uint(m) + 40 <= uint(phead)) &&
  off_list: (all i: nat. i < len(l) -> l[i] + 16 <= uint(m) || uint(m) + 40 <= l[i])
pred meta_freed(before: Vm, vm: Vm, objs: Objs, phead: bits[64], m: bits[64]) =
  all l: List[nat]. list_at(before, objs, phead, l) && meta_joinable(before, objs, phead, l, m) ->
    list_at(vm, objs, phead, l ++ [uint(m)]) &&
    (all a: nat. uint(m) + 16 <= a && a < uint(m) + 40 -> vm.bytes[bits[64](a)] = 0) &&
    (vm with { bytes: before.bytes }) = before &&
    (all a: nat. a < 2^64 && !(uint(phead) <= a && a < uint(phead) + 8) && !(uint(m) <= a && a < uint(m) + 40) &&
       (all i: nat. i < len(l) -> !(l[i] <= a && a < l[i] + 16)) ->
       vm.bytes[bits[64](a)] = before.bytes[bits[64](a)])

proc[World] free_meta_spec(ctx: bits[64], m: bits[64]) {
  require uint(ctx) + 16 < 2^64 &&
    (ex l: List[nat]. list_at(vm, objs, ctx + 16, l) && meta_joinable(vm, objs, ctx + 16, l, m)) &&
    thread_ok(vm, fs_base) && uint(fs_base) + 8 <= 2^64 && (uint(fs_base) + 8 <= uint(m) || uint(m) + 40 <= uint(fs_base))
  either { overflow() } or {
    let before = vm
    havoc vm where meta_freed(before, vm, objs, ctx + 16, m)
  }
}

// dequeue_head(phead): the list at *phead's first element (0 for an empty
// list) out of it and returned. Its call to dequeue needs the thread
// pointer sound (the ABI's, at every call).
pred is_head(vm: Vm, objs: Objs, phead: bits[64], h: bits[64]) =
  all l: List[nat]. list_at(vm, objs, phead, l) -> uint(h) = (if len(l) = 0 { 0 } else { l[0] })
pred head_taken(before: Vm, vm: Vm, objs: Objs, phead: bits[64], h: bits[64]) =
  (h = 0 -> vm = before) && (h != 0 -> dequeued(before, vm, objs, phead, h))

proc[World] dequeue_head_spec(phead: bits[64]) -> bits[64] {
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

proc[World] set_size_spec(p: bits[64], end: bits[64], n: bits[64]) {
  require set_size_pre(vm, objs, p, end, n)
  either { overflow() } or {
    let before = vm
    havoc vm where size_set(before, vm, p, end, n)
  }
}

// get_slot_index(p), p where a client block or a nested group starts: the
// index of its slot in its group
proc[MallocAbs] get_slot_index_spec(c: Cfg, p: bits[64]) -> bits[32] {
  require holds_in(c, A, vm, objs, blocks) && no_reserved(A) && (ex g: nat, i: nat. starts_at(A, g, i, uint(p)))
  either { overflow() } or {
    return any i: bits[32] where ex g: nat. starts_at(A, g, uint(i), uint(p))
  }
}

// get_meta(p), p where a client block or a nested group starts: the meta
// of its group (the thread pointer sound: get_meta's checks may call
// a_crash)
proc[MallocAbs] get_meta_spec(c: Cfg, p: bits[64]) -> bits[64] {
  require holds_in(c, A, vm, objs, blocks) && no_reserved(A) && thread_ok(vm, fs_base) && (ex g: nat, i: nat. starts_at(A, g, i, uint(p)))
  either { overflow() } or {
    return any m: bits[64] where ex i: nat. starts_at(A, uint(m), i, uint(p))
  }
}

// __malloc_allzerop(p), p where a client block or a nested group starts:
// whether its group is one slot mapped on its own (`own_mapping`)
proc[MallocAbs] allzerop_spec(c: Cfg, p: bits[64]) -> bits[32] {
  require holds_in(c, A, vm, objs, blocks) && no_reserved(A) && thread_ok(vm, fs_base) && (ex g: nat, i: nat. starts_at(A, g, i, uint(p)))
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
// part: for a size class, p within the class's slot wherever it lies (the
// slot's slack under it, or the offset's 256 units); the thread pointer's
// word apart from the slot; the slot's slack past n below 2^31 (enframe's
// int arithmetic on it).
proc[MallocAbs] enframe_spec(c: Cfg, g: bits[64], idx: bits[32], n: bits[64]) -> bits[64] {
  require holds_in(c, A, vm, objs, blocks) && thread_ok(vm, fs_base) && is_used(A, uint(g)) && reserved_only(A, uint(g), uint(idx)) &&
    slot_rw(vm, A.metas[uint(g)], uint(idx)) &&
    uint(n) + IB <= stride(A.metas[uint(g)]) && stride(A.metas[uint(g)]) - uint(n) - IB < 2^31 &&
    (A.metas[uint(g)].sizeclass < 48 ->
       slot_end(A.metas[uint(g)], uint(idx)) - uint(n) - storage(A.metas[uint(g)]) < UNIT * size_classes[A.metas[uint(g)].sizeclass] * (uint(idx) + 1) ||
       slot_start(A.metas[uint(g)], uint(idx)) - storage(A.metas[uint(g)]) + 256 * UNIT <= UNIT * size_classes[A.metas[uint(g)].sizeclass] * (uint(idx) + 1)) &&
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
proc[MallocAbs] get_stride_spec(c: Cfg, g: bits[64]) -> bits[64] {
  require holds_in(c, A, vm, objs, blocks) && is_used(A, uint(g))
  either { overflow() } or { return bits[64](stride(A.metas[uint(g)])) }
}

// The context's counters (`ctx_free`: the bounce counters, the sequence
// bytes): what step_seq, decay_bounces and account_bounce do there is
// musl's tuning -- by their purpose, those bytes changed anyhow, nothing
// else (so the invariant kept). is_bouncing(sc) reads them: whether class
// sc bounces, a heuristic's answer -- any.
pred ctx_only(c: Cfg, before: Vm, vm: Vm) =
  (vm with { bytes: before.bytes }) = before && (all x: bits[64]. !ctx_free(c, uint(x)) -> vm.bytes[x] = before.bytes[x])

proc[MallocAbs] counters_spec(c: Cfg) {
  require holds_in(c, A, vm, objs, blocks)
  either { overflow() } or {
    let before = vm
    havoc vm where ctx_only(c, before, vm)
  }
}

proc[MallocAbs] is_bouncing_spec(c: Cfg, sc: bits[32]) -> bits[32] {
  require holds_in(c, A, vm, objs, blocks)
  either { overflow() } or { return any bits[32] }
}

// get_nominal_size(p, end), p a client block in slot i of a group, end the
// slot's end: the block's size (its reserved-size encoding up to end, as
// enframe left it -- the code's checks of it pass)
proc[MallocAbs] nominal_size_spec(c: Cfg, p: bits[64], end: bits[64]) -> bits[64] {
  require holds_in(c, A, vm, objs, blocks) && no_reserved(A) && thread_ok(vm, fs_base) &&
    (ex g: nat, i: nat. is_used(A, g) && i < len(A.slots[g]) && A.slots[g][i] = block(uint(p)) && uint(end) = slot_end(A.metas[g], i))
  either { overflow() } or { return bits[64](blocks[p].value) }
}

// okay_to_free(g), g a group in use whose slots are all free: whether to
// free it now -- musl's heuristic (the class's usage, bouncing), any answer
proc[MallocAbs] okay_to_free_spec(c: Cfg, g: bits[64]) -> bits[32] {
  require holds_in(c, A, vm, objs, blocks) && is_used(A, uint(g)) && thread_ok(vm, fs_base)
  either { overflow() } or { return any bits[32] }
}

// A2: A with its groups' masks (which free slots are available, which
// freed) changed, nothing else
pred masks_only(A: Abs, A2: Abs) =
  others: (A2 with { metas: A.metas }) = A &&
  groups: (all g: nat. (A2.metas[g] with { avail: 0, freed: 0 }) = (A.metas[g] with { avail: 0, freed: 0 }))

// a group's active index (its header's): the slots above it never handed out
fn active_idx(vm: Vm, v: MetaV) -> nat = b8(mview(vm, all_bytes()), v.mem + 8) % 32

// A2: A with g's freed slots up to idx made available, its others staying
// freed
pred activated(A: Abs, A2: Abs, g: nat, idx: nat) =
  masks_only(A, A2) && (all h: nat. h != g -> A2.metas[h] = A.metas[h]) &&
  A2.metas[g].avail < 2^32 && A2.metas[g].freed < 2^32 &&
  (all i: nat. i < 32 ->
     bit(A2.metas[g].avail, i) = (if i <= idx { bit(A.metas[g].freed, i) } else { 0 }) &&
     bit(A2.metas[g].freed, i) = (if i <= idx { 0 } else { bit(A.metas[g].freed, i) }))

// activate_group(m), m a group in use, none of its slots available (else
// musl's a_crash), on no active list but as its head: its freed slots up to
// its active index made available (`activated`), the new available mask
// returned; the memory outside the allocator's untouched. Its call to a_cas
// needs the thread pointer sound.
proc[MallocAbs] activate_group_spec(c: Cfg, m: bits[64]) -> bits[32] {
  require holds_in(c, A, vm, objs, blocks) && no_reserved(A) && thread_ok(vm, fs_base) && is_used(A, uint(m)) && A.metas[uint(m)].avail = 0 &&
    (all sc: nat, k: nat. sc < 48 && k < len(A.active[sc]) && A.active[sc][k] = uint(m) -> k = 0)
  either { overflow() } or {
    let A0 = A
    let before = vm
    ghost A := any A2: Abs where activated(A0, A2, uint(m), active_idx(before, A0.metas[uint(m)]))
    havoc vm where holds_in(c, A, vm, objs, blocks) && untouched(c, A0, blocks, before, vm, objs, {})
    return bits[32](A.metas[uint(m)].avail)
  }
}

// the thread pointer's word: not the allocator's (a function calling on
// after writing the allocator's memory needs it intact)
pred tls_apart(c: Cfg, A: Abs, blocks: Addr -> Option[nat], fs: Addr) = all i: nat. i < 8 -> uint(fs) + i notin footprint(c, A, blocks)

// errno's cell (the thread's, mapped as the thread pointer's word) not the
// allocator's
pred errno_apart(c: Cfg, A: Abs, blocks: Addr -> Option[nat], vm: Vm, fs: Addr) =
  all i: nat. i < 4 -> uint(errno_at(fs)) + i notin footprint(c, A, blocks) && mapped(vm, (uint(errno_at(fs)) + i) / PAGE)

// try_avail(pm), pm class sc's active list: a free slot of a group already
// there. Its bit (1 << i) returned, slot i of the list's head reserved --
// the head now, if need be: the list reorganised --; or 0, no group of the
// list with a free slot (the list then empty). A runs out of stack, if it
// does, with the memory arbitrary.
proc[MallocAbs] try_avail_spec(c: Cfg, sc: nat, pm: bits[64]) -> bits[32] {
  require holds_in(c, A, vm, objs, blocks) && no_reserved(A) && thread_ok(vm, fs_base) && tls_apart(c, A, blocks, fs_base) &&
    sc < 48 && uint(pm) >= c.ctx + C_ACTIVE && uint(pm) = c.ctx + C_ACTIVE + 8 * sc
  either { overflow() } or {
    let A0 = A
    let before = vm
    ghost A := any A2: Abs where reorganised(A0, A2, sc)
    let r = any r: bits[32] where (
      (r = 0 && len(A.active[sc]) = 0 && (all g: nat. on_list(A0.active[sc], g) -> !has_unused(A0, g)) && A.slots = A0.slots) ||
      (ex i: nat. i < 32 && uint(r) = 2^i && len(A.active[sc]) > 0 && reserves(A0, A, A.active[sc][0], i)))
    havoc vm where holds_in(c, A, vm, objs, blocks) && untouched(c, A0, blocks, before, vm, objs, {})
    return r
  }
}

// alloc_slot(sc, req): a slot for a block of req bytes in class sc. Its
// index i returned, slot i of the head of class sc's active list reserved
// (an existing group's free slot, or a new group's: mapped, or nested in a
// slot of a larger class), room in it for req bytes and the in-band
// header; or -1, out of memory, errno ENOMEM. The smaller classes' lists
// as before. The allocator may take memory that was unmapped (a new group,
// a meta area) and set errno (a failed mmap); the slot reserved is of the
// allocator's memory or of that.
proc[MallocAbs] alloc_slot_spec(c: Cfg, sc: bits[32], req: bits[64]) -> bits[32] {
  require holds_in(c, A, vm, objs, blocks) && no_reserved(A) && thread_ok(vm, fs_base) && tls_apart(c, A, blocks, fs_base) &&
    brk_start_ok(vm) && errno_ok(vm, objs, fs_base) && errno_apart(c, A, blocks, vm, fs_base) &&
    uint(sc) < 48 && uint(req) + IB <= UNIT * size_classes[uint(sc)]
  either { overflow() } or {
    let A0 = A
    let before = vm
    let errno = {a: nat | uint(fs_base) + 0x34 <= a && a < uint(fs_base) + 0x38}
    ghost A := any A2: Abs where A2.taken = A0.taken && (all s: nat. s < uint(sc) -> A2.active[s] = A0.active[s])
    let r = any r: bits[32] where (
      (r = bits[32](2^32 - 1) && no_reserved(A)) ||
      (uint(r) < 32 && len(A.active[uint(sc)]) > 0 && reserved_only(A, A.active[uint(sc)][0], uint(r)) &&
       A.metas[A.active[uint(sc)][0]].sizeclass = uint(sc) &&
       uint(req) + IB <= stride(A.metas[A.active[uint(sc)][0]])))
    havoc vm where holds_in(c, A, vm, objs, blocks) && untouched(c, A0, blocks, before, vm, objs, errno) &&
      (all a: nat. a in footprint(c, A, blocks) -> a in footprint(c, A0, blocks) || !mapped(before, a / PAGE)) &&
      (all a: nat. in_reserved(A, a) -> a in footprint(c, A0, blocks) || !mapped(before, a / PAGE)) &&
      (r = bits[32](2^32 - 1) -> errno_is(vm, fs_base, ENOMEM))
    return r
  }
}

// A2: A with its groups as before -- the ones in use, their metas, slots
// and the active lists (the metas' supply, the areas, may differ)
pred groups_kept(A: Abs, A2: Abs) =
  A2.used = A.used && A2.slots = A.slots && A2.active = A.active && (all g: nat. is_used(A, g) -> A2.metas[g] = A.metas[g])

// a meta handed out: its bytes accessible, its links 0 (on no list)
pred meta_ready(vm: Vm, m: nat) =
  (all a: nat. m <= a && a < m + META_SIZE -> m_rw(mview(vm, all_bytes()), a) && pg(mview(vm, all_bytes()), a).value.kind != stack) &&
  rd(mview(vm, all_bytes()), m, 8) = 0 && rd(mview(vm, all_bytes()), m + 8, 8) = 0

// alloc_meta(): a meta for a new group -- taken (its maker's, out of the
// allocator's bytes: the allocator's before, or unmapped), ready -- or 0,
// none to be had (a failed mmap or mprotect), errno ENOMEM. The groups as before; the
// allocator may take memory that was unmapped (a meta area) and set errno
// (its cell writable, not the allocator's).
proc[MallocAbs] alloc_meta_spec(c: Cfg) -> bits[64] {
  require holds_in(c, A, vm, objs, blocks) && thread_ok(vm, fs_base) && tls_apart(c, A, blocks, fs_base) && brk_start_ok(vm) &&
    errno_ok(vm, objs, fs_base) && errno_apart(c, A, blocks, vm, fs_base)
  either { overflow() } or {
    let A0 = A
    let before = vm
    let errno = {a: nat | uint(fs_base) + 0x34 <= a && a < uint(fs_base) + 0x38}
    ghost A := any A2: Abs where groups_kept(A0, A2)
    let m = any m: bits[64] where (m = 0 && A.taken = A0.taken) || (m != 0 && A.taken = A0.taken ++ [uint(m)])
    havoc vm where holds_in(c, A, vm, objs, blocks) && untouched(c, A0, blocks, before, vm, objs, errno) &&
      (all a: nat. a in footprint(c, A, blocks) -> a in footprint(c, A0, blocks) || !mapped(before, a / PAGE)) &&
      (m != 0 -> meta_ready(vm, uint(m))) &&
      (m != 0 -> all a: nat. uint(m) <= a && a < uint(m) + META_SIZE -> a in footprint(c, A0, blocks) || !mapped(before, a / PAGE)) &&
      (m = 0 -> errno_is(vm, fs_base, ENOMEM))
    return m
  }
}

// g a group just made for class sc's requests of up to req bytes: in use,
// on no list (unlinked), its slots all unused, the first available; room
// in each slot for req bytes and the in-band header; one slot if mapped on
// its own shorter than the class's slots
pred fresh_group(A: Abs, g: nat, sc: nat, req: nat) =
  is_used(A, g) && A.metas[g].sizeclass = sc && A.metas[g].prev = 0 && A.metas[g].next = 0 &&
  (all i: nat. i < len(A.slots[g]) -> A.slots[g][i] = unused) && bit(A.metas[g].avail, 0) = 1 &&
  req + IB <= stride(A.metas[g]) && (own_mapping(A.metas[g]) -> A.metas[g].last_idx = 0)

// alloc_group(sc, req): a new group of class sc for requests of up to req
// bytes (`fresh_group`; partially active only if its slots reach past its
// first page) -- or 0, none to be had, errno ENOMEM. The lists of class sc and the
// smaller ones as before (a nested group's slot is a larger class's), no
// slot reserved; the allocator may take memory that was unmapped (the
// group, a meta area, a slot of a larger class's group) and set errno.
proc[MallocAbs] alloc_group_spec(c: Cfg, sc: bits[32], req: bits[64]) -> bits[64] {
  require holds_in(c, A, vm, objs, blocks) && no_reserved(A) && thread_ok(vm, fs_base) && tls_apart(c, A, blocks, fs_base) &&
    brk_start_ok(vm) && errno_ok(vm, objs, fs_base) && errno_apart(c, A, blocks, vm, fs_base) &&
    uint(sc) < 48 && uint(req) + IB <= UNIT * size_classes[uint(sc)]
  either { overflow() } or {
    let A0 = A
    let before = vm
    let errno = {a: nat | uint(fs_base) + 0x34 <= a && a < uint(fs_base) + 0x38}
    ghost A := any A2: Abs where no_reserved(A2) && (all s: nat. s <= uint(sc) -> A2.active[s] = A0.active[s]) && A2.taken = A0.taken
    let g = any g: bits[64] where g = 0 || fresh_group(A, uint(g), uint(sc), uint(req))
    havoc vm where holds_in(c, A, vm, objs, blocks) && untouched(c, A0, blocks, before, vm, objs, errno) &&
      (all a: nat. a in footprint(c, A, blocks) -> a in footprint(c, A0, blocks) || !mapped(before, a / PAGE)) &&
      (g != 0 -> active_idx(vm, A.metas[uint(g)]) < A.metas[uint(g)].last_idx ->
         4096 < UNIT + stride(A.metas[uint(g)]) * (A.metas[uint(g)].last_idx + 1)) &&
      (g = 0 -> errno_is(vm, fs_base, ENOMEM))
    return g
  }
}

// __libc_malloc_impl(n): a block of n bytes for the client -- p, a new
// live block (`blocks`; in a slot of one of the allocator's groups, framed
// for n bytes: the invariant's), its bytes the allocator's before or
// unmapped then -- or 0, errno ENOMEM (n beyond the allocator's sizes, no
// memory to be had). The invariant kept, nothing outside the allocator
// touched but errno, the allocator grown only into memory unmapped
// before. Which slot of which group -- musl's heuristics -- left free.
proc[MallocAbs] malloc_impl_spec(c: Cfg, n: bits[64]) -> Addr {
  require holds_in(c, A, vm, objs, blocks) && no_reserved(A) && len(A.taken) = 0 && thread_ok(vm, fs_base) &&
    tls_apart(c, A, blocks, fs_base) && brk_start_ok(vm) && errno_ok(vm, objs, fs_base) && errno_apart(c, A, blocks, vm, fs_base)
  either { overflow() } or {
    let A0 = A
    let blocks0 = blocks
    let before = vm
    let errno = {a: nat | uint(fs_base) + 0x34 <= a && a < uint(fs_base) + 0x38}
    let p = any p: Addr where p = 0 || blocks0[p] = none
    ghost blocks := if p != 0 { set_block(blocks0, p, some(uint(n))) } else { blocks0 }
    ghost A := any A2: Abs where no_reserved(A2) && len(A2.taken) = 0
    havoc vm where holds_in(c, A, vm, objs, blocks) && untouched(c, A0, blocks0, before, vm, objs, errno) &&
      (all a: nat. a in footprint(c, A, blocks) -> a in footprint(c, A0, blocks0) || !mapped(before, a / PAGE)) &&
      (p != 0 -> all a: nat. uint(p) <= a && a < uint(p) + uint(n) -> a in footprint(c, A0, blocks0) || !mapped(before, a / PAGE)) &&
      (p = 0 -> errno_is(vm, fs_base, ENOMEM))
    return p
  }
}

// ... as C function values (the result as GIMPLE returns it: `result`)
fn malloc_impl_spec_fun(c: Cfg) -> CFun2[MallocAbs] = (args: Args) => {
  require len(args) >= 1
  let r = malloc_impl_spec(c, bits[64](args[0]))
  let w = result[64](r)
  return (w, any bits[64])
}

fn set_size_spec_fun() -> CFun2[World] = (args: Args) => {
  require len(args) >= 3
  set_size_spec(bits[64](args[0]), bits[64](args[1]), bits[64](args[2]))
  return (any bits[64], any bits[64])
}

fn dequeue_spec_fun() -> CFun2[World] = (args: Args) => {
  require len(args) >= 2
  dequeue_spec(bits[64](args[0]), bits[64](args[1]))
  return (any bits[64], any bits[64])
}

fn queue_spec_fun() -> CFun2[World] = (args: Args) => {
  require len(args) >= 2
  queue_spec(bits[64](args[0]), bits[64](args[1]))
  return (any bits[64], any bits[64])
}

fn free_meta_spec_fun(ctx: bits[64]) -> CFun2[World] = (args: Args) => {
  require len(args) >= 1
  free_meta_spec(ctx, bits[64](args[0]))
  return (any bits[64], any bits[64])
}

fn dequeue_head_spec_fun() -> CFun2[World] = (args: Args) => {
  require len(args) >= 1
  let r = dequeue_head_spec(bits[64](args[0]))
  let w = result[64](r)
  return (w, any bits[64])
}

fn get_slot_index_spec_fun(c: Cfg) -> CFun2[MallocAbs] = (args: Args) => {
  require len(args) >= 1
  let r = get_slot_index_spec(c, bits[64](args[0]))
  let w = result[32](r)
  return (w, any bits[64])
}

fn get_meta_spec_fun(c: Cfg) -> CFun2[MallocAbs] = (args: Args) => {
  require len(args) >= 1
  let r = get_meta_spec(c, bits[64](args[0]))
  let w = result[64](r)
  return (w, any bits[64])
}

fn allzerop_spec_fun(c: Cfg) -> CFun2[MallocAbs] = (args: Args) => {
  require len(args) >= 1
  let r = allzerop_spec(c, bits[64](args[0]))
  let w = result[32](r)
  return (w, any bits[64])
}

fn enframe_spec_fun(c: Cfg) -> CFun2[MallocAbs] = (args: Args) => {
  require len(args) >= 4
  let r = enframe_spec(c, bits[64](args[0]), bits[32](args[1]), bits[64](args[2]))
  let w = result[64](r)
  return (w, any bits[64])
}

fn get_stride_spec_fun(c: Cfg) -> CFun2[MallocAbs] = (args: Args) => {
  require len(args) >= 1
  let r = get_stride_spec(c, bits[64](args[0]))
  let w = result[64](r)
  return (w, any bits[64])
}

// (step_seq: no argument; decay_bounces, account_bounce: the class, not
// read)
fn counters_spec_fun0(c: Cfg) -> CFun2[MallocAbs] = (args: Args) => {
  counters_spec(c)
  return (any bits[64], any bits[64])
}

fn counters_spec_fun1(c: Cfg) -> CFun2[MallocAbs] = (args: Args) => {
  require len(args) >= 1
  counters_spec(c)
  return (any bits[64], any bits[64])
}

fn is_bouncing_spec_fun(c: Cfg) -> CFun2[MallocAbs] = (args: Args) => {
  require len(args) >= 1
  let r = is_bouncing_spec(c, bits[32](args[0]))
  let w = result[32](r)
  return (w, any bits[64])
}

fn nominal_size_spec_fun(c: Cfg) -> CFun2[MallocAbs] = (args: Args) => {
  require len(args) >= 2
  let r = nominal_size_spec(c, bits[64](args[0]), bits[64](args[1]))
  let w = result[64](r)
  return (w, any bits[64])
}

fn okay_to_free_spec_fun(c: Cfg) -> CFun2[MallocAbs] = (args: Args) => {
  require len(args) >= 1
  let r = okay_to_free_spec(c, bits[64](args[0]))
  let w = result[32](r)
  return (w, any bits[64])
}

fn activate_group_spec_fun(c: Cfg) -> CFun2[MallocAbs] = (args: Args) => {
  require len(args) >= 1
  let r = activate_group_spec(c, bits[64](args[0]))
  let w = result[32](r)
  return (w, any bits[64])
}

fn try_avail_spec_fun(c: Cfg) -> CFun2[MallocAbs] = (args: Args) => {
  require len(args) >= 1
  let r = try_avail_spec(c, (uint(bits[64](args[0])) - c.ctx - C_ACTIVE) / 8, bits[64](args[0]))
  let w = result[32](r)
  return (w, any bits[64])
}

fn alloc_slot_spec_fun(c: Cfg) -> CFun2[MallocAbs] = (args: Args) => {
  require len(args) >= 2
  let r = alloc_slot_spec(c, bits[32](args[0]), bits[64](args[1]))
  let w = result[32](r)
  return (w, any bits[64])
}

fn alloc_meta_spec_fun(c: Cfg) -> CFun2[MallocAbs] = (args: Args) => {
  let r = alloc_meta_spec(c)
  let w = result[64](r)
  return (w, any bits[64])
}

fn alloc_group_spec_fun(c: Cfg) -> CFun2[MallocAbs] = (args: Args) => {
  require len(args) >= 2
  let r = alloc_group_spec(c, bits[32](args[0]), bits[64](args[1]))
  let w = result[64](r)
  return (w, any bits[64])
}
