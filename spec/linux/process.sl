spec x86_64_linux

// Linux process model: the system calls a single-threaded static program
// needs, with anonymous memory only.

// External interaction is an append-only trace of events. A diverging run
// carries the limit of its trace, which may be infinite (e.g. `yes`).
type IoEvent = read(data: List[bits[8]])                   // consumed from stdin
             | write(fd: bits[64], data: List[bits[8]])    // written to fd 1 or 2

// user and group ids: real and effective
record Creds { uid, euid, gid, egid : bits[32] }

record Os {
  input       : Seq[bits[8]]      // everything stdin will ever provide (fixed)
  trace events: Seq[IoEvent]      // what happened so far
  creds       : Creds             // set at exec; no modelled syscall changes them
  secure      : bool              // "secure execution" (set-user-ID, capabilities, ...),
                                  // reported as AT_SECURE; set at exec
}

// bytes of stdin consumed so far, and what is left
fn consumed(t: Seq[IoEvent]) -> natinf = sum e in t. match e { read(d) => len(d), _ => 0 }
fn pending(os: Os) -> Seq[bits[8]] = os.input[consumed(os.events)..]

// everything written to `fd`
fn output(t: Seq[IoEvent], fd: bits[64]) -> Seq[bits[8]] =
  concat([d for write(f, d) in t if f = fd])

const EPERM  : nat = 1
const EBADF  : nat = 9
const EAGAIN : nat = 11
const ENOMEM : nat = 12
const EFAULT : nat = 14
const EINVAL : nat = 22

fn err(e: nat) -> bits[64] = -bits[64](e)

const MAP_PRIVATE   : nat = 0x02
const MAP_FIXED     : nat = 0x10
const MAP_ANONYMOUS : nat = 0x20
const ARCH_SET_FS   : nat = 0x1002

// The whole process: runs until exit or a fault (or forever).
proc run() {
  while true { step() }
}

proc linux_syscall(nr: bits[64], a1: bits[64], a2: bits[64], a3: bits[64],
                   a4: bits[64], a5: bits[64], a6: bits[64]) -> bits[64] {
  match uint(nr) {
    0       => return sys_read(a1, a2, a3)
    1       => return sys_write(a1, a2, a3)
    9       => return sys_mmap(a1, a2, a3, a4, a5, a6)
    10      => return sys_mprotect(a1, a2, a3)
    11      => return sys_munmap(a1, a2)
    12      => return sys_brk(a1)
    158     => return sys_arch_prctl(a1, a2)
    202     => return sys_futex(a1, a2, a3, a4)
    218     => return sys_set_tid_address(a1)
    60, 231 => raise exit(a1[7:0])                    // exit, exit_group
    _       => undefined
  }
}

///////////////////////////////////////////////////////////////////////
//  Access to user memory from the kernel: a fault becomes -EFAULT.
//  (A kernel access below the stack grows it like a user access would.)

proc copy_from_user(a: Addr, n: nat) -> Option[List[bits[8]]] {
  try {
    touch_range(a, n, read)
    return some([vm.bytes[a + bits[64](i)] for i in 0..n])
  } catch segv(_, _) { return none }
}

// the kernel can write n bytes at a (without writing them)
proc user_writable(a: Addr, n: nat) -> bool {
  try {
    touch_range(a, n, write)
    return true
  } catch segv(_, _) { return false }
}

// On a fault part-way, the bytes before it may already have been written:
// some prefix, depending on how the kernel copies (byte by byte with
// `rep movsb`, in larger chunks otherwise).
proc copy_to_user(a: Addr, data: List[bits[8]]) -> bool {
  for i in 0..len(data) {
    try { touch(a + bits[64](i), write) }
    catch segv(_, _) {
      let k = any nat where k <= i
      for j in 0..k { vm.bytes[a + bits[64](j)] := data[j] }
      return false
    }
  }
  for i in 0..len(data) { vm.bytes[a + bits[64](i)] := data[i] }
  return true
}

///////////////////////////////////////////////////////////////////////
//  I/O

// The kernel's `access_ok`: the buffer lies in user space (checked even
// for an empty transfer).
pred user_range(a: Addr, n: bits[64]) = uint(a) + uint(n) <= TASK_SIZE

proc sys_write(fd: bits[64], buf: Addr, count: bits[64]) -> bits[64] {
  if fd != 1 && fd != 2 { undefined }                 // other fds: not modelled
  if !user_range(buf, count) { return err(EFAULT) }
  // a write may be short, but writes at least one byte
  let n = any nat where n <= uint(count) && (n >= 1 || count = 0)
  match copy_from_user(buf, n) {
    none       => return err(EFAULT)
    some(data) => {
      emit os.events write(fd, data)
      return bits[64](n)
    }
  }
}

proc sys_read(fd: bits[64], buf: Addr, count: bits[64]) -> bits[64] {
  if fd != 0 { undefined }
  if !user_range(buf, count) { return err(EFAULT) }
  // returns any non-empty prefix of the pending input; 0 only at end of input
  let rest = pending(os)
  let n = any nat where n <= uint(count) && n <= len(rest) &&
                        (n >= 1 || count = 0 || rest = [])
  if !copy_to_user(buf, rest[0..n]) { return err(EFAULT) }
  emit os.events read(rest[0..n])
  return bits[64](n)
}

///////////////////////////////////////////////////////////////////////
//  Memory management

fn pages_for(len: nat) -> nat = (len + PAGE - 1) / PAGE

// p..p+n is unmapped and keeps the stack guard gap below any stack
pred free_range(vm: Vm, p: nat, n: nat) =
  p + n <= TASK_SIZE / PAGE &&
  (all q: nat. p <= q && q < p + n -> !mapped(vm, q)) &&
  (all q: nat. q >= p + n && q < p + n + STACK_GUARD_GAP / PAGE && mapped(vm, q)
               -> vm.pages[q].value.kind != stack)

proc map_pages(p: nat, n: nat, pg: Page) {
  for q in p..p+n { vm.pages[q] := some(pg) }
  for i in p*PAGE .. (p+n)*PAGE { vm.bytes[bits[64](i)] := 0 }
}

fn prot_of(prot: bits[64]) -> Prot = Prot { r: prot[0], w: prot[1], x: prot[2] }

proc sys_mmap(addr: Addr, len: bits[64], prot: bits[64], flags: bits[64],
              fd: bits[64], off: bits[64]) -> bits[64] {
  let fixed = flags[4]
  require uint(flags) in {MAP_PRIVATE | MAP_ANONYMOUS,               // only anonymous private
                          MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED}
  require uint(prot) < 8
  if uint(off) % PAGE != 0 { return err(EINVAL) }     // checked even for anonymous maps
  if len = 0 { return err(EINVAL) }
  let n = pages_for(uint(len))
  either { return err(ENOMEM) } or {}                 // the kernel may always refuse
  var p = 0
  if fixed {
    if uint(addr) % PAGE != 0 { return err(EINVAL) }
    p := page_of(addr)
    if p + n > TASK_SIZE / PAGE { return err(ENOMEM) }
  } else {
    // the address hint may or may not be honoured; never page 0 (POSIX:
    // "When the implementation selects a value for pa, it never places a
    // mapping at address 0")
    p := any q: nat where q >= 1 && free_range(vm, q, n)
  }
  map_pages(p, n, Page { prot: prot_of(prot), kind: anon })   // MAP_FIXED replaces
  return bits[64](p * PAGE)
}

proc sys_munmap(addr: Addr, len: bits[64]) -> bits[64] {
  if uint(addr) % PAGE != 0 || len = 0 { return err(EINVAL) }
  let p = page_of(addr)
  let n = pages_for(uint(len))
  if p + n > TASK_SIZE / PAGE { return err(EINVAL) }
  for q in p..p+n { vm.pages[q] := none }
  return 0
}

// Stops at the first unmapped page; the pages before it may already
// have been changed when -ENOMEM is returned.
proc sys_mprotect(addr: Addr, len: bits[64], prot: bits[64]) -> bits[64] {
  if uint(addr) % PAGE != 0 { return err(EINVAL) }
  require uint(prot) < 8
  let p = page_of(addr)
  let n = pages_for(uint(len))
  for q in p..p+n {
    if !mapped(vm, q) { return err(ENOMEM) }
    vm.pages[q] := some(vm.pages[q].value with { prot: prot_of(prot) })
  }
  return 0
}

proc sys_brk(new: Addr) -> bits[64] {
  let old_end = pages_for(uint(vm.brk))
  let new_end = pages_for(uint(new))
  if new < vm.brk_start { return vm.brk }
  if new_end > old_end {
    if !free_range(vm, old_end, new_end - old_end) { return vm.brk }
    either { return vm.brk } or {}                    // out of memory
    map_pages(old_end, new_end - old_end,
              Page { prot: Prot { r: true, w: true, x: false }, kind: heap })
  } else {
    for q in new_end..old_end { vm.pages[q] := none }
  }
  vm.brk := new
  return new
}

// set_tid_address: returns the thread id (the kernel remembers the pointer
// for thread exit, which is not modelled)
proc sys_set_tid_address(tidptr: Addr) -> bits[64] {
  return any t: bits[64] where 0 < uint(t) && uint(t) < 2^22
}

// futex, for a single-threaded process: nobody else can wake a waiter or
// change the futex word. Only WAIT without timeout and WAKE are modelled.
const FUTEX_WAIT    : nat = 0
const FUTEX_WAKE    : nat = 1
const FUTEX_PRIVATE : nat = 128

proc sys_futex(uaddr: Addr, op: bits[64], val: bits[64], timeout: Addr) -> bits[64] {
  let cmd = uint(op) % FUTEX_PRIVATE
  if uint(op) >= 2 * FUTEX_PRIVATE { undefined }
  if cmd != FUTEX_WAKE && (cmd != FUTEX_WAIT || timeout != 0) { undefined }
  // the futex word: aligned, in user space
  if uint(uaddr) % 4 != 0 { return err(EINVAL) }
  if uint(uaddr) + 4 > TASK_SIZE { return err(EFAULT) }
  // a shared (not private) futex is identified by its page, which must be
  // writable: a read-only anonymous page never changes
  if uint(op) < FUTEX_PRIVATE && !user_writable(uaddr, 4) { return err(EFAULT) }
  if cmd = FUTEX_WAKE { return 0 }                   // no waiters
  match copy_from_user(uaddr, 4) {
    none    => return err(EFAULT)
    some(d) => {
      if (sum i in 0..4. uint(d[i]) * 256^i) != uint(val) % 2^32 { return err(EAGAIN) }
      loop {}                                        // blocks forever
    }
  }
}

proc sys_arch_prctl(code: bits[64], addr: bits[64]) -> bits[64] {
  if uint(code) != ARCH_SET_FS { undefined }
  if uint(addr) >= TASK_SIZE { return err(EPERM) }
  fs_base := addr
  return 0
}
