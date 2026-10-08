layer abi uses x86_64_linux

// System V x86_64 calling convention, as an abstraction over the machine.
// Nothing here is assumed about the computer: everything is a definition, and
// the claims (e.g. "glibc's malloc implements its spec") are theorems to prove.
//
// Covered: up to 6 integer/pointer arguments, integer/pointer result in rax.
// Not yet: stack-passed or floating-point arguments, struct returns, varargs.

///////////////////////////////////////////////////////////////////////
//  What a C function sees

// What a C function sees: the machine's memory on the world's domain (a
// partial byte map: the mapped pages that are not stack pages, and the bytes
// of the live stack objects `objs` -- address-taken locals it may reach),
// the I/O, the thread pointer, the CPU. Not the registers, and not the
// stack: frames, spilled values, return addresses and the stack's growth are
// the machine's own business (the ABI below constrains them); running out
// of stack is a C function's only contact with it (`stack_overflow`).
state World {
  vm      : Vm
  os      : Os
  fs_base : Addr          // thread pointer: TLS, errno
  cpu     : Cpu           // CPU features (fixed for the run)
  objs    : Set[nat]      // the bytes of the live stack objects (on stack pages)
}

// the world's memory: the byte at a is in its domain
pred in_domain(vm: Vm, objs: Set[nat], a: nat) =
  a in objs || (mapped(vm, a / PAGE) && vm.pages[a / PAGE].value.kind != stack)

// A C function specification: a program over the world (possibly extended
// by ghost state of higher layers), from arguments to the value in rax.
// A void function returns an arbitrary value.
type Args     = {l: List[bits[64]] | len(l) <= 6}
type CFun[S]  = proc[S](Args) -> bits[64]                   // S extends World
type CFun2[S] = proc[S](Args) -> (bits[64], bits[64])       // result in rax:rdx (a small struct)

// a single-result spec as a two-result one: rdx is clobbered
fn wide[G](spec: CFun[World & G]) -> CFun2[World & G] = (args: Args) => (spec(args), any bits[64])

const ARG_REGS     = [rdi, rsi, rdx, rcx, r8, r9]
const CALLEE_SAVED = {rbx, rbp, r12, r13, r14, r15}
const CALLEE_SAVED_LIST = [rbx, rbp, r12, r13, r14, r15]   // the same, in a fixed order

///////////////////////////////////////////////////////////////////////
//  The world as a view of the machine

pred stack_page(vm: Vm, p: nat) = mapped(vm, p) && vm.pages[p].value.kind = stack

// `new` is the machine's memory after a callee called with the stack
// pointer `sp` ran from `old`, where the callee's world ended as `w` (with
// the stack objects `objs`): on the world's domain, the world's; the stack
// pages at and above sp (the callers' frames) as they were, but for the
// objects (bytes outside the domain and the stack -- unmapped -- the
// machine's, whatever a callee left there); the
// pages the world's, or stack pages where the world has none (the stack
// grew).
pred world_matches(old: Vm, new: Vm, w: Vm, objs: Set[nat], sp: Addr) =
  top: new.stack_top = w.stack_top && limit: new.stack_limit = w.stack_limit &&
  brk0: new.brk_start = w.brk_start && brk: new.brk = w.brk &&
  bytes: (all a: Addr. in_domain(w, objs, uint(a)) -> new.bytes[a] = w.bytes[a]) &&
  frames: (all a: Addr. uint(sp) <= uint(a) && !in_domain(w, objs, uint(a)) && stack_page(old, page_of(a)) -> new.bytes[a] = old.bytes[a]) &&
  pages: (all p: PageNo. new.pages[p] = w.pages[p] || (w.pages[p] = none && stack_page(new, p)))

// `world(sp, objs, mem)` views a machine as a World, for a function called
// with the caller's stack pointer `sp`, which may reach the stack objects
// `objs` (above sp): the world's memory `mem`, a view of the machine's
// (`world_matches(vm, vm, mem, objs, sp)`: the machine's bytes on the
// world's domain, its pages but for grown stack pages -- what lies outside
// the domain is no C function's to see). Writing a world back: its domain
// the world's, the callers' frames kept, the stack below sp arbitrary (the
// callee used it).
view[Machine] world(sp: Addr, objs: Set[nat], mem: Vm) : World {
  get {
    return World { vm: mem, os, fs_base, cpu, objs }
  }
  set(w) {
    let old = vm
    havoc vm where world_matches(old, vm, w.vm, objs, sp)
    os      := w.os
    fs_base := w.fs_base
  }
}

///////////////////////////////////////////////////////////////////////
//  Machine code in memory

// The bytes `code` are loaded at `a`: fetchable, and not writable (so no
// store of the program changes them), and not on the stack (where callees
// leave arbitrary bytes).
pred code_at(vm: Vm, a: nat, code: List[bits[8]]) =
  all i: nat. i < len(code) ->
    fetchable(vm, bits[64](a + i)) && !can_access(vm, bits[64](a + i), write) && !stack_page(vm, page_of(bits[64](a + i))) &&
    vm.bytes[bits[64](a + i)] = code[i]

// `new` keeps the mapped pages of `old` and their contents: memory after
// accesses that may have grown the stack (into unmapped pages)
pred vm_grows(old: Vm, new: Vm) =
  (all p: nat. mapped(old, p) -> new.pages[p] = old.pages[p]) &&
  (all a: Addr. mapped(old, page_of(a)) -> new.bytes[a] = old.bytes[a])

///////////////////////////////////////////////////////////////////////
//  Calling a function

// No other mapping lies within the guard gap below a stack page. Linux
// keeps this gap for every mapping it places (only MAP_FIXED can break it);
// it makes a callee's stack use fault instead of overwriting other memory.
pred stack_gap_free(vm: Vm) =
  all p: nat, q: nat. stack_page(vm, p) && q < p && (p - q) * PAGE <= STACK_GUARD_GAP && mapped(vm, q) ->
    stack_page(vm, q)

// entry conditions: rsp points to the return address on the stack (its
// page writable: `call` has just written it there), rsp + 8 is 16-byte
// aligned, the direction flag is clear, arguments are in registers, and
// the thread pointer points to itself (x86-64 TLS ABI: the word at fs:0 is
// the thread pointer, which is how code finds its TLS)
pred entry_ok(m: Machine, args: Args) =
  stack_page(m.vm, uint(m.gpr[rsp]) / PAGE) && can_access(m.vm, m.gpr[rsp], write) && stack_gap_free(m.vm) &&
  uint(m.gpr[rsp] + 8) % 16 = 0 && !m.flags.df &&
  (all i: nat. i < len(args) -> m.gpr[ARG_REGS[i]] = args[i]) &&
  readable(m.vm, uint(m.fs_base), 8) && le(m.vm.bytes, m.fs_base, 8) = m.fs_base

// the thread pointer as entry_ok has it: the word at fs:0 points to itself
pred thread_ok(vm: Vm, fs: Addr) = readable(vm, uint(fs), 8) && le(vm.bytes, fs, 8) = fs

// the stack as entry_ok has it, rsp at the return address's slot: a
// writable stack page, no other mapping in the guard gap below the stack
pred stack_ok(vm: Vm, rsp: Addr) =
  stack_page(vm, uint(rsp) / PAGE) && can_access(vm, rsp, write) && stack_gap_free(vm)

// The machine, from the function's entry until it returns to its caller.
proc[Machine] run_to_return() {
  let sp  = gpr[rsp] + 8
  let ret = le(vm.bytes, gpr[rsp], 8)
  while !(rip = ret && gpr[rsp] = sp) { step() }
}

///////////////////////////////////////////////////////////////////////
//  Stack overflow
//
// The implementation may run out of stack inside the function: an access
// to its stack faults (the stack cannot grow further). The process
// dies: memory and registers no longer matter, but the I/O done so far
// does. Policy: the spec says where it may overflow (`stack_overflow`), and
// the crash's I/O is that of such a point of the spec -- or of one where
// the spec does no more I/O (it returns, or runs on silently).

// Where a stack overflow faults, as the machine has it at the fault (vm,
// rsp): below the function's sp, every page from the address up to rsp's
// a stack page or unmapped -- a push or a frame access the stack could not
// grow to. Stated at the fault, not at the entry: the page map may change
// in between (munmap), and a callee's overflow is then its caller's (its
// sp is lower).
pred overflow_at(vm: Vm, rsp: Addr, sp: Addr, a: Addr) =
  uint(a) < uint(sp) &&
  (all p: nat. uint(a) / PAGE <= p && p <= uint(rsp) / PAGE -> stack_page(vm, p) || !mapped(vm, p))

// Specs say where a stack overflow may stop them: the exception
// `stack_overflow` (no undefined behavior, see `spec_raises`). Readable
// GIMPLE may overflow at every call; a spec above it at every call or
// stack push it models. (The machine itself has no such exception: it
// faults with segv, overflow_at.)
exception stack_overflow

// a crash state's I/O is the entry's (the call itself overflowed: the
// function's frame, before it did anything -- as GIMPLE's call may overflow
// before its callee runs), or that of some outcome the spec allows from
// `w` where the I/O stops: a stack overflow, a normal return (the crash
// came after the last I/O), or an infinite run with that trace
pred overflow_ok[S](w: S, spec: CFun2[S], args: Args, crash: Os) =
  input: w.os.input = crash.input &&
  events: (at_call: w.os.events = crash.events ||
  ex o: Outcome[S, (bits[64], bits[64])]. outcome(w, spec(args), o) && match o {
    ok(s, _)   => s.os.events = crash.events
    exc(s, e)  => e = stack_overflow && s.os.events = crash.events
    diverge(t) => t.os.events = crash.events
  })

///////////////////////////////////////////////////////////////////////
//  Undefined behavior

// The spec may raise from `w`. A C function's spec raises only through
// undefined behavior (`undefined` allows every outcome of the spec,
// exceptions included) or a deliberate crash (e.g. a_crash). In both cases
// the implementation owes nothing: in C, undefined behavior makes the whole
// run undefined, and a program's top-level spec (malloc's) never raises, so
// it excludes both. A stack overflow is not raising: the implementation
// then crashes as `overflow_ok` allows.
pred spec_raises[S](w: S, spec: CFun2[S], args: Args) =
  ex o: Outcome[S, (bits[64], bits[64])]. outcome(w, spec(args), o) && match o {
    ok(_, _)   => false
    exc(_, e)  => e != stack_overflow
    diverge(_) => false
  }

///////////////////////////////////////////////////////////////////////
//  What the ABI promises

// The parts of a normal return (separate, so that proofs can take them one
// at a time): the spec run on the world, its result in rax:rdx
proc[Machine & G] abi_call[G](spec: CFun2[World & G], args: Args, sp: Addr, objs: Set[nat], mem: Vm) -> (bits[64], bits[64]) {
  let (r0, r1) = with world(sp, objs, mem) { return spec(args) }
  return (r0, r1)
}

// the callee-saved registers back to their values at entry
proc[Machine] abi_restore(saved: Reg -> bits[64]) {
  for reg in CALLEE_SAVED_LIST { gpr[reg] := saved[reg] }
}

// the caller's stack pointer, the result, df clear, back to the caller
proc[Machine] abi_set_result(sp: Addr, ret: Addr, r0: bits[64], r1: bits[64]) {
  gpr[rsp]  := sp
  gpr[rax]  := r0
  gpr[rdx]  := r1
  flags.df  := false
  rip       := ret
}

// From entry to return: the function behaves like `spec` on the world (with
// the stack objects `objs` of its callers it may reach: above sp, on their
// writable stack pages), whichever view `mem` of the machine's memory is
// the world's;
// callee-saved registers and rsp are restored, rax holds the result, other
// registers (including all XMM registers) and flags are clobbered. Or it runs
// out of stack (see above: also right at the call, before any I/O): a
// fault of a stack access -- a page the stack cannot grow to, or a
// non-canonical address (the stack's address wrapped).
// If the spec may raise (undefined behavior), anything.
proc[Machine & G] abi_function[G](f: Addr, spec: CFun2[World & G], args: Args, objs: Set[nat], mem: Vm) {
  require rip = f && entry_ok(self, args)
  let sp    = gpr[rsp] + 8
  require all a: nat. a in objs -> uint(sp) <= a && stack_page(vm, a / PAGE) && can_access(vm, bits[64](a), write)
  require world_matches(vm, vm, mem, objs, sp)
  let ret   = le(vm.bytes, gpr[rsp], 8)
  let saved = gpr
  let w0    = with world(sp, objs, mem) { return self }    // the world, with ghost state
  require !spec_raises(w0, spec, args)
  either {
    let (r0, r1) = abi_call(spec, args, sp, objs, mem)
    havoc gpr, xmm, flags
    abi_restore(saved)
    abi_set_result(sp, ret, r0, r1)
  } or {
    havoc self where overflow_ok(w0, spec, args, os)
    either {
      let a = any Addr where overflow_at(vm, gpr[rsp], sp, a)
      either { raise segv(a, maperr) } or { raise segv(a, accerr) }
    } or { raise stack_fault }
  }
}

// Machine code at `f` implements `spec`.
//
// `refines` with ghost fields G on the right: for every initial ghost value,
// each machine outcome is matched by a spec outcome for *some* final ghost
// value (the proof chooses it; a forward simulation).
pred implements2[G](f: Addr, spec: CFun2[World & G]) =
  all args: Args, objs: Set[nat], mem: Vm. run_to_return() refines abi_function(f, spec, args, objs, mem)

pred implements[G](f: Addr, spec: CFun[World & G]) = implements2(f, wide(spec))

// The program is loaded: its code (the executable segment `code`, at
// `base`) is in memory, and its static data (the addresses `statics`) is
// mapped and not on the stack -- the ELF's segments are mapped at load,
// and the stack grows only into unmapped pages. (Otherwise a store to a
// global could overwrite a return address, which the ABI cannot allow
// for.)
pred loaded(vm: Vm, base: nat, code: List[bits[8]], statics: Set[nat]) =
  code_at(vm, base, code) && (all a: nat. a in statics -> mapped(vm, a / PAGE) && !stack_page(vm, a / PAGE))

// ... provided the program is loaded: the contract of a function inside
// the program, which only its callers use. Every function of a program
// assumes the same, so callers and callees have the same precondition;
// the program's entry points (e.g. malloc) show it from their own spec.
pred implements2_at[G](f: Addr, spec: CFun2[World & G], base: nat, code: List[bits[8]], statics: Set[nat]) =
  all args: Args, objs: Set[nat], mem: Vm. run_to_return() refines do[Machine & G] { require loaded(vm, base, code, statics); abi_function(f, spec, args, objs, mem) }

// A spec keeps the program loaded: from a world where it is, every outcome
// still has it (a frame property, proven for each function at the C level;
// a caller needs it to go on after a call).
pred keeps_code[S](spec: CFun2[S], base: nat, code: List[bits[8]], statics: Set[nat]) =
  all args: Args, w: S, o: Outcome[S, (bits[64], bits[64])].
    loaded(w.vm, base, code, statics) && outcome(w, spec(args), o) ->
      match o {
        ok(s, _)  => loaded(s.vm, base, code, statics)
        exc(s, _) => loaded(s.vm, base, code, statics)
        diverge(_) => true
      }

///////////////////////////////////////////////////////////////////////
//  Using it

// The call rule: at a call site `call f` (after the arguments are set up),
// the machine may be reasoned about as the spec. Follows from the
// definitions; proven once, used at every call site.
theorem call_rule[G](f: Addr, spec: CFun2[World & G], args: Args, objs: Set[nat], mem: Vm):
  implements2(f, spec) ->
    do[Machine] { call_abs(f); run_to_return() } refines do[Machine & G] { push(rip); rip := f; abi_function(f, spec, args, objs, mem) }

// ... for a function inside the program: at the call, the program must be
// loaded.
theorem call_rule_at[G](f: Addr, spec: CFun2[World & G], args: Args, objs: Set[nat], mem: Vm, base: nat, code: List[bits[8]], statics: Set[nat]):
  implements2_at(f, spec, base, code, statics) ->
    do[Machine] { call_abs(f); run_to_return() } refines do[Machine & G] { require loaded(vm, base, code, statics); push(rip); rip := f; abi_function(f, spec, args, objs, mem) }
