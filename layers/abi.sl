layer abi uses x86_64_linux

// System V x86_64 calling convention, as an abstraction over the machine.
// Nothing here is assumed about the computer: everything is a definition, and
// the claims (e.g. "glibc's malloc implements its spec") are theorems to prove.
//
// Covered: up to 6 integer/pointer arguments, integer/pointer result in rax.
// Not yet: stack-passed or floating-point arguments, struct returns, varargs.

///////////////////////////////////////////////////////////////////////
//  What a C function sees

// The part of the machine that a C function can see and change: everything
// except registers. The stack below the caller's stack pointer is the
// callee's scratch space; the view `world` hides its contents.
state World {
  vm      : Vm
  os      : Os
  fs_base : Addr          // thread pointer: TLS, errno
  cpu     : Cpu           // CPU features (fixed for the run)
  sp      : Addr          // the caller's stack pointer: memory below is the function's scratch
}

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

///////////////////////////////////////////////////////////////////////
//  The world as a view of the machine

pred stack_page(vm: Vm, p: nat) = mapped(vm, p) && vm.pages[p].value.kind = stack

// Scratch space of a callee: the stack below `sp` and the free space right
// below it, into which the stack can grow -- the pages from `a` up to `sp`
// are all stack pages or unmapped. (Not bounded by RLIMIT_STACK: growth
// beyond it faults, and with an unlimited limit the stack may grow down to
// the next mapping.)
pred scratch(vm: Vm, sp: Addr, a: nat) =
  a < uint(sp) &&
  (all p: nat. a / PAGE <= p && p <= uint(sp) / PAGE -> stack_page(vm, p) || !mapped(vm, p))

pred scratch_page(vm: Vm, sp: Addr, p: nat) = scratch(vm, sp, p * PAGE + PAGE - 1)

// memory with the contents of the scratch space normalised to zero (its
// pages stay visible: stack pages are not free memory)
fn clean(vm: Vm, sp: Addr) -> Vm = vm with {
  bytes: (a: Addr) => if scratch(vm, sp, uint(a)) { 0 } else { vm.bytes[a] }
}

// `new` is the machine's memory after a callee ran from `old`, where the
// callee's world ended as `w`: outside the scratch space they agree; in it,
// the contents are arbitrary and the stack may have grown into free pages.
pred world_matches(old: Vm, new: Vm, w: Vm, sp: Addr) =
  new.stack_top = w.stack_top && new.stack_limit = w.stack_limit &&
  new.brk_start = w.brk_start && new.brk = w.brk &&
  (all a: nat. !scratch(old, sp, a) -> new.bytes[bits[64](a)] = w.bytes[bits[64](a)]) &&
  (all p: PageNo. new.pages[p] = w.pages[p] ||
     (scratch_page(old, sp, p) && w.pages[p] = none && stack_page(new, p)))

// `world(sp)` views a machine as a World, for a function called with the
// caller's stack pointer `sp`. Writing a world back leaves the scratch space
// arbitrary: a callee may have used (and grown) the stack there.
view[Machine] world(sp: Addr) : World {
  get = World { vm: clean(vm, sp), os, fs_base, cpu, sp }
  set(w) {
    let old = vm
    havoc vm where world_matches(old, vm, w.vm, sp)
    os      := w.os
    fs_base := w.fs_base
  }
}

///////////////////////////////////////////////////////////////////////
//  Machine code in memory

// The bytes `code` are loaded at `a`: fetchable, and not writable (so no
// store of the program changes them).
pred code_at(vm: Vm, a: nat, code: List[bits[8]]) =
  all i: nat. i < len(code) ->
    fetchable(vm, bits[64](a + i)) && !can_access(vm, bits[64](a + i), write) && vm.bytes[bits[64](a + i)] = code[i]

///////////////////////////////////////////////////////////////////////
//  Calling a function

// No other mapping lies within the guard gap below a stack page. Linux
// keeps this gap for every mapping it places (only MAP_FIXED can break it);
// it makes a callee's stack use fault instead of overwriting other memory.
pred stack_gap_free(vm: Vm) =
  all p: nat, q: nat. stack_page(vm, p) && q < p && (p - q) * PAGE <= STACK_GUARD_GAP && mapped(vm, q) ->
    stack_page(vm, q)

// entry conditions: rsp points to the return address on the stack, rsp + 8
// is 16-byte aligned, the direction flag is clear, arguments are in
// registers, and the thread pointer points to itself (x86-64 TLS ABI: the
// word at fs:0 is the thread pointer, which is how code finds its TLS)
pred entry_ok(m: Machine, args: Args) =
  stack_page(m.vm, uint(m.gpr[rsp]) / PAGE) && stack_gap_free(m.vm) &&
  uint(m.gpr[rsp] + 8) % 16 = 0 && !m.flags.df &&
  (all i: nat. i < len(args) -> m.gpr[ARG_REGS[i]] = args[i]) &&
  readable(m.vm, uint(m.fs_base), 8) && le(m.vm.bytes, m.fs_base, 8) = m.fs_base

// The machine, from the function's entry until it returns to its caller.
proc[Machine] run_to_return() {
  let sp  = gpr[rsp] + 8
  let ret = le(vm.bytes, gpr[rsp], 8)
  while !(rip = ret && gpr[rsp] = sp) { step() }
}

///////////////////////////////////////////////////////////////////////
//  Crashes the spec cannot foresee (stack overflow)
//
// A C-level spec knows nothing about stack usage, so the implementation may
// run out of stack at any point inside the function: an access to its
// scratch space faults (the stack cannot grow further). The process dies:
// memory and registers no longer matter, but the I/O done so far does.
// Policy: that I/O is the beginning of some complete behavior the spec
// allows. (Sound: the crashed run is the same as a run with a larger stack
// limit, cut short, and that run is allowed by the spec.)

// a crash state's I/O lies between the entry and some complete outcome the
// spec allows from `w` -- including infinite runs, whose outcome carries the
// limit of their (possibly infinite) trace
pred crash_io_ok[S](w: S, spec: CFun2[S], args: Args, crash: Os) =
  w.os.input = crash.input && w.os.events <= crash.events &&
  ex o: Outcome[S, (bits[64], bits[64])]. outcome(w, spec(args), o) && match o {
    ok(s, _)   => crash.events <= s.os.events
    exc(s, _)  => crash.events <= s.os.events
    diverge(t) => crash.events <= t.os.events
  }

///////////////////////////////////////////////////////////////////////
//  What the ABI promises

// From entry to return: the function behaves like `spec` on the world;
// callee-saved registers and rsp are restored, rax holds the result, other
// registers (including all XMM registers) and flags are clobbered. Or it runs out of stack (see above).
proc[Machine & G] abi_function[G](f: Addr, spec: CFun2[World & G], args: Args) {
  require rip = f && entry_ok(self, args)
  let sp    = gpr[rsp] + 8
  let ret   = le(vm.bytes, gpr[rsp], 8)
  let saved = gpr
  either {
    let (r0, r1) = with world(sp) { return spec(args) }
    havoc gpr, xmm, flags
    for reg in CALLEE_SAVED { gpr[reg] := saved[reg] }
    gpr[rsp]  := sp
    gpr[rax]  := r0
    gpr[rdx]  := r1
    flags.df  := false
    rip       := ret
  } or {
    let w0 = with world(sp) { return self }    // the world, with ghost state
    let vm0 = vm
    let a = any Addr where scratch(vm0, sp, uint(a))
    havoc self where crash_io_ok(w0, spec, args, os)
    either { raise segv(a, maperr) } or { raise segv(a, accerr) }
  }
}

// Machine code at `f` implements `spec`.
//
// `refines` with ghost fields G on the right: for every initial ghost value,
// each machine outcome is matched by a spec outcome for *some* final ghost
// value (the proof chooses it; a forward simulation).
pred implements2[G](f: Addr, spec: CFun2[World & G]) =
  all args: Args. run_to_return() refines abi_function(f, spec, args)

pred implements[G](f: Addr, spec: CFun[World & G]) = implements2(f, wide(spec))

///////////////////////////////////////////////////////////////////////
//  Using it

// The call rule: at a call site `call f` (after the arguments are set up),
// the machine may be reasoned about as the spec. Follows from the
// definitions; proven once, used at every call site.
theorem call_rule[G](f: Addr, spec: CFun2[World & G], args: Args):
  implements2(f, spec) ->
    do[Machine] { call_abs(f); run_to_return() } refines do[Machine & G] { push(rip); rip := f; abi_function(f, spec, args) }
