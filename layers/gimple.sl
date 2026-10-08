layer gimple uses abi, x86_64_linux

// GCC's GIMPLE (the optimized form, after all tree-level optimizations), as
// an implementation level between machine code and C function specs.
//
// A GIMPLE function means a C function spec: `gimple_fun(f, callees)` is a
// `CFun2[World]`. So the relation to machine code is the ABI's
//
//     implements2(address, gimple_fun(f, callees))
//
// ("the compiled function behaves like its GIMPLE"), and a proof about the
// GIMPLE (it refines e.g. `malloc_fun()`) carries over to the machine code.
// For proving that relation function by function, `coupled` below relates a
// running GIMPLE function to the machine at corresponding program points.
//
// Nothing here is trusted: a wrong detail can make a proof fail, never make
// a false claim provable. Programs are given in a normalized form produced
// from GCC's dumps (names numbered, fields resolved to offsets, aggregate
// stores split into bytes, globals replaced by their addresses).

///////////////////////////////////////////////////////////////////////
//  Syntax

type Name = nat                   // SSA names and variables whose address is not taken

// An integer type: precision in bits, signedness. Pointers are unsigned
// 64-bit, _Bool has precision 1, vectors are 128-bit integers.
record Ty { prec: nat, signed: bool }

type Opnd = ssa(x: Name)       // the value of a name
             | cst(v: nat)        // a constant (in the operation's type)
             | obj(k: nat)        // the address of stack object k

enum UOp { neg, bnot, copy, realpart, imagpart }

enum BinOp {
  add, sub, mul, div, mod,        // div / mod truncate toward zero
  band, bor, bxor, shl, shr,      // shr is arithmetic for signed types
  eq, ne, lt, le, gt, ge,         // results are _Bool (0 or 1)
  min, max,
  ptr_add                         // pointer + offset (the offset is signed, 64-bit)
}

// GCC internal functions (`.CTZ (x, 32)` ...)
type IFn = ctz                    // trailing zeros; a second argument gives the value for 0
         | sat_sub                // unsigned a - b, or 0
         | mul_overflow           // real part: the product; imaginary part: 1 on overflow
         | reduc_ior(lanes: nat)  // bitwise or of the lanes of a vector

type Rhs = unary(op: UOp, ty: Ty, a: Opnd)
         | binary(op: BinOp, ty: Ty, a: Opnd, b: Opnd)   // ty: the operands' type
         | convert(from: Ty, to: Ty, a: Opnd)
         | internal(f: IFn, ty: Ty, args: List[Opnd])

// A memory access: `size` bytes at base + off, aligned to `align` bytes;
// for a bitfield, `bits` > 0 bits at bit position `bitpos` within them.
record Loc { base: Opnd, off: bits[64], size: nat, align: nat, bitpos: nat, bits: nat }

type Stmt = assign(dst: Name, rhs: Rhs)
          | load(dst: Name, loc: Loc, ty: Ty)
          | store(loc: Loc, v: Opnd)
          | store_bytes(loc: Loc, data: List[bits[8]])         // constant aggregates
          | call(dsts: List[(Name, Ty)], f: nat, args: List[(Opnd, Ty)])
          | asm(code: List[bits[8]], ins: List[(Reg, Opnd)], outs: List[(Name, Ty, Reg)])

type Jump = goto(b: nat)
          | branch(op: BinOp, ty: Ty, a: Opnd, c: Opnd, yes: nat, no: nat)
          | ret(vals: List[(Opnd, Ty)])                      // 0, 1 or 2 values (rax, rdx)

// phi: the value of `dst` on entry, by predecessor block
record Phi { dst: Name, args: List[(nat, Opnd)] }

record Block { phis: List[Phi], body: List[Stmt], jump: Jump }

// A function: typed parameters, the types of its names, its stack objects
// (size, alignment: variables whose address is taken), blocks, entry block.
record Function {
  params : List[(Name, Ty)]
  types  : Name -> Ty
  objs   : List[(nat, nat)]
  blocks : List[Block]
  entry  : nat
}

///////////////////////////////////////////////////////////////////////
//  Integers

fn wrap(ty: Ty, v: int) -> nat = v % 2^ty.prec

// the value as a mathematical integer (two's complement if signed)
fn sval(ty: Ty, v: nat) -> int =
  if ty.signed && v >= 2^(ty.prec - 1) { v - 2^ty.prec } else { v }

pred fits(ty: Ty, x: int) =
  if ty.signed { -(2^(ty.prec - 1)) <= x && x < 2^(ty.prec - 1) } else { 0 <= x && x < 2^ty.prec }

// signed overflow is undefined; unsigned arithmetic wraps
proc[World] arith(ty: Ty, x: int) -> nat {
  if ty.signed && !fits(ty, x) { undefined }
  return wrap(ty, x)
}

fn b128(v: nat) -> bits[128] = bits[128](v)

fn set_val(m: Name -> nat, x: Name, v: nat) -> Name -> nat = (y: Name) => if y = x { v } else { m[y] }
fn set_reg(m: Reg -> bits[64], r: Reg, v: bits[64]) -> Reg -> bits[64] = (q: Reg) => if q = r { v } else { m[q] }

proc[World] binop(op: BinOp, ty: Ty, a: nat, b: nat) -> nat {
  let x = sval(ty, a)
  let y = sval(ty, b)
  match op {
    add  => return arith(ty, x + y)
    sub  => return arith(ty, x - y)
    mul  => return arith(ty, x * y)
    div  => { if y = 0 { undefined }; return arith(ty, tdiv(x, y)) }
    mod  => { if y = 0 { undefined }; let q = arith(ty, tdiv(x, y)); return wrap(ty, x - y * tdiv(x, y)) }
    band => return uint(b128(a) & b128(b))
    bor  => return uint(b128(a) | b128(b))
    bxor => return uint(b128(a) xor b128(b))
    shl  => { if b >= ty.prec { undefined }; return wrap(ty, a * 2^b) }
    shr  => { if b >= ty.prec { undefined }; return wrap(ty, x / 2^b) }      // floor: arithmetic
    eq   => return if x = y { 1 } else { 0 }
    ne   => return if x != y { 1 } else { 0 }
    lt   => return if x < y { 1 } else { 0 }
    le   => return if x <= y { 1 } else { 0 }
    gt   => return if x > y { 1 } else { 0 }
    ge   => return if x >= y { 1 } else { 0 }
    min  => return if x <= y { a } else { b }
    max  => return if x >= y { a } else { b }
    ptr_add => {
      // pointer arithmetic may not wrap around the address space
      let r = a + sval(Ty { prec: 64, signed: true }, b)
      if r < 0 || r >= 2^64 { undefined }
      return r
    }
  }
}

proc[World] unop(op: UOp, ty: Ty, a: nat) -> nat {
  match op {
    neg      => return arith(ty, -sval(ty, a))
    bnot     => return wrap(ty, -a - 1)
    copy     => return a
    realpart => return a % 2^ty.prec              // ty: the type of a component
    imagpart => return a / 2^ty.prec % 2^ty.prec
  }
}

// trailing zeros of a nonzero number
fn tz(v: nat) -> nat = min({k: nat | k < 128 && v / 2^k % 2 = 1})

proc[World] ifn(f: IFn, ty: Ty, args: List[nat]) -> nat {
  match f {
    ctz => {
      if args[0] = 0 {
        if len(args) < 2 { undefined }
        return args[1]
      }
      return tz(args[0])
    }
    sat_sub      => return if args[0] > args[1] { args[0] - args[1] } else { 0 }
    mul_overflow => {
      let p = sval(ty, args[0]) * sval(ty, args[1])
      return wrap(ty, p) + 2^ty.prec * (if fits(ty, p) { 0 } else { 1 })
    }
    reduc_ior(n) => {
      var r = 0
      for i in 0..n { r := uint(b128(r) | b128(args[0] / 2^(i * ty.prec) % 2^ty.prec)) }
      return r
    }
  }
}

///////////////////////////////////////////////////////////////////////
//  The state of a running function

// The frame: values of names, addresses of stack objects, the current
// block and the block it was entered from (for phis).
record Frame { vals: Name -> nat, objs: List[Addr], bb: nat, prev: nat }

fn operand(fr: Frame, o: Opnd) -> nat =
  match o { ssa(x) => fr.vals[x], cst(v) => v, obj(k) => uint(fr.objs[k]) }

// The memory a GIMPLE access may use: readable / writable (C objects are
// never write-only), and aligned. Anything else is undefined (GCC may
// remove, reorder or speculate accesses that are valid in C).
pred usable(vm: Vm, a: nat, n: nat, w: bool) =
  all i: nat. i < n -> mapped(vm, (a + i) / PAGE) &&
    (if w { vm.pages[(a + i) / PAGE].value.prot.w } else { vm.pages[(a + i) / PAGE].value.prot.r })

// An access through a null base pointer is undefined, whatever is mapped at
// page 0: no C object is there, and GCC relies on it (a dereferenced pointer
// is non-null: `-fdelete-null-pointer-checks` removes later null tests). The
// Linux model never maps page 0 on its own (docs/spec-language.md, 12), so
// programs can show they avoid this.
proc[World] address(fr: Frame, loc: Loc, w: bool) -> Addr {
  if operand(fr, loc.base) = 0 { undefined }
  let a = binop(ptr_add, Ty { prec: 64, signed: false }, operand(fr, loc.base), uint(loc.off))
  if a % loc.align != 0 || !usable(vm, a, loc.size, w) { undefined }
  return bits[64](a)
}

// the n bytes at a as a number (little-endian)
fn bytes_at(vm: Vm, a: Addr, n: nat) -> nat = sum i in 0..n. uint(vm.bytes[a + bits[64](i)]) * 256^i

proc[World] write_bytes(a: Addr, n: nat, v: nat) {
  for i in 0..n { vm.bytes[a + bits[64](i)] := bits[8](v / 256^i) }
}

// Stack objects are placed in the scratch space below `sp` (anywhere GCC's
// frame layout may put them), disjoint and aligned; their contents are
// arbitrary. The stack grows as needed (running out of stack is the ABI's
// crash case). `sp` then is the lowest object: the objects are the
// function's, no longer scratch (calls go below them).
proc[World] alloc_objs(objs: List[(nat, nat)]) -> List[Addr] {
  let addrs = any l: List[Addr] where len(l) = len(objs) &&
    (all k: nat. k < len(objs) ->
       uint(l[k]) % objs[k][1] = 0 &&
       (all a: nat. uint(l[k]) <= a && a < uint(l[k]) + objs[k][0] -> scratch(vm, sp, a))) &&
    (all j: nat, k: nat. j < k && k < len(objs) ->
       uint(l[j]) + objs[j][0] <= uint(l[k]) || uint(l[k]) + objs[k][0] <= uint(l[j]))
  for k in 0..len(objs) {
    for a in uint(addrs[k]) .. uint(addrs[k]) + objs[k][0] { grow_to(a) }
    for i in 0..objs[k][0] { vm.bytes[addrs[k] + bits[64](i)] := any bits[8] }
  }
  sp := bits[64](min({a: nat | a = uint(sp) || (ex j: nat. j < len(addrs) && a = uint(addrs[j]))}))
  return addrs
}

// the stack now reaches down to address a: unmapped pages from a up to sp
// become stack pages
proc[World] grow_to(a: nat) {
  for p in a / PAGE .. uint(sp) / PAGE {
    if !mapped(vm, p) {
      vm.pages[p] := some(Page { prot: Prot { r: true, w: true, x: false }, kind: stack })
      for i in p * PAGE .. (p + 1) * PAGE { vm.bytes[bits[64](i)] := 0 }
    }
  }
}

///////////////////////////////////////////////////////////////////////
//  Readable GIMPLE: the operations
//
// `slc gimple --readable` translates each function to an SL proc close to
// the C source: C variables keep their names, integers are words of their
// precision (`bits[n]`; signedness is in the operations: `<s`, `>>s`,
// `sext`), struct fields are read and written through accessors generated
// from DWARF, and called functions are parameters (their specs, once
// proven). Unsigned arithmetic and bitwise operations are SL's own; the
// operations below are GIMPLE's where it has undefined behaviour: signed
// overflow, shifts by the width or more, division by zero, null or unusable
// memory, pointer arithmetic leaving the address space. Like the rest of
// this layer, nothing here is trusted: machine code is checked against the
// translation, and proofs about the translation carry over.

proc[World] sadd[n: nat](a: bits[n], b: bits[n]) -> bits[n] { return bits[n](arith(Ty { prec: n, signed: true }, sint(a) + sint(b))) }
proc[World] ssub[n: nat](a: bits[n], b: bits[n]) -> bits[n] { return bits[n](arith(Ty { prec: n, signed: true }, sint(a) - sint(b))) }
proc[World] smul[n: nat](a: bits[n], b: bits[n]) -> bits[n] { return bits[n](arith(Ty { prec: n, signed: true }, sint(a) * sint(b))) }
proc[World] sneg[n: nat](a: bits[n]) -> bits[n] { return bits[n](arith(Ty { prec: n, signed: true }, -sint(a))) }

// division and remainder (truncating); `signed` as in C
proc[World] cdiv[n: nat](a: bits[n], b: bits[n], signed: bool) -> bits[n] {
  return bits[n](binop(div, Ty { prec: n, signed: signed }, uint(a), uint(b)))
}
proc[World] crem[n: nat](a: bits[n], b: bits[n], signed: bool) -> bits[n] {
  return bits[n](binop(mod, Ty { prec: n, signed: signed }, uint(a), uint(b)))
}

// shifts by fewer bits than the width
proc[World] shl[n: nat](a: bits[n], k: nat) -> bits[n] { if k >= n { undefined }; return a << k }
proc[World] shr[n: nat](a: bits[n], k: nat) -> bits[n] { if k >= n { undefined }; return a >> k }
proc[World] sar[n: nat](a: bits[n], k: nat) -> bits[n] { if k >= n { undefined }; return a >>s k }

fn smin[n: nat](a: bits[n], b: bits[n]) -> bits[n] = if a <=s b { a } else { b }
fn smax[n: nat](a: bits[n], b: bits[n]) -> bits[n] = if a >=s b { a } else { b }
fn umin[n: nat](a: bits[n], b: bits[n]) -> bits[n] = if a <= b { a } else { b }
fn umax[n: nat](a: bits[n], b: bits[n]) -> bits[n] = if a >= b { a } else { b }

// a condition as a _Bool (precision 1)
fn b1(c: bool) -> bits[1] = if c { 1 } else { 0 }

// GCC's internal functions: the product and whether it overflowed (a
// complex value: real part low, imaginary part high); trailing zeros
// (undefined for 0 without a value for it)
fn mul_ovf[n: nat](a: bits[n], b: bits[n], signed: bool) -> bits[2*n] = bits[2*n](
  (if signed { sint(a) * sint(b) } else { uint(a) * uint(b) }) % 2^n +
  2^n * (if fits(Ty { prec: n, signed: signed }, if signed { sint(a) * sint(b) } else { uint(a) * uint(b) }) { 0 } else { 1 }))
proc[World] ctz[n: nat](a: bits[n]) -> bits[n] { if a = 0 { undefined }; return bits[n](tz(uint(a))) }

// pointer + signed offset: may not leave the address space
proc[World] padd(p: Addr, off: bits[64]) -> Addr {
  return bits[64](binop(ptr_add, Ty { prec: 64, signed: false }, uint(p), uint(off)))
}

// the address of `size` bytes of a C object at p + off: p is not null, the
// bytes are usable (readable; writable for `w`)
// Scratch memory (below the stack pointer: the function's own stack, where
// the machine keeps the values C does not see) holds no C object but the
// function's stack objects, which `alloc_objs` puts above `sp`: an access
// there is through a dangling pointer, undefined.
pred unscratched(vm: Vm, sp: Addr, a: nat, n: nat) = all i: nat. i < n -> !scratch(vm, sp, a + i)

proc[World] mem(p: Addr, off: bits[64], size: nat, w: bool) -> Addr {
  if p = 0 { undefined }
  let a = padd(p, off)
  if !usable(vm, uint(a), size, w) || !unscratched(vm, sp, uint(a), size) { undefined }
  return a
}

proc[World] ld8(p: Addr, off: bits[64]) -> bits[8] { return bits[8](bytes_at(vm, mem(p, off, 1, false), 1)) }
proc[World] ld16(p: Addr, off: bits[64]) -> bits[16] { return bits[16](bytes_at(vm, mem(p, off, 2, false), 2)) }
proc[World] ld32(p: Addr, off: bits[64]) -> bits[32] { return bits[32](bytes_at(vm, mem(p, off, 4, false), 4)) }
proc[World] ld64(p: Addr, off: bits[64]) -> bits[64] { return bits[64](bytes_at(vm, mem(p, off, 8, false), 8)) }
proc[World] ld128(p: Addr, off: bits[64]) -> bits[128] { return bits[128](bytes_at(vm, mem(p, off, 16, false), 16)) }

proc[World] st8(p: Addr, off: bits[64], v: bits[8]) { write_bytes(mem(p, off, 1, true), 1, uint(v)) }
proc[World] st16(p: Addr, off: bits[64], v: bits[16]) { write_bytes(mem(p, off, 2, true), 2, uint(v)) }
proc[World] st32(p: Addr, off: bits[64], v: bits[32]) { write_bytes(mem(p, off, 4, true), 4, uint(v)) }
proc[World] st64(p: Addr, off: bits[64], v: bits[64]) { write_bytes(mem(p, off, 8, true), 8, uint(v)) }
proc[World] st128(p: Addr, off: bits[64], v: bits[128]) { write_bytes(mem(p, off, 16, true), 16, uint(v)) }

// constant bytes (aggregate initializers)
proc[World] st_bytes(p: Addr, off: bits[64], data: List[bits[8]]) {
  let a = mem(p, off, len(data), true)
  for i in 0..len(data) { vm.bytes[a + bits[64](i)] := data[i] }
}

// a bitfield: `bits` bits at bit `pos` of the `size` bytes at p + off
proc[World] ldbf(p: Addr, off: bits[64], size: nat, pos: nat, bits: nat) -> nat {
  return bytes_at(vm, mem(p, off, size, false), size) / 2^pos % 2^bits
}
proc[World] stbf(p: Addr, off: bits[64], size: nat, pos: nat, bits: nat, v: nat) {
  let a = mem(p, off, size, true)
  let old = bytes_at(vm, a, size)
  let m = 2^pos * (2^bits - 1)
  write_bytes(a, size, uint(b128(old) & ~b128(m)) + (v % 2^bits) * 2^pos)
}

///////////////////////////////////////////////////////////////////////
//  Calls and inline assembly

// A called function sees the world with its own stack pointer (below the
// caller's stack objects); afterwards the stack below it is arbitrary.
view[World] callee_world(sp2: Addr) : World {
  get {
    let v = any Vm where scratch_view(v, vm, sp2)
    return World { vm: v, os, fs_base, cpu, sp: sp2 }
  }
  set(w) {
    let old = vm
    havoc vm where world_matches(old, vm, w.vm, sp2)
    os      := w.os
    fs_base := w.fs_base
  }
}

// The machine inline assembly runs on: the world, and registers (the
// operands in theirs, everything else arbitrary).
view[World] asm_machine(regs: Reg -> bits[64], xregs: Reg -> bits[128], fl: Flags, gs: Addr) : Machine {
  get = Machine { gpr: regs, xmm: xregs, rip: 0, flags: fl, cpu, fs_base, gs_base: gs, vm, os }
  set(m) {
    vm      := m.vm
    os      := m.os
    fs_base := m.fs_base
  }
}

// executes instruction bytes with the machine's own semantics; returns the
// registers afterwards
proc[Machine] run_code(code: List[bits[8]]) -> Reg -> bits[64] {
  var pos = 0
  while pos < len(code) {
    let ms = x86.decode((i: nat) => if pos + i < len(code) { code[pos + i] } else { 0 })
    if ms = {} { undefined }
    let (n, insn) = any m: (nat, x86.Insn) where m in ms
    pos := pos + n
    rip := rip + bits[64](n)
    x86.execute(insn)
  }
  return gpr
}

// a value passed in a 64-bit register: the upper bits are unspecified
fn in_reg(v: nat, ty: Ty) -> Set[bits[64]] = {r: bits[64] | uint(r) % 2^ty.prec = v % 2^ty.prec}

// The caller's frame at a call to a callee with stack pointer sp2: the
// stack may have grown down to the return address's slot below sp2 (free
// pages mapped, their bytes new; the call checks they are stack pages),
// and the bytes from that slot up to `hi` --
// the caller's private frame [sp2, hi), below its stack pointer and
// holding none of its C objects -- are arbitrary: the caller's machine
// code keeps values there that C does not see.
pred frame_at_call(old: Vm, new: Vm, sp2: Addr, hi: nat) =
  new.stack_top = old.stack_top && new.stack_limit = old.stack_limit &&
  new.brk_start = old.brk_start && new.brk = old.brk &&
  (all a: Addr. !(uint(sp2) - 8 <= uint(a) && uint(a) < hi) && mapped(old, page_of(a)) -> new.bytes[a] = old.bytes[a]) &&
  (all p: PageNo. new.pages[p] = old.pages[p] ||
     ((uint(sp2) - 8) / PAGE <= p && p * PAGE < hi && old.pages[p] = none))

// Calling g: the arguments (values with their types) in registers, g on
// its own stack below `low` (the stack pointer, or the lowest stack object
// of the caller); the result registers rax, rdx. The caller's private
// frame [sp2, hi) is the caller's own: a callee that changes it (its bytes
// or its pages) is undefined (C: none of the caller's objects it may
// access is there). A
// call with the thread pointer broken (the word at fs:0 not pointing to
// itself, as the ABI requires at every call) or the stack unsound (the
// return address's slot not a writable stack page, a mapping in the guard
// gap: the ABI's entry conditions) is undefined. Every call may
// overflow the stack (`stack_overflow`, the ABI's: no undefined behavior),
// before the callee runs and after it returns.
proc[World] call_at(low: nat, hi: nat, g: CFun2[World], args: List[(nat, Ty)]) -> (bits[64], bits[64]) {
  let (regs, sp2) = call_enter(low, hi, args)
  let mid = vm.bytes
  let mid_pages = vm.pages
  let (r0, r1) = call_callee(sp2, g, regs)
  return call_leave(sp2, hi, mid, mid_pages, r0, r1)
}

// (the callee on its world, the caller's memory below sp2)
proc[World] call_callee(sp2: Addr, g: CFun2[World], regs: List[bits[64]]) -> (bits[64], bits[64]) {
  let (r0, r1) = with callee_world(sp2) { return g(regs) }
  return (r0, r1)
}

// (the call's way in: the arguments in registers, the callee's stack
// pointer, the caller's frame, the thread pointer and the stack checked)
proc[World] call_enter(low: nat, hi: nat, args: List[(nat, Ty)]) -> (List[bits[64]], Addr) {
  // (a call may overflow the stack: here, the world as it is)
  either { raise stack_overflow } or { }
  let regs = any l: List[bits[64]] where len(l) = len(args) && (all i: nat. i < len(args) -> l[i] in in_reg(args[i][0], args[i][1]))
  let sp2 = any s: Addr where uint(s) <= low && uint(s) % 16 = 0
  let old = vm
  havoc vm where frame_at_call(old, vm, sp2, hi)
  // (the ABI's thread pointer at a call: the word at fs:0 points to itself;
  // the stack sound at the return address's slot)
  if !(thread_ok(vm, fs_base) && stack_ok(vm, sp2 - 8)) { undefined }
  return (regs, sp2)
}

// (... and its way back: the private frame [sp2, hi) as it was before the
// callee (mid, mid_pages))
proc[World] call_leave(sp2: Addr, hi: nat, mid: Addr -> bits[8], mid_pages: PageNo -> Option[Page], r0: bits[64], r1: bits[64]) -> (bits[64], bits[64]) {
  // (the callee may crash after its last I/O -- its spec then returns,
  // with the I/O the crash has)
  either { raise stack_overflow } or { }
  if !(all a: Addr. uint(sp2) <= uint(a) && uint(a) < hi -> vm.bytes[a] = mid[a] && vm.pages[page_of(a)] = mid_pages[page_of(a)]) { undefined }
  return (r0, r1)
}

// (readable GIMPLE) an argument, a call from a function without stack
// objects, and from one with them (the private frame then only below the
// lowest object: the objects' sizes are not passed here)
fn arg[n: nat](x: bits[n]) -> (nat, Ty) = (uint(x), Ty { prec: n, signed: false })
proc[World] call(g: CFun2[World], args: List[(nat, Ty)]) -> (bits[64], bits[64]) { return call_at(uint(sp), uint(sp), g, args) }
proc[World] call_objs(objs: List[Addr], g: CFun2[World], args: List[(nat, Ty)]) -> (bits[64], bits[64]) {
  let low = min({a: nat | a = uint(sp) || (ex j: nat. j < len(objs) && a = uint(objs[j]))})
  return call_at(low, low, g, args)
}

// ... with the value in rax only
proc[World] call1(g: CFun2[World], args: List[(nat, Ty)]) -> bits[64] {
  let (r0, r1) = call(g, args)
  return r0
}
proc[World] call1_objs(objs: List[Addr], g: CFun2[World], args: List[(nat, Ty)]) -> bits[64] {
  let (r0, r1) = call_objs(objs, g, args)
  return r0
}

// (readable GIMPLE) the address of element i (signed) of `size` bytes
proc[World] elem(p: Addr, i: bits[64], size: nat) -> Addr { return padd(p, smul(i, bits[64](size))) }

// (readable GIMPLE) a result in a register: the upper bits are unspecified
proc[World] result[n: nat](v: bits[n]) -> bits[64] {
  return any r: bits[64] where r in in_reg(uint(v), Ty { prec: n, signed: false })
}

// inline assembly: the input registers set (the others arbitrary); the
// registers afterwards
proc[World] inline_asm(code: List[bits[8]], ins: List[(Reg, nat)]) -> Reg -> bits[64] {
  var regs = any (Reg -> bits[64])
  for i in 0..len(ins) { regs := set_reg(regs, ins[i][0], bits[64](ins[i][1])) }
  let out = with asm_machine(regs, any (Reg -> bits[128]), any Flags, any Addr) { return run_code(code) }
  return out
}

///////////////////////////////////////////////////////////////////////
//  Executing a function

proc[World] exec_stmt(fr: Frame, s: Stmt, callees: nat -> CFun2[World]) -> Frame {
  match s {
    assign(x, r) => {
      let v = match r {
        unary(op, ty, a)     => unop(op, ty, operand(fr, a))
        binary(op, ty, a, b) => binop(op, ty, operand(fr, a), operand(fr, b))
        convert(t1, t2, a)   => wrap(t2, sval(t1, operand(fr, a)))
        internal(f, ty, xs)  => ifn(f, ty, [operand(fr, a) for a in xs])
      }
      return fr with { vals: set_val(fr.vals, x, v) }
    }
    load(x, loc, ty) => {
      let a = address(fr, loc, false)
      var v = bytes_at(vm, a, loc.size)
      if loc.bits > 0 { v := wrap(ty, sval(Ty { prec: loc.bits, signed: ty.signed }, v / 2^loc.bitpos % 2^loc.bits)) }
      return fr with { vals: set_val(fr.vals, x, v) }
    }
    store(loc, o) => {
      let a = address(fr, loc, true)
      var v = operand(fr, o)
      if loc.bits > 0 {
        // read-modify-write of the bytes holding the bitfield
        let old = bytes_at(vm, a, loc.size)
        let m   = 2^loc.bitpos * (2^loc.bits - 1)
        v := uint(b128(old) & ~b128(m)) + (v % 2^loc.bits) * 2^loc.bitpos
      }
      write_bytes(a, loc.size, v)
      return fr
    }
    store_bytes(loc, data) => {
      let a = address(fr, loc, true)
      for i in 0..len(data) { vm.bytes[a + bits[64](i)] := data[i] }
      return fr
    }
    call(dsts, k, args) => {
      let low = min({a: nat | a = uint(sp) || (ex j: nat. j < len(fr.objs) && a = uint(fr.objs[j]))})
      let (r0, r1) = call_at(low, low, callees[k], [(operand(fr, args[i][0]), args[i][1]) for i in 0..len(args)])
      let rs = [r0, r1]
      var vals = fr.vals
      for i in 0..len(dsts) { vals := set_val(vals, dsts[i][0], uint(rs[i]) % 2^dsts[i][1].prec) }
      return fr with { vals: vals }
    }
    asm(code, ins, outs) => {
      let out = inline_asm(code, [(ins[i][0], operand(fr, ins[i][1])) for i in 0..len(ins)])
      var vals = fr.vals
      for i in 0..len(outs) { vals := set_val(vals, outs[i][0], uint(out[outs[i][2]]) % 2^outs[i][1].prec) }
      return fr with { vals: vals }
    }
  }
}

// enter block b (from the current block): all phis read the values before
// any is set; a missing argument is a malformed program (undefined)
proc[World] enter(fr: Frame, blocks: List[Block], b: nat) -> Frame {
  var vals = fr.vals
  let phis = blocks[b].phis
  for i in 0..len(phis) {
    let o = any o: Opnd where ex j: nat. j < len(phis[i].args) && phis[i].args[j] = (fr.bb, o)
    vals := set_val(vals, phis[i].dst, operand(fr, o))
  }
  return fr with { vals: vals, bb: b, prev: fr.bb }
}

// A GIMPLE function as a C function spec, given the specs of the
// functions it calls (by number).
proc[World] run_fun(f: Function, callees: nat -> CFun2[World], args: Args) -> (bits[64], bits[64]) {
  var vals = any (Name -> nat)                  // uninitialized names: arbitrary
  for i in 0..len(f.params) {
    let (x, ty) = f.params[i]
    vals := set_val(vals, x, uint(args[i]) % 2^ty.prec)
  }
  var fr = Frame { vals: vals, objs: alloc_objs(f.objs), bb: f.entry, prev: f.entry }
  while true {
    let blk = f.blocks[fr.bb]
    for i in 0..len(blk.body) { fr := exec_stmt(fr, blk.body[i], callees) }
    match blk.jump {
      goto(b) => fr := enter(fr, f.blocks, b)
      branch(op, ty, a, c, yes, no) => {
        let t = binop(op, ty, operand(fr, a), operand(fr, c))
        fr := enter(fr, f.blocks, if t = 1 { yes } else { no })
      }
      ret(vs) => {
        // unused result registers, and bits above a result's precision, are arbitrary
        var rs: List[bits[64]] = [any bits[64], any bits[64]]
        for i in 0..len(vs) { rs := rs[0..i] ++ [any r: bits[64] where r in in_reg(operand(fr, vs[i][0]), vs[i][1])] ++ rs[i+1..] }
        return (rs[0], rs[1])
      }
    }
  }
}

fn gimple_fun(f: Function, callees: nat -> CFun2[World]) -> CFun2[World] =
  (args: Args) => run_fun(f, callees, args)

///////////////////////////////////////////////////////////////////////
//  Relating a running function to the machine (for proofs)

// Where compiled code keeps a value at a program point.
type Home = in_reg(r: Reg)        // in a register (the value in its low bits)
          | in_slot(off: int)     // in the stack slot at entry sp + off (8 bytes)
          | known(v: nat)         // not kept: the code has the constant built in
          | dead                  // not needed any more

// A program point of the compiled function: the machine address where
// GIMPLE block `bb` begins (after its phis), the stack pointer relative to
// the stack pointer at entry, the homes of names, the offsets of the stack
// objects, and where the caller's callee-saved registers are.
record Point {
  addr   : Addr
  bb     : nat
  rsp_at : int
  homes  : Name -> Home
  objs   : List[int]
  saved  : Reg -> Home
}

pred holds(m: Machine, sp: Addr, h: Home, v: nat, ty: Ty) = match h {
  in_reg(r)   => uint(m.gpr[r]) % 2^ty.prec = v % 2^ty.prec
  in_slot(o)  => bytes_at(m.vm, bits[64](uint(sp) + o), 8) % 2^ty.prec = v % 2^ty.prec
  known(c)    => c % 2^ty.prec = v % 2^ty.prec
  dead        => true
}

// The machine `m` is at point `pt` of the compiled function, called with
// stack pointer `sp` (the return address `ret` is at sp - 8) by a caller
// whose callee-saved registers were `entry`, and the running GIMPLE function is in
// frame `fr` with world `w`:
// - memory, OS state and thread pointer agree, except for the machine's
//   scratch contents that are not GIMPLE stack objects (spills, saved
//   registers, the frames of callees) and stack pages only it has;
// - each name's value is in its home, each stack object where the frame says;
// - the caller's callee-saved registers can be restored.
pred coupled(f: Function, pt: Point, sp: Addr, ret: Addr, entry: Reg -> bits[64], fr: Frame, w: World, m: Machine) =
  m.rip = pt.addr && fr.bb = pt.bb &&
  uint(m.gpr[rsp]) = uint(sp) + pt.rsp_at &&
  m.os = w.os && m.fs_base = w.fs_base && m.cpu = w.cpu && w.sp = sp &&
  (all p: PageNo. m.vm.pages[p] = w.vm.pages[p] ||             // the machine's stack may be
     (scratch_page(w.vm, sp, p) && w.vm.pages[p] = none && stack_page(m.vm, p))) &&   // deeper (spills)
  (all a: Addr. (!scratch(w.vm, sp, uint(a)) || (ex k: nat. k < len(fr.objs) &&
       uint(fr.objs[k]) <= uint(a) && uint(a) < uint(fr.objs[k]) + f.objs[k][0])) ->
     m.vm.bytes[a] = w.vm.bytes[a]) &&
  (all k: nat. k < len(fr.objs) -> uint(fr.objs[k]) = uint(sp) + pt.objs[k]) &&
  (all x: Name. holds(m, sp, pt.homes[x], fr.vals[x], f.types[x])) &&
  (all r: Reg. r in CALLEE_SAVED -> holds(m, sp, pt.saved[r], uint(entry[r]), Ty { prec: 64, signed: false })) &&
  bytes_at(m.vm, sp - 8, 8) = uint(ret)
