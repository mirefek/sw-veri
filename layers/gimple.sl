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
// crash case).
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
//  Calls and inline assembly

// A called function sees the world with its own stack pointer (below the
// caller's stack objects); afterwards the stack below it is arbitrary.
view[World] callee_world(sp2: Addr) : World {
  get = World { vm: clean(vm, sp2), os, fs_base, cpu, sp: sp2 }
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
      var regs: List[bits[64]] = []
      for i in 0..len(args) { regs := regs ++ [any r: bits[64] where r in in_reg(operand(fr, args[i][0]), args[i][1])] }
      let low  = min({a: nat | a = uint(sp) || (ex j: nat. j < len(fr.objs) && a = uint(fr.objs[j]))})
      let sp2  = any s: Addr where uint(s) <= low && uint(s) % 16 = 0
      let g    = callees[k]
      let (r0, r1) = with callee_world(sp2) { return g(regs) }
      let rs = [r0, r1]
      var vals = fr.vals
      for i in 0..len(dsts) { vals := set_val(vals, dsts[i][0], uint(rs[i]) % 2^dsts[i][1].prec) }
      return fr with { vals: vals }
    }
    asm(code, ins, outs) => {
      var regs = any (Reg -> bits[64])
      for i in 0..len(ins) { regs := set_reg(regs, ins[i][0], bits[64](operand(fr, ins[i][1]))) }
      let out = with asm_machine(regs, any (Reg -> bits[128]), any Flags, any Addr) { return run_code(code) }
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
  (all a: nat. (!scratch(w.vm, sp, a) || (ex k: nat. k < len(fr.objs) &&
       uint(fr.objs[k]) <= a && a < uint(fr.objs[k]) + f.objs[k][0])) ->
     m.vm.bytes[bits[64](a)] = w.vm.bytes[bits[64](a)]) &&
  (all k: nat. k < len(fr.objs) -> uint(fr.objs[k]) = uint(sp) + pt.objs[k]) &&
  (all x: Name. holds(m, sp, pt.homes[x], fr.vals[x], f.types[x])) &&
  (all r: Reg. r in CALLEE_SAVED -> holds(m, sp, pt.saved[r], uint(entry[r]), Ty { prec: 64, signed: false })) &&
  bytes_at(m.vm, sp - 8, 8) = uint(ret)
