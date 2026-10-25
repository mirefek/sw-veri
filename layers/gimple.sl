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
// GIMPLE (it refines e.g. `malloc_fun()`) carries over to the machine code
// (proven function by function by the bridge, proofs/translate*.core).
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

// The memory a GIMPLE access may use: the world's (its domain: the C
// world's bytes on its mapped pages, as their protection allows -- C objects are
// never write-only --, and elsewhere the stack objects, not wrapping
// around the address space; the world has no stack pages, so the test for
// them is vacuous). Anything else
// is undefined (GCC may remove, reorder or speculate accesses that are
// valid in C): also the stack outside the stack objects, where the machine
// keeps what C does not see -- reached only by a dangling pointer.
pred usable(vm: Vm, objs: Objs, a: nat, n: nat, w: bool) =
  all i: nat. i < n ->
    if mapped(vm, (a + i) / PAGE) && vm.pages[(a + i) / PAGE].value.kind != stack {
      (if w { vm.pages[(a + i) / PAGE].value.prot.w } else { vm.pages[(a + i) / PAGE].value.prot.r }) && a + i in objs.c_bytes
    } else { a + i < 2^64 && a + i in objs.live }

// A valid page: mapped, all its bytes the C world's (as the pages the
// kernel gives are; a page the ABI keeps a byte of is not).
pred page_valid(vm: Vm, objs: Objs, p: nat) = mapped(vm, p) && (all i: nat. i < PAGE -> p * PAGE + i in objs.c_bytes)

// An access through a null base pointer is undefined, whatever is mapped at
// page 0: no C object is there, and GCC relies on it (a dereferenced pointer
// is non-null: `-fdelete-null-pointer-checks` removes later null tests). The
// Linux model never maps page 0 on its own (spec/linux/process.sl), so
// programs can show they avoid this.
proc[World] address(fr: Frame, loc: Loc, w: bool) -> Addr {
  if operand(fr, loc.base) = 0 { undefined }
  let a = binop(ptr_add, Ty { prec: 64, signed: false }, operand(fr, loc.base), uint(loc.off))
  if a % loc.align != 0 || !usable(vm, objs, a, loc.size, w) { undefined }
  return bits[64](a)
}

// the n bytes at a as a number (little-endian)
fn bytes_at(vm: Vm, a: Addr, n: nat) -> nat = sum i in 0..n. uint(vm.bytes[a + bits[64](i)]) * 256^i

proc[World] write_bytes(a: Addr, n: nat, v: nat) {
  for i in 0..n { vm.bytes[a + bits[64](i)] := bits[8](v / 256^i) }
}

// Stack objects (address-taken locals) are placed on the stack (anywhere
// GCC's frame layout may put them: the stack's free bytes, on none of the
// world's pages), disjoint and aligned, not null and within the address
// space (as C's objects) -- no such place, a stack overflow; their
// contents are arbitrary. They join the world's domain
// (`objs.live`) for the rest of the function: its `_fun` wrapper drops them
// at the return.
pred objs_fit(vm: Vm, objs: Objs, sizes: List[(nat, nat)], l: List[Addr]) =
  len(l) = len(sizes) &&
  (all k: nat. k < len(sizes) ->
     uint(l[k]) % sizes[k][1] = 0 && l[k] != 0 && uint(l[k]) + sizes[k][0] <= 2^64 &&
     (all a: nat. uint(l[k]) <= a && a < uint(l[k]) + sizes[k][0] -> stack_free(vm, objs, a))) &&
  (all j: nat, k: nat. j < k && k < len(sizes) ->
     uint(l[j]) + sizes[j][0] <= uint(l[k]) || uint(l[k]) + sizes[k][0] <= uint(l[j]))

proc[World] alloc_objs(sizes: List[(nat, nat)]) -> List[Addr] {
  // (no room for them: the stack overflows)
  if !(ex l: List[Addr]. objs_fit(vm, objs, sizes, l)) { raise stack_overflow }
  let addrs = any l: List[Addr] where objs_fit(vm, objs, sizes, l)
  // (their bytes any: the memory but for them as it was)
  let before = vm
  havoc vm where (vm with { bytes: before.bytes }) = before &&
    (all a: Addr. (all k: nat. k < len(sizes) -> !(uint(addrs[k]) <= uint(a) && uint(a) < uint(addrs[k]) + sizes[k][0])) -> vm.bytes[a] = before.bytes[a])
  objs := objs with { live: {a: nat | a in objs.live || ex k: nat. k < len(sizes) && uint(addrs[k]) <= a && a < uint(addrs[k]) + sizes[k][0]} }
  return addrs
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
proc[World] mem(p: Addr, off: bits[64], size: nat, w: bool) -> Addr {
  if p = 0 { undefined }
  let a = padd(p, off)
  if !usable(vm, objs, uint(a), size, w) { undefined }
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

// Atomic primitives: inline assembly GCC keeps opaque (`asm volatile`
// with a "memory" clobber: emitted verbatim, no access moved across it),
// given its meaning at this level -- one step (atomic: the world has one
// thread so far); C1 shows the instruction implements it, wherever it is
// (an out-of-line function or inlined).
//
// lock cmpxchg [p], s (rax t): compare-and-swap of the 32-bit word at p --
// s written if it holds t; its old value returned. The word is read and
// written either way (a locked read-modify-write: the old value written
// back).
proc[World] cas32(p: Addr, t: bits[32], s: bits[32]) -> bits[32] {
  let old = ld32(p, 0)
  st32(p, 0, if old = t { s } else { old })
  return old
}

// A system call (`syscall`: rax n, rdi a1, rsi a2, rdx a3, r10 a4, r8 a5,
// r9 a6; its result in rax, rcx and r11 clobbered): Linux's call
// (spec/linux/process.sl) as the C world sees it -- on the world's memory,
// the machine's but its stack pages (a page free in the machine is free
// there: the world's call allows the machine's). Only the calls the
// allocator makes -- brk, mmap, mprotect -- and only where the pages they
// change are its kind of memory: off the stack's space (the world does not
// see the stack's pages: its frames, its room to grow), not the
// program's code (executable), and valid -- whole pages of the world's
// (`page_valid`: none the ABI keeps a byte of). A call reaching other
// pages is undefined, as is any other call.
pred sys_pages_ok(vm: Vm, objs: Objs, p: nat, n: nat) =
  off_stack_space(vm, p, n) && (all q: nat. p <= q && q < p + n -> mapped(vm, q) -> !vm.pages[q].value.prot.x) &&
  (all q: nat. p <= q && q < p + n -> mapped(vm, q) -> page_valid(vm, objs, q))

// The memory's changes by a call. vm: before with the pages p .. p+n-1
// fresh pages pg -- their bytes 0; the C world's (none of them has a
// byte the ABI keeps: the kernel maps no page that is mapped, the ABI's
// are), so valid pages --, nothing else changed (its break aside)
pred fresh_pages(before: Vm, vm: Vm, objs: Objs, p: nat, n: nat, pg: Page) =
  (all a: nat. p * PAGE <= a && a < (p + n) * PAGE -> a in objs.c_bytes) &&
  vm.stack_top = before.stack_top && vm.stack_limit = before.stack_limit && vm.brk_start = before.brk_start &&
  (all q: nat. q < TASK_SIZE / PAGE -> vm.pages[q] = (if p <= q && q < p + n { some(pg) } else { before.pages[q] })) &&
  (all a: Addr. vm.bytes[a] = (if p * PAGE <= uint(a) && uint(a) < (p + n) * PAGE { bits[8](0) } else { before.bytes[a] }))

// vm: before with the pages p .. p+n-1 gone, nothing else changed (its break aside)
pred gone_pages(before: Vm, vm: Vm, p: nat, n: nat) =
  vm.stack_top = before.stack_top && vm.stack_limit = before.stack_limit && vm.brk_start = before.brk_start &&
  (all q: nat. q < TASK_SIZE / PAGE -> vm.pages[q] = (if p <= q && q < p + n { none } else { before.pages[q] })) &&
  vm.bytes = before.bytes

// vm: before with the pages p .. p+n-1 (mapped) of protection pr, nothing else changed
pred reprot(before: Vm, vm: Vm, p: nat, n: nat, pr: Prot) =
  (vm with { pages: before.pages }) = before &&
  (all q: nat. q < TASK_SIZE / PAGE -> vm.pages[q] = (if p <= q && q < p + n { some(before.pages[q].value with { prot: pr }) } else { before.pages[q] }))

// Linux's calls (spec/linux/process.sl's sys_brk, sys_mmap, sys_mprotect),
// their effect on the memory stated (C1's `syscall` rule shows the
// machine's run of each, seen through the world, one of these).
//
// brk(new): the memory vm after it, from before -- unchanged, below the
// break's start or refused growing (the pages not free, off the stack's
// space; or the kernel's choice); grown to new by fresh heap pages; or
// shrunk to new, the pages above gone. The break returned (the old one
// unchanged, else new).
pred brk_post(before: Vm, vm: Vm, objs: Objs, new: Addr) =
  (vm = before && (new < before.brk_start || pages_for(uint(new)) > pages_for(uint(before.brk)))) ||
  (new >= before.brk_start && pages_for(uint(new)) > pages_for(uint(before.brk)) &&
   free_range(before, pages_for(uint(before.brk)), pages_for(uint(new)) - pages_for(uint(before.brk))) &&
   off_stack_space(before, pages_for(uint(before.brk)), pages_for(uint(new)) - pages_for(uint(before.brk))) &&
   fresh_pages(before, vm, objs, pages_for(uint(before.brk)), pages_for(uint(new)) - pages_for(uint(before.brk)),
     Page { prot: Prot { r: true, w: true, x: false }, kind: heap }) && vm.brk = new) ||
  (new >= before.brk_start && pages_for(uint(new)) <= pages_for(uint(before.brk)) &&
   gone_pages(before, vm, pages_for(uint(new)), pages_for(uint(before.brk)) - pages_for(uint(new))) && vm.brk = new)

proc[World] os_brk(new: Addr) -> bits[64] {
  let before = vm
  havoc vm where brk_post(before, vm, objs, new)
  return vm.brk
}

// mmap (anonymous private memory only)
proc[World] os_mmap(addr: Addr, len: bits[64], prot: bits[64], flags: bits[64], fd: bits[64], off: bits[64]) -> bits[64] {
  require uint(flags) = MAP_PRIVATE + MAP_ANONYMOUS || uint(flags) = MAP_PRIVATE + MAP_ANONYMOUS + MAP_FIXED
  require uint(prot) < 8
  if uint(off) % PAGE != 0 { return err(EINVAL) }
  if len = 0 { return err(EINVAL) }
  let n = pages_for(uint(len))
  either { return err(ENOMEM) } or {}
  let before = vm
  if flags[4] {
    if uint(addr) % PAGE != 0 { return err(EINVAL) }
    let p = page_of(addr)
    if p + n > TASK_SIZE / PAGE { return err(ENOMEM) }
    havoc vm where fresh_pages(before, vm, objs, p, n, Page { prot: prot_of(prot), kind: anon }) && vm.brk = before.brk else { return err(ENOMEM) }
    return bits[64](p * PAGE)
  } else {
    // (no free place: ENOMEM, as Linux's get_unmapped_area; the havocs'
    // else -- no memory with fresh pages, never so for a world's memory --
    // ENOMEM too, so the call is defined for every state)
    let p = any nat where p >= 1 && free_range(before, p, n) && (addr != 0 || off_stack_space(before, p, n)) else { return err(ENOMEM) }
    havoc vm where fresh_pages(before, vm, objs, p, n, Page { prot: prot_of(prot), kind: anon }) && vm.brk = before.brk else { return err(ENOMEM) }
    return bits[64](p * PAGE)
  }
}

// mprotect: the pages up to the first unmapped one (k) changed; ENOMEM if
// there is one in the range
pred mprot_post(before: Vm, vm: Vm, addr: Addr, len: bits[64], prot: bits[64]) =
  ex k: nat. page_of(addr) <= k && k <= page_of(addr) + pages_for(uint(len)) &&
    (all q: nat. page_of(addr) <= q && q < k -> mapped(before, q)) &&
    (k < page_of(addr) + pages_for(uint(len)) -> !mapped(before, k)) &&
    reprot(before, vm, page_of(addr), k - page_of(addr), prot_of(prot))

fn mprot_ret(before: Vm, addr: Addr, len: bits[64]) -> bits[64] =
  if all q: nat. page_of(addr) <= q && q < page_of(addr) + pages_for(uint(len)) -> mapped(before, q) { 0 } else { err(ENOMEM) }

proc[World] os_mprotect(addr: Addr, len: bits[64], prot: bits[64]) -> bits[64] {
  if uint(addr) % PAGE != 0 { return err(EINVAL) }
  require uint(prot) < 8
  let before = vm
  havoc vm where mprot_post(before, vm, addr, len, prot)
  return mprot_ret(before, addr, len)
}

// munmap: the pages from addr's for len gone (EINVAL: addr not a page's
// start, len 0, or the pages beyond the task's)
proc[World] os_munmap(addr: Addr, len: bits[64]) -> bits[64] {
  if uint(addr) % PAGE != 0 || len = 0 { return err(EINVAL) }
  if page_of(addr) + pages_for(uint(len)) > TASK_SIZE / PAGE { return err(EINVAL) }
  let before = vm
  havoc vm where gone_pages(before, vm, page_of(addr), pages_for(uint(len))) && vm.brk = before.brk
  return 0
}

// The calls by the arguments passed (the registers not passed no
// argument of the call made, which reads only its own): with one, brk
// (12); with two, munmap (11); with three, mprotect (10); with six, mmap
// (9).
proc[World] sys_call1(n: bits[64], a1: bits[64]) -> bits[64] {
  require uint(n) = 12
  // the pages it gives back, the break's own (it takes new ones only where
  // they are free, off the stack's space)
  require pages_for(uint(a1)) < pages_for(uint(vm.brk)) -> a1 >= vm.brk_start ->
    pages_for(uint(vm.brk)) <= TASK_SIZE / PAGE &&
    sys_pages_ok(vm, objs, pages_for(uint(a1)), pages_for(uint(vm.brk)) - pages_for(uint(a1))) &&
    (all q: nat. pages_for(uint(a1)) <= q && q < pages_for(uint(vm.brk)) -> mapped(vm, q) -> vm.pages[q].value.kind = heap)
  return os_brk(a1)
}

proc[World] sys_call2(n: bits[64], a1: bits[64], a2: bits[64]) -> bits[64] {
  require uint(n) = 11
  // its pages
  require sys_pages_ok(vm, objs, page_of(a1), pages_for(uint(a2)))
  return os_munmap(a1, a2)
}

proc[World] sys_call3(n: bits[64], a1: bits[64], a2: bits[64], a3: bits[64]) -> bits[64] {
  require uint(n) = 10
  // its pages
  require sys_pages_ok(vm, objs, page_of(a1), pages_for(uint(a2)))
  return os_mprotect(a1, a2, a3)
}

proc[World] sys_call6(n: bits[64], a1: bits[64], a2: bits[64], a3: bits[64], a4: bits[64], a5: bits[64], a6: bits[64]) -> bits[64] {
  require uint(n) = 9
  // a fixed mapping's pages; else no hint (Linux then places it on free
  // pages off the stack's space)
  require if a4[4] { sys_pages_ok(vm, objs, page_of(a1), pages_for(uint(a2))) } else { uint(a1) = 0 }
  return os_mmap(a1, a2, a3, a4, a5, a6)
}

// the thread pointer (`mov %fs:0, r`, musl's __get_tp): the ABI's, in a
// sound thread (`thread_ok`: the word at fs:0 the thread descriptor's own
// address) -- the machine's load of that word is the bridge's
proc[World] thread_ptr() -> Addr {
  if !thread_ok(vm, fs_base) { undefined }
  return fs_base
}

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

// Calling g: the arguments (values with their types) in registers, the
// result registers rax, rdx. The callee runs on the caller's world (with
// its stack objects, which it may reach; the caller's frame is not in the
// world, nor is the rest of the stack: the machine's business, the ABI
// bridge's). A call with the thread pointer broken (the word at fs:0 not
// pointing to itself, as the ABI requires at every call) is undefined.
// The thread pointer is the thread's: back as it was after the call (the
// ABI's `world`).
// Every call may overflow the stack (`stack_overflow`, the ABI's: no
// undefined behavior), before the callee runs and after it returns.
proc[World] call(g: CFun2[World], args: List[(nat, Ty)]) -> (bits[64], bits[64]) {
  either { raise stack_overflow } or { }
  let (r0, r1) = call_callee(g, args)
  // (the callee may crash after its last I/O -- its spec then returns,
  // with the I/O the crash has)
  either { raise stack_overflow } or { }
  return (r0, r1)
}

// (the callee's part of a call)
proc[World] call_callee(g: CFun2[World], args: List[(nat, Ty)]) -> (bits[64], bits[64]) {
  let regs = any l: List[bits[64]] where len(l) = len(args) && (all i: nat. i < len(args) -> l[i] in in_reg(args[i][0], args[i][1]))
  if !thread_ok(vm, fs_base) { undefined }
  let live0 = objs.live
  let fs0 = fs_base
  let (r0, r1) = g(regs)
  objs := objs with { live: live0 }      // (the callee's stack objects are gone)
  fs_base := fs0
  return (r0, r1)
}

// (readable GIMPLE) an argument; a call from a function with stack objects
// (the same: the objects are in the world)
fn arg[n: nat](x: bits[n]) -> (nat, Ty) = (uint(x), Ty { prec: n, signed: false })
proc[World] call_objs(objs: List[Addr], g: CFun2[World], args: List[(nat, Ty)]) -> (bits[64], bits[64]) { return call(g, args) }

// (a callee of more than six arguments, the rest on the stack: the same --
// the stack is the ABI bridge's)
proc[World] call_s(g: CFunS[World], args: List[(nat, Ty)]) -> (bits[64], bits[64]) {
  either { raise stack_overflow } or { }
  let (r0, r1) = call_callee_s(g, args)
  either { raise stack_overflow } or { }
  return (r0, r1)
}
proc[World] call_callee_s(g: CFunS[World], args: List[(nat, Ty)]) -> (bits[64], bits[64]) {
  let regs = any l: List[bits[64]] where len(l) = len(args) && (all i: nat. i < len(args) -> l[i] in in_reg(args[i][0], args[i][1]))
  if !thread_ok(vm, fs_base) { undefined }
  let live0 = objs.live
  let fs0 = fs_base
  let (r0, r1) = g(regs)
  objs := objs with { live: live0 }
  fs_base := fs0
  return (r0, r1)
}
proc[World] call1_s(g: CFunS[World], args: List[(nat, Ty)]) -> bits[64] {
  let (r0, r1) = call_s(g, args)
  return r0
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
      let (r0, r1) = call(callees[k], [(operand(fr, args[i][0]), args[i][1]) for i in 0..len(args)])
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
