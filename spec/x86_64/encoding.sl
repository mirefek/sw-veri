spec x86_64_linux

// Instruction decoding for x86_64, fully specified in SL.
//
//   1. decoding context: prefixes, REX, and which of them a row used
//   2. decoders: prefixes, ModRM/SIB, immediates, opcode-embedded fields
//   3. notations: the Intel-manual shorthand, defined via the decoders
//   4. the instruction table
//   5. fetch & execute
//
// The language knows only generic decoders, tables and notations
// (docs/language.md, section 8); everything x86-specific is here.

///////////////////////////////////////////////////////////////////////
//  1. Decoding context

// REX prefix 0100WRXB: W = 64-bit operand size, R/X/B = 4th bit of the
// ModRM reg field / SIB index / ModRM rm, SIB base or opcode register.
record Rex { present, w, r, x, b : bool }

// which prefix information the matched row relied on
record Used { opsize, rep, lock, seg, w, r, x, b : bool }

record Ctx {
  opsize : bool         // 66 seen
  rep    : bool         // F3 seen
  lock   : bool         // F0 seen
  seg    : Seg          // 2E / 64 / 65 seen
  rex    : Rex          // all false without REX
  osz    : Size         // operand size in bytes, set by opsize()
  used   : Used
}

const NO_REX = Rex  { present: false, w: false, r: false, x: false, b: false }
const NO_USE = Used { opsize: false, rep: false, lock: false, seg: false, w: false, r: false, x: false, b: false }
const START  = Ctx  { opsize: false, rep: false, lock: false, seg: flat, rex: NO_REX, osz: 4, used: NO_USE }

decoder context Ctx

///////////////////////////////////////////////////////////////////////
//  2. Decoders

// Legacy prefixes in any order (repeats allowed, as in gcc's padding
// `66 66 2E 0F 1F 84 ...`), then an optional REX byte, which must be the
// last byte before the opcode.
decoder prefixes() {
  loop {
    match peek() {
      0x66 => { next(); ctx.opsize := true }
      0xF3 => { next(); ctx.rep := true }
      0xF0 => { next(); ctx.lock := true }
      0x2E => { next(); ctx.seg := cs }
      0x64 => { next(); ctx.seg := fs }
      0x65 => { next(); ctx.seg := gs }
      _    => break
    }
  }
  let b = peek()
  if b[7:4] = 0x4 {
    next()
    ctx.rex := Rex { present: true, w: b[3], r: b[2], x: b[1], b: b[0] }
  }
}

// Prefixes or REX bits the row did not use: not modelled (the CPU mostly
// ignores them), so the row does not match and the step is `undefined`.
decoder finish() {
  guard !ctx.opsize    || ctx.used.opsize
  guard !ctx.rep       || ctx.used.rep
  guard !ctx.lock      || ctx.used.lock
  guard ctx.seg = flat || ctx.used.seg
  guard !ctx.rex.w     || ctx.used.w
  guard !ctx.rex.r     || ctx.used.r
  guard !ctx.rex.x     || ctx.used.x
  guard !ctx.rex.b     || ctx.used.b
}

// operand size in bytes: REX.W → 8, else 66 → 2, else 4
decoder opsize() -> Size {
  ctx.used.opsize := true
  ctx.used.w      := true
  ctx.osz := if ctx.rex.w { 8 } else if ctx.opsize { 2 } else { 4 }
  return ctx.osz
}

decoder rex_w() { guard ctx.rex.w; ctx.used.w := true }
decoder rep()   { guard ctx.rep;   ctx.used.rep := true }

// `lock`: the instruction is atomic. With a single thread this changes
// nothing; the prefix is only accepted where the manual allows it.
decoder lock()  { guard ctx.lock;  ctx.used.lock := true }

// a mandatory 66 prefix (SSE): selects the instruction, not the operand size
decoder pfx66() { guard ctx.opsize; ctx.used.opsize := true }

// n-byte little-endian immediate
decoder imm(n: nat) -> bits[8*n] {
  var v: bits[8*n] = 0
  for i in 0..n { v[8*i+7 : 8*i] := next() }
  return v
}

// 16-bit immediate for 16-bit operands, 32-bit otherwise (also for 64-bit),
// zero-extended to 32 bits (so `sext[8*n](iz)` is right for every n)
fn zsize(n: Size) -> nat = if n = 2 { 2 } else { 4 }
decoder imm_z() -> bits[32] {
  guard ctx.used.opsize                    // needs opsize() first
  return zext[32](imm(zsize(ctx.osz)))
}

fn xreg(ext: bool, lo: bits[3]) -> Reg = Reg(uint(lo) + if ext { 8 } else { 0 })

// opcode byte base..base+7, the low 3 bits (+ REX.B) name a register
decoder plus_reg(base: bits[8]) -> Reg {
  let b = next()
  guard b[7:3] = base[7:3]
  ctx.used.b := true
  return xreg(ctx.rex.b, b[2:0])
}

// opcode byte base..base+15, the low 4 bits are a condition code
decoder plus_cc(base: bits[8]) -> bits[4] {
  let b = next()
  guard b[7:4] = base[7:4]
  return b[3:0]
}

// ModRM byte: mod (2 bits) | reg (3 bits) | rm (3 bits).
// Returns the raw reg field and the operand described by mod/rm
// (with SIB byte and displacement).
decoder modrm() -> (bits[3], Operand) {
  let m   = next()
  let mod = m[7:6]
  let reg = m[5:3]
  let rm  = m[2:0]
  if mod = 3 {                                         // register
    ctx.used.b := true
    return (reg, gp(xreg(ctx.rex.b, rm)))
  }
  ctx.used.seg := true
  if rm = 4 { return (reg, ref(sib(mod))) }
  if mod = 0 && rm = 5 {                               // RIP-relative
    return (reg, ref(MemOp { seg: ctx.seg, base: rip_rel, index: none, scale: 1,
                             disp: sext[64](imm(4)) }))
  }
  ctx.used.b := true
  return (reg, ref(MemOp { seg: ctx.seg, base: base(xreg(ctx.rex.b, rm)), index: none,
                           scale: 1, disp: disp(mod) }))
}

// SIB byte: scale (2 bits) | index (3 bits) | base (3 bits)
decoder sib(mod: bits[2]) -> MemOp {
  let s  = next()
  let ix = s[5:3]
  let bs = s[2:0]
  ctx.used.x := true
  let index = if ix = 4 && !ctx.rex.x { none } else { some(xreg(ctx.rex.x, ix)) }
  let scale = 2^uint(s[7:6])
  if bs = 5 && mod = 0 {                               // no base, disp32
    return MemOp { seg: ctx.seg, base: nobase, index, scale, disp: sext[64](imm(4)) }
  }
  ctx.used.b := true
  return MemOp { seg: ctx.seg, base: base(xreg(ctx.rex.b, bs)), index, scale, disp: disp(mod) }
}

decoder disp(mod: bits[2]) -> bits[64] {
  match mod {
    0 => return 0
    1 => return sext[64](imm(1))
    _ => return sext[64](imm(4))
  }
}

// byte operands: register numbers 4..7 mean ah..bh without REX,
// spl..dil with any REX (even 0x40)
fn byte_operand(rex: Rex, o: Operand) -> Operand = match o {
  gp(r) => if !rex.present && uint(r) in 4..8 { hi8(Reg(uint(r) - 4)) } else { o }
  _     => o
}

// ModRM whose reg field names a register (extended by REX.R)
decoder modrm_r() -> (Reg, Operand, Operand, Operand) {
  let (reg, rm) = modrm()
  ctx.used.r := true
  let r = xreg(ctx.rex.r, reg)
  return (r, rm, byte_operand(ctx.rex, rm), byte_operand(ctx.rex, gp(r)))
}

// ModRM whose reg field is a fixed opcode extension
decoder modrm_ext(d: bits[3]) -> (Operand, Operand) {
  let (reg, rm) = modrm()
  guard reg = d
  return (rm, byte_operand(ctx.rex, rm))
}

// ModRM whose reg field selects an operation of enum E
decoder modrm_enum[E: enum bits[3]]() -> (E, Operand, Operand) {
  let (reg, rm) = modrm()
  guard reg in E
  return (E(reg), rm, byte_operand(ctx.rex, rm))
}

///////////////////////////////////////////////////////////////////////
//  3. Notations: Intel SDM opcode-table shorthand
//
//  Each notation is a pattern of tokens with typed holes, expanding to
//  table items. Names bound in the expansion are visible in the row.

notations intel {
  ib                        ~> ib = imm(1)                     // 1-byte immediate
  iw                        ~> iw = imm(2)                     // 2-byte immediate
  id                        ~> id = imm(4)                     // 4-byte immediate
  io                        ~> io = imm(8)                     // 8-byte immediate
  iz                        ~> iz = imm_z()                    // 2 or 4 bytes by operand size
  cb                        ~> cb = imm(1)                     // 1-byte relative offset
  cd                        ~> cd = imm(4)                     // 4-byte relative offset
  /r                        ~> (r, rm, rm8, reg8) = modrm_r()
  /(d: nat)                 ~> (rm, rm8) = modrm_ext(d)
  /(x: ident):(E: type)     ~> (x, rm, rm8) = modrm_enum[E]()
  (b: byte)+r               ~> r = plus_reg(b)
  (b: byte)+cc              ~> cc = plus_cc(b)
  REX.W                     ~> rex_w()
  REP                       ~> rep()
  LOCK                      ~> lock()
  P66                       ~> pfx66()
}

///////////////////////////////////////////////////////////////////////
//  4. The instruction table
//
//  A row matches if `prefixes()`, its items, and `finish()` all succeed.
//  Its statement runs with `rip` already pointing to the next instruction.

table x86 using intel {
  context START
  before  prefixes()
  after   finish()

  // ---- byte operations
  for op in AluOp {
    {8*uint(op) + 0x00} /r               => alu(op, rm8, at(reg8, 1))
    {8*uint(op) + 0x02} /r               => alu(op, reg8, at(rm8, 1))
    {8*uint(op) + 0x04} ib               => alu(op, gp(rax), ib)          // al
  }
  0x80 /op:AluOp ib                      => alu(op, rm8, ib)
  0x84 /r                                => test(at(rm8, 1), at(reg8, 1))
  0xA8 ib                                => test(reg(rax, 1), ib)
  0xF6 /0 ib                             => test(at(rm8, 1), ib)
  0x88 /r                                => at(rm8, 1) := at(reg8, 1)
  0x8A /r                                => at(reg8, 1) := at(rm8, 1)
  0xC6 /0 ib                             => at(rm8, 1) := ib
  0x0F 0x90+cc /0                        => at(rm8, 1) := if cond(flags, cc) { 1 } else { 0 }  // setcc
  0xC0 /op:ShiftOp ib                    => shift(op, 1, rm8, ib)
  0xD0 /op:ShiftOp                       => shift(op, 1, rm8, 1)
  0xD2 /op:ShiftOp                       => shift(op, 1, rm8, reg(rcx, 1))

  // ---- operations of operand size n = 2 / 4 / 8 bytes
  with n = opsize() {
    for op in AluOp {
      {8*uint(op) + 0x01} /r             => alu(op, rm, reg(r, n))
      {8*uint(op) + 0x03} /r             => alu(op, gp(r), at(rm, n))
      {8*uint(op) + 0x05} iz             => alu(op, gp(rax), sext[8*n](iz))
    }
    0x81 /op:AluOp iz                    => alu(op, rm, sext[8*n](iz))
    0x83 /op:AluOp ib                    => alu(op, rm, sext[8*n](ib))

    0x85 /r                              => test(at(rm, n), reg(r, n))
    0xA9 iz                              => test(reg(rax, n), sext[8*n](iz))
    0xF7 /0 iz                           => test(at(rm, n), sext[8*n](iz))

    0xF7 /op:UnOp                        => unary(op, n, rm)
    0xFF /0                              => incdec(false, n, rm)
    0xFF /1                              => incdec(true, n, rm)
    0xF7 /4                              => mul(n, at(rm, n))
    0xF7 /6                              => div(n, at(rm, n))
    0xF7 /7                              => idiv(n, at(rm, n))
    0x0F 0xAF /r                         => imul2(n, r, at(rm, n))
    0x99                                 => sign_fill(n)                  // cwd / cdq / cqo

    0xC1 /op:ShiftOp ib                  => shift(op, n, rm, ib)
    0xD1 /op:ShiftOp                     => shift(op, n, rm, 1)
    0xD3 /op:ShiftOp                     => shift(op, n, rm, reg(rcx, 1))

    0x89 /r                              => at(rm, n) := reg(r, n)
    0x8B /r                              => reg(r, n) := at(rm, n)
    0xC7 /0 iz                           => at(rm, n) := sext[8*n](iz)
    0x8D /r  if rm is ref(m)             => reg(r, n) := bits[8*n](ea(m with { seg: flat }))   // lea
    0x0F 0xB6 /r                         => reg(r, n) := zext[8*n](at(rm8, 1))    // movzx
    0x0F 0xB7 /r                         => reg(r, n) := zext[8*n](at(rm, 2))
    0x0F 0xBE /r                         => reg(r, n) := sext[8*n](at(rm8, 1))    // movsx
    0x0F 0xBF /r                         => reg(r, n) := sext[8*n](at(rm, 2))
    0x87 /r => {                                                          // xchg
      let a = at(rm, n)
      let b = reg(r, n)
      at(rm, n) := b
      reg(r, n) := a
    }
    // cmov: the source is read, and a 32-bit destination zero-extended,
    // even when the condition is false
    0x0F 0x40+cc /r => {
      let v = at(rm, n)
      reg(r, n) := if cond(flags, cc) { v } else { reg(r, n) }
    }

    REP 0xA5                             => rep_movs(n)
    REP 0xAB                             => rep_stos(n)
    0xA5                                 => movs(n)
    0xAB                                 => stos(n)

    0x69 /r iz                           => imul3(n, r, at(rm, n), sext[8*n](iz))
    0x6B /r ib                           => imul3(n, r, at(rm, n), sext[8*n](ib))
    0x98                                 => widen(n)           // cbw / cwde / cdqe
    REP 0x0F 0xBC /r                     => tzcnt(n, r, at(rm, n))
    0x0F 0xBC /r                         => bsf(n, r, at(rm, n))
    0x0F 0xA3 /r  if rm is gp(g)         => bt(n, at(rm, n), uint(reg(r, n)))   // register operand only
    0x0F 0xBA /4 ib                      => bt(n, at(rm, n), uint(ib))
    0x0F 0xB1 /r  if rm is ref(m)        => cmpxchg(n, rm, r)
    LOCK 0x0F 0xB1 /r  if rm is ref(m)   => cmpxchg(n, rm, r)
    0x0F 0xC1 /r                         => xadd(n, rm, r)
    LOCK 0x0F 0xC1 /r  if rm is ref(m)   => xadd(n, rm, r)
    // locked read-modify-write on memory (cmp cannot be locked)
    for op in AluOp except cmp {
      LOCK {8*uint(op) + 0x01} /r  if rm is ref(_)  => alu(op, rm, reg(r, n))
    }
    LOCK 0x81 /op:AluOp iz  if rm is ref(_) && op != cmp  => alu(op, rm, sext[8*n](iz))
    LOCK 0x83 /op:AluOp ib  if rm is ref(_) && op != cmp  => alu(op, rm, sext[8*n](ib))
    0x90                                 => {}                  // nop, also 66 90
    0x0F 0x1F /0                         => {}                  // nop r/m: no memory access
  }

  // ---- 64-bit only
  0xB8+r id                              => reg(r, 4) := id
  REX.W 0xB8+r io                        => reg(r, 8) := io
  REX.W 0x63 /r                          => reg(r, 8) := sext[64](at(rm, 4))   // movsxd

  // ---- stack and control flow (operand size fixed to 64)
  0x50+r                                 => push(gpr[r])
  0x58+r                                 => { let v = pop(); gpr[r] := v }  // pop rsp: rsp := v
  0x6A ib                                => push(sext[64](ib))
  0x68 id                                => push(sext[64](id))
  0xFF /6                                => push(at(rm, 8))
  0xC9                                   => { gpr[rsp] := gpr[rbp]; gpr[rbp] := pop() }  // leave
  0xE8 cd                                => call_rel(sext[64](cd))
  0xFF /2                                => call_abs(at(rm, 8))
  0xC3                                   => rip := pop()
  REP 0xC3                               => rip := pop()        // "rep ret"
  0xE9 cd                                => jump_rel(sext[64](cd))
  0xEB cb                                => jump_rel(sext[64](cb))
  0xFF /4                                => rip := at(rm, 8)
  0x70+cc cb                             => if cond(flags, cc) { jump_rel(sext[64](cb)) }
  0x0F 0x80+cc cd                        => if cond(flags, cc) { jump_rel(sext[64](cd)) }

  // ---- strings and flags
  REP 0xA4                               => rep_movs(1)
  REP 0xAA                               => rep_stos(1)
  0xA4                                   => movs(1)
  0xAA                                   => stos(1)
  0xFC                                   => flags.df := false
  0xFD                                   => flags.df := true

  // ---- SSE: integer moves and logic (`r` / `rm` name XMM registers)
  P66 0x0F 0xEF /r                       => xmm[r] := xmm[r] xor xmm_at(rm, true)   // pxor
  P66 0x0F 0xEB /r                       => xmm[r] := xmm[r] | xmm_at(rm, true)     // por
  P66 0x0F 0xDB /r                       => xmm[r] := xmm[r] & xmm_at(rm, true)     // pand
  P66 0x0F 0x6F /r                       => xmm[r] := xmm_at(rm, true)              // movdqa
  P66 0x0F 0x7F /r                       => xmm_at(rm, true) := xmm[r]
  REP 0x0F 0x6F /r                       => xmm[r] := xmm_at(rm, false)             // movdqu
  REP 0x0F 0x7F /r                       => xmm_at(rm, false) := xmm[r]
  0x0F 0x28 /r                           => xmm[r] := xmm_at(rm, true)              // movaps
  0x0F 0x29 /r                           => xmm_at(rm, true) := xmm[r]
  0x0F 0x10 /r                           => xmm[r] := xmm_at(rm, false)             // movups
  0x0F 0x11 /r                           => xmm_at(rm, false) := xmm[r]
  P66 0x0F 0x73 /3 ib  if rm is gp(g)    => xmm[g] := xmm[g] >> (8 * uint(ib))      // psrldq
  P66 0x0F 0x73 /7 ib  if rm is gp(g)    => xmm[g] := xmm[g] << (8 * uint(ib))      // pslldq
  P66 REX.W 0x0F 0x7E /r                 => at(rm, 8) := xmm[r][63:0]               // movq r/m64, xmm
  P66 0x0F 0x7E /r                       => at(rm, 4) := xmm[r][31:0]               // movd r/m32, xmm
  P66 0x0F 0xD6 /r  if rm is ref(m)      => at(rm, 8) := xmm[r][63:0]               // movq m64, xmm
  P66 0x0F 0xD6 /r  if rm is gp(g)       => xmm[g] := zext[128](xmm[r][63:0])       // movq xmm, xmm
  P66 REX.W 0x0F 0x6E /r                 => xmm[r] := zext[128](at(rm, 8))          // movq xmm, r/m64
  P66 0x0F 0x6E /r                       => xmm[r] := zext[128](at(rm, 4))          // movd xmm, r/m32

  // ---- misc
  REP 0x90                               => {}                  // pause
  REP 0x0F 0x1E 0xFA                     => {}                  // endbr64
  0x0F 0x05                              => syscall()
  0x0F 0x0B                              => raise ud            // ud2
  0xF4                                   => raise segv(0, kernel)  // hlt: #GP in user mode
}

///////////////////////////////////////////////////////////////////////
//  5. Fetch & execute
//
//  The table elaborates to
//    fn   x86.decode(b: Bytes) -> Set[(nat, x86.Insn)]  -- matching rows, with length
//    proc x86.execute(i: x86.Insn)                      -- the row's statement

type Bytes = nat -> bits[8]

proc step() {
  let matches = x86.decode((i: nat) => vm.bytes[rip + bits[64](i)])
  if matches = {} { undefined }                     // unmodelled or invalid
  let (len, insn) = any m: (nat, x86.Insn) where m in matches
  return exec_insn(len, insn)
}

// a decoded instruction of `len` bytes at rip: fetched (executable), then
// executed with rip after it (per-instruction theorems: `step()` at known
// bytes is `exec_insn` of their one decoding)
proc exec_insn(len: nat, insn: x86.Insn) {
  touch_range(rip, len, exec)
  return exec_body(len, insn)
}

// the instruction after its bytes were fetched (code known to be
// executable: `exec_insn` is `exec_body`)
proc exec_body(len: nat, insn: x86.Insn) {
  rip := rip + bits[64](len)
  x86.execute(insn)
}
