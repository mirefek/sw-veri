spec x86_64_linux

// Semantics of the modelled instructions.
// Every proc runs with `rip` already pointing to the next instruction.

///////////////////////////////////////////////////////////////////////
//  Flags

fn even_parity(x: bits[8]) -> bool = (sum i in 0..8. if x[i] { 1 } else { 0 }) % 2 = 0

proc set_result_flags[w: Width](r: bits[w]) {
  flags.zf := r = 0
  flags.sf := r[w-1]
  flags.pf := even_parity(r[7:0])
}

proc set_add_flags[w: Width](a: bits[w], b: bits[w], cin: nat, r: bits[w]) {
  set_result_flags(r)
  flags.cf := uint(a) + uint(b) + cin >= 2^w
  flags.of := sint(a) + sint(b) + cin != sint(r)
  flags.af := (a xor b xor r)[4]
}

proc set_sub_flags[w: Width](a: bits[w], b: bits[w], cin: nat, r: bits[w]) {
  set_result_flags(r)
  flags.cf := uint(a) < uint(b) + cin
  flags.of := sint(a) - sint(b) - cin != sint(r)
  flags.af := (a xor b xor r)[4]
}

proc set_logic_flags[w: Width](r: bits[w]) {
  set_result_flags(r)
  flags.cf := false
  flags.of := false
  havoc flags.af
}

// condition codes, as in Jcc / SETcc / CMOVcc
fn cond(f: Flags, cc: bits[4]) -> bool {
  let c = match cc[3:1] {
    0 => f.of
    1 => f.cf
    2 => f.zf
    3 => f.cf || f.zf
    4 => f.sf
    5 => f.pf
    6 => f.sf != f.of
    7 => f.zf || f.sf != f.of
  }
  return c != cc[0]                  // odd codes are the negations
}

///////////////////////////////////////////////////////////////////////
//  Integer arithmetic

enum AluOp : bits[3] { add, or, adc, sbb, and, sub, xor, cmp }

// Operand sizes are in bytes (n); values of n bytes are bits[8*n].

proc alu[n: Size](op: AluOp, dst: Operand, b: bits[8*n]) {
  let a   = at(dst, n)
  let cin = if op in {adc, sbb} && flags.cf { 1 } else { 0 }
  match op {
    add, adc => {
      let r = a + b + bits[8*n](cin)
      set_add_flags(a, b, cin, r)
      at(dst, n) := r
    }
    sub, sbb, cmp => {
      let r = a - b - bits[8*n](cin)
      set_sub_flags(a, b, cin, r)
      if op != cmp { at(dst, n) := r }
    }
    and, or, xor => {
      let r = match op { and => a & b, or => a | b, xor => a xor b }
      set_logic_flags(r)
      at(dst, n) := r
    }
  }
}

proc test[w: Width](a: bits[w], b: bits[w]) {
  set_logic_flags(a & b)
}

enum UnOp : bits[3] { not = 2, neg = 3 }

proc unary(op: UnOp, n: Size, dst: Operand) {
  let a = at(dst, n)
  match op {
    not => at(dst, n) := ~a                      // flags unaffected
    neg => {
      set_sub_flags(0, a, 0, -a)
      at(dst, n) := -a
    }
  }
}

// inc / dec keep CF
proc incdec(dec: bool, n: Size, dst: Operand) {
  let a  = at(dst, n)
  let cf = flags.cf
  if dec { set_sub_flags(a, 1, 0, a - 1); at(dst, n) := a - 1 }
  else   { set_add_flags(a, 1, 0, a + 1); at(dst, n) := a + 1 }
  flags.cf := cf
}

// unsigned rdx:rax := rax * src
proc mul(n: Size, src: bits[8*n]) {
  let p = uint(reg(rax, n)) * uint(src)
  reg(rax, n) := bits[8*n](p)
  reg(rdx, n) := bits[8*n](p / 2^(8*n))
  flags.cf := p >= 2^(8*n)
  flags.of := flags.cf
  havoc flags.{sf, zf, af, pf}
}

// two-operand signed multiply: dst := dst * src
proc imul2(n: Size, dst: Reg, src: bits[8*n]) {
  let p = sint(reg(dst, n)) * sint(src)
  reg(dst, n) := bits[8*n](p)
  flags.cf := sint(bits[8*n](p)) != p
  flags.of := flags.cf
  havoc flags.{sf, zf, af, pf}
}

// unsigned rdx:rax / src  (n >= 2; the 1-byte form uses ax and is not modelled)
proc div(n: Size, src: bits[8*n]) {
  require n >= 2
  let d = uint(src)
  if d = 0 { raise div_error }
  let x = uint(reg(rdx, n)) * 2^(8*n) + uint(reg(rax, n))
  if x / d >= 2^(8*n) { raise div_error }
  reg(rax, n) := bits[8*n](x / d)
  reg(rdx, n) := bits[8*n](x % d)
  havoc flags.{cf, of, sf, zf, af, pf}
}

// signed division, quotient rounded toward zero
proc idiv(n: Size, src: bits[8*n]) {
  require n >= 2
  let d = sint(src)
  if d = 0 { raise div_error }
  let x = sint(reg(rdx, n)) * 2^(8*n) + uint(reg(rax, n))
  let q = tdiv(x, d)
  if q < -2^(8*n-1) || q >= 2^(8*n-1) { raise div_error }
  reg(rax, n) := bits[8*n](q)
  reg(rdx, n) := bits[8*n](x - q * d)
  havoc flags.{cf, of, sf, zf, af, pf}
}

fn tdiv(n: int, d: int) -> int = if (n < 0) = (d < 0) { abs(n) / abs(d) } else { -(abs(n) / abs(d)) }

// cwd / cdq / cqo: sign-fill rdx from rax
proc sign_fill(n: Size) {
  reg(rdx, n) := if reg(rax, n)[8*n-1] { -1 } else { 0 }
}

enum ShiftOp : bits[3] { shl = 4, shr = 5, sar = 7 }

proc shift(op: ShiftOp, n: Size, dst: Operand, count: bits[8]) {
  let w = 8 * n
  let k = uint(count) % (if n = 8 { 64 } else { 32 })
  if k = 0 {                                       // flags unaffected, but the
    at(dst, n) := at(dst, n)                       // operand is accessed and a 32-bit
    return                                         // register zero-extended (measured)
  }
  let a = at(dst, n)
  let r = match op { shl => a << k, shr => a >> k, sar => a >>s k }
  if k > w { havoc flags.cf }                      // only for n in {1, 2}
  else { flags.cf := match op { shl => a[w - k], shr, sar => a[k - 1] } }
  if k = 1 {
    flags.of := match op { shl => r[w-1] != flags.cf, shr => a[w-1], sar => false }
  } else { havoc flags.of }
  set_result_flags(r)
  havoc flags.af
  at(dst, n) := r
}

// three-operand signed multiply: dst := a * b
proc imul3(n: Size, dst: Reg, a: bits[8*n], b: bits[8*n]) {
  let p = sint(a) * sint(b)
  reg(dst, n) := bits[8*n](p)
  flags.cf := sint(bits[8*n](p)) != p
  flags.of := flags.cf
  havoc flags.{sf, zf, af, pf}
}

// cbw / cwde / cdqe: sign-extend the lower half of the accumulator
proc widen(n: Size) {
  if n = 8 { gpr[rax] := sext[64](reg(rax, 4)) }
  else if n = 4 { reg(rax, 4) := sext[32](reg(rax, 2)) }
  else { reg(rax, 2) := sext[16](reg(rax, 1)) }
}

// index of the lowest set bit (x != 0)
fn ctz[w: Width](x: bits[w]) -> nat = min({i: nat | i < w && x[i]})

// tzcnt (F3 0F BC). CPUs without BMI1 ignore the F3 prefix and execute bsf,
// which agrees for a non-zero source.
proc tzcnt(n: Size, dst: Reg, src: bits[8*n]) {
  if cpu.bmi1 {
    let c = if src = 0 { 8 * n } else { ctz(src) }
    reg(dst, n) := bits[8*n](c)
    flags.cf := src = 0
    flags.zf := c = 0
    havoc flags.{of, sf, af, pf}
  } else {
    bsf(n, dst, src)
  }
}

// bsf: for a zero source the destination's value is not specified
// (Intel: undefined, AMD: unchanged)
proc bsf(n: Size, dst: Reg, src: bits[8*n]) {
  if src = 0 { havoc gpr[dst] } else { reg(dst, n) := bits[8*n](ctz(src)) }
  flags.zf := src = 0
  havoc flags.{cf, of, sf, af, pf}
}

// bt with a register operand, or an immediate offset: CF := the bit
proc bt(n: Size, a: bits[8*n], off: nat) {
  flags.cf := a[off % (8 * n)]
  havoc flags.{of, sf, af, pf}
}

// cmpxchg (memory destination): compare with the accumulator; on failure
// the destination is still written (with its old value).
// Register destinations are not modelled (no table row): they are useless
// for synchronization. Measured on Intel i7-1185G7, `cmpxchg ecx, edx`:
// on success rax is unchanged and rcx := zext(edx); on failure
// rax := zext(ecx) and rcx is NOT written back (its upper half is kept),
// unlike the manual's pseudocode. Unverified on AMD.
proc cmpxchg(n: Size, dst: Operand, src: Reg) {
  let d = at(dst, n)
  let acc = reg(rax, n)
  set_sub_flags(acc, d, 0, acc - d)
  if acc = d {
    at(dst, n) := reg(src, n)
  } else {
    at(dst, n) := d
    reg(rax, n) := d
  }
}

// xadd: src := old dst, then dst := dst + src (for `xadd r, r` the sum
// wins). `src` may be the base register of a memory `dst`, whose address is
// computed before the register write.
proc xadd(n: Size, dst0: Operand, src: Reg) {
  let dst = resolve(dst0, n)
  let d = at(dst, n)
  let v = reg(src, n)
  let r = d + v
  set_add_flags(d, v, 0, r)
  reg(src, n) := d
  at(dst, n) := r
}

///////////////////////////////////////////////////////////////////////
//  SSE: integer moves and logic (no floating point)

// An XMM operand: a register (ModRM register number) or 16 bytes of
// memory. Legacy SSE instructions other than the explicitly unaligned ones
// (movups, movdqu) fault (#GP) on a memory operand not aligned to 16.
view xmm_at(o: Operand, aligned: bool) : bits[128] {
  get {
    match o {
      gp(r)  => return xmm[r]
      hi8(r) => undefined
      ref(m) => {
        stack_check(m, 16)
        let a = ea(m)
        if aligned && uint(a) % 16 != 0 { raise segv(0, kernel) }
        return mem(a, 16)
      }
    }
  }
  set(v) {
    match o {
      gp(r)  => xmm[r] := v
      hi8(r) => undefined
      ref(m) => {
        stack_check(m, 16)
        let a = ea(m)
        if aligned && uint(a) % 16 != 0 { raise segv(0, kernel) }
        mem(a, 16) := v
      }
    }
  }
}

///////////////////////////////////////////////////////////////////////
//  Stack and control flow

proc push(v: bits[64]) {
  let sp = gpr[rsp] - 8
  stack_range(sp, 8)
  mem(sp, 8) := v                  // may grow the stack, or overflow it
  gpr[rsp] := sp
}

proc pop() -> bits[64] {
  stack_range(gpr[rsp], 8)
  let v = mem(gpr[rsp], 8)
  gpr[rsp] := gpr[rsp] + 8
  return v
}

proc jump_rel(off: bits[64])  { rip := rip + off }
proc call_rel(off: bits[64])  { push(rip); rip := rip + off }

proc call_abs(target: Addr)   { push(rip); rip := target }

///////////////////////////////////////////////////////////////////////
//  Strings

proc string_step(n: Size) -> bits[64] = if flags.df { -bits[64](n) } else { bits[64](n) }

// movs / stos without rep: one element
proc movs(n: Size) {
  mem(gpr[rdi], n) := mem(gpr[rsi], n)
  gpr[rsi] := gpr[rsi] + string_step(n)
  gpr[rdi] := gpr[rdi] + string_step(n)
}

proc stos(n: Size) {
  mem(gpr[rdi], n) := reg(rax, n)
  gpr[rdi] := gpr[rdi] + string_step(n)
}

// rep movs{b,w,d,q}: n bytes at a time
proc rep_movs(n: Size) {
  while gpr[rcx] != 0 {
    mem(gpr[rdi], n) := mem(gpr[rsi], n)
    gpr[rsi] := gpr[rsi] + string_step(n)
    gpr[rdi] := gpr[rdi] + string_step(n)
    gpr[rcx] := gpr[rcx] - 1
  }
}

// rep stos{b,w,d,q}
proc rep_stos(n: Size) {
  while gpr[rcx] != 0 {
    mem(gpr[rdi], n) := reg(rax, n)
    gpr[rdi] := gpr[rdi] + string_step(n)
    gpr[rcx] := gpr[rcx] - 1
  }
}

///////////////////////////////////////////////////////////////////////
//  System call

// Linux preserves all registers except rax, rcx and r11.
proc syscall() {
  gpr[rcx] := rip
  gpr[r11] := rflags_word(flags)
  gpr[rax] := linux_syscall(gpr[rax], gpr[rdi], gpr[rsi], gpr[rdx],
                            gpr[r10], gpr[r8], gpr[r9])   // linux/process.sl
}
