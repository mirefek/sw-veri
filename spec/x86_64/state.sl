spec x86_64_linux

// x86_64 user-mode machine state

type Addr   = bits[64]
type Size   = {n: nat | n in {1, 2, 4, 8}}       // operand size in bytes
type Width  = {w: nat | w in {8, 16, 32, 64}}    // the same in bits (flag helpers)

enum Reg : bits[4] {
  rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi,
  r8, r9, r10, r11, r12, r13, r14, r15
}

// Features of the CPU the program runs on: fixed for the whole run and
// not specified at process start (claims hold for every CPU).
record Cpu {
  bmi1 : bool           // BMI1: tzcnt (otherwise its encoding executes as bsf)
  pku  : bool           // protection keys, used by Linux to make execute-only
                        // mappings unreadable (otherwise they are readable)
}

record Flags {
  cf, pf, af, zf, sf, df, of : bool
}

state Machine {
  gpr     : Reg -> bits[64]
  xmm     : Reg -> bits[128]    // xmm0..xmm15, numbered like the GPRs
  rip     : Addr
  flags   : Flags
  cpu     : Cpu           // never changed by any instruction
  fs_base : Addr
  gs_base : Addr
  vm      : Vm        // memory.sl
  os      : Os        // linux/process.sl
}

// SIGSEGV, with exactly what Linux reports in siginfo: si_addr and si_code.
// Whether it was a stack overflow is not part of the exception; it is
// decided from the address and the state at the fault, see
// `stack_space` / `below_stack_space` in memory.sl.
enum SegvCode {
  maperr,          // SEGV_MAPERR: nothing mapped (incl. refused stack growth)
  accerr,          // SEGV_ACCERR: mapped without the needed permission
  kernel,          // SI_KERNEL:   #GP (non-canonical address, hlt, ...); addr is 0
  pkuerr           // SEGV_PKUERR: denied by a protection key (execute-only memory)
}

exception segv(addr: Addr, code: SegvCode)
exception stack_fault                 // SIGBUS:  #SS, a non-canonical address
                                      //          through rsp / rbp (stack segment)
exception div_error                   // SIGFPE:  #DE
exception ud                          // SIGILL:  #UD
exception exit(status: bits[8])       // exit / exit_group

///////////////////////////////////////////////////////////////////////
//  Registers

// The low n bytes of a register. Writing 4 bytes zero-extends into the
// full register, writing 1 or 2 bytes keeps the rest.
view reg(r: Reg, n: Size) : bits[8*n] {
  get = gpr[r][8*n-1:0]
  set(v) {
    if n = 4 { gpr[r] := zext[64](v) } else { gpr[r][8*n-1:0] := v }
  }
}

// ah, ch, dh, bh
view hibyte(r: Reg) : bits[8] {
  get    = gpr[r][15:8]
  set(v) { gpr[r][15:8] := v }
}

// the RFLAGS word as seen by pushf / syscall (r11)
fn rflags_word(f: Flags) -> bits[64] {
  var x: bits[64] = 0x202          // bit 1 is reserved-one, IF = 1 in user mode
  x[0] := f.cf; x[2] := f.pf; x[4] := f.af; x[6] := f.zf
  x[7] := f.sf; x[10] := f.df; x[11] := f.of
  return x
}

///////////////////////////////////////////////////////////////////////
//  Operands

enum Seg { flat, cs, fs, gs }    // flat: no override; cs has base 0 in 64-bit mode
type Base = nobase | rip_rel | base(Reg)

record MemOp {
  seg   : Seg
  base  : Base
  index : Option[Reg]
  scale : {s: nat | s in {1, 2, 4, 8}}
  disp  : bits[64]
}

type Operand = gp(Reg) | hi8(Reg) | ref(MemOp)    // register, ah..bh, memory

// Effective address. `rip` already points to the next instruction,
// which is exactly what RIP-relative addressing needs.
proc ea(m: MemOp) -> Addr {
  let s = match m.seg   { flat, cs => 0, fs => fs_base, gs => gs_base }
  let b = match m.base  { nobase => 0, rip_rel => rip, base(r) => gpr[r] }
  let i = match m.index { none => 0, some(r) => gpr[r] * bits[64](m.scale) }
  return s + b + i + m.disp
}

// The operand (accessed with n bytes) with its effective address computed
// now. The CPU computes addresses once, before the instruction writes
// anything; an instruction that writes a register and then a memory operand
// resolves it first. The stack-segment check is made here, since the
// resolved operand no longer names its base register.
proc resolve(o: Operand, n: Size) -> Operand {
  match o {
    ref(m) => {
      stack_check(m, n)
      return ref(MemOp { seg: flat, base: nobase, index: none, scale: 1, disp: ea(m) })
    }
    _      => return o
  }
}

// "r/m" operand: a register or memory, accessed with n bytes
view at(o: Operand, n: Size) : bits[8*n] {
  get {
    match o {
      gp(r)  => return reg(r, n)
      hi8(r) => { require n = 1; return hibyte(r) }
      ref(m) => { stack_check(m, n); return mem(ea(m), n) }
    }
  }
  set(v) {
    match o {
      gp(r)  => reg(r, n) := v
      hi8(r) => { require n = 1; hibyte(r) := bits[8](v) }
      ref(m) => { stack_check(m, n); mem(ea(m), n) := v }
    }
  }
}

// Addressing through rsp or rbp (without a segment override) uses the stack
// segment: a non-canonical address raises #SS instead of #GP.
proc stack_check(m: MemOp, n: nat) {
  if m.seg = flat && (m.base = base(rsp) || m.base = base(rbp)) { stack_range(ea(m), n) }
}

proc stack_range(a: Addr, n: nat) {
  if !(all i: nat. i < n -> canonical(a + bits[64](i))) { raise stack_fault }
}
