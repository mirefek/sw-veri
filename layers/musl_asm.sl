layer musl_asm uses gimple, abi, x86_64_linux

// musl's assembly functions as readable GIMPLE, written by hand (no GCC
// GIMPLE is behind them): each function's instructions as statements on the
// C world, its registers as locals. As the generated ones, a structured
// form (this layer: the C2 proofs' side) and the control-flow graph
// (musl_asm_cfg: the blocks as the code has them, C1's side), the one
// refining the other (`refines`). C1 checks the CFG form against the code,
// so nothing here is trusted.

///////////////////////////////////////////////////////////////////////
//  The string instructions' moves (the direction flag clear: the ABI's)

// movs: n bytes from s to d -- read, then written; both usable (and fewer
// than 2^64: the machine faults before), else undefined
proc[World] move(d: Addr, s: Addr, n: nat) {
  // (d as a word: it is one, by its type -- and so to the bookkeeping of
  // a caller's loop, which knows no types of its locals)
  let a = bits[64](uint(d))
  if !usable(vm, objs, uint(s), n, false) || !usable(vm, objs, uint(a), n, true) || n >= 2^64 { undefined }
  write_bytes(a, n, bytes_at(vm, s, n))
}

// rep movsq: c words from s to d, one at a time, upwards -- the 8c bytes
// moved as one when no word is read after a write reached it (d not above
// s within its words); that case not modelled (undefined, as overlapping
// copies are in C)
proc[World] move_words(d: Addr, s: Addr, c: bits[64]) {
  if uint(s) < uint(d) && uint(d) < uint(s) + 8 * uint(c) { undefined }
  move(d, s, 8 * uint(c))
}

///////////////////////////////////////////////////////////////////////
//  memcpy (src/string/x86_64/memcpy.s)
//
//   mov rax, rdi; cmp rdx, 8; jb 2f; test edi, 7; jz 2f
//   1: movsb; dec rdx; test edi, 7; jnz 1b
//   2: mov rcx, rdx; shr rcx, 3; rep movsq; and edx, 7; jz 1f
//   2: movsb; dec edx; jnz 2b
//   1: ret

// rep stosq: c words v at d, upwards -- usable (writable; fewer than 2^64
// bytes), else undefined
proc[World] fill_words(d: Addr, v: bits[64], c: bits[64]) {
  let a = bits[64](uint(d))
  if !usable(vm, objs, uint(a), 8 * uint(c), true) || 8 * uint(c) >= 2^64 { undefined }
  write_bytes(a, 8 * uint(c), sum i in 0..uint(c). uint(v) * 2^(64 * i))
}

proc[World] memcpy(d: Addr, s: Addr, n: bits[64]) -> Addr {
  var di: bits[64] = any bits[64]
  var k: bits[64] = any bits[64]
  var r: bits[32] = any bits[32]
  var rv: bits[64] = any bits[64]
  var si: bits[64] = any bits[64]
  rv := d
  di := d
  si := s
  k := n
  // (the bytes up to d's word boundary, if 8 or more)
  if !(k < 8) {
    if (bits[32](di) & 7) != 0 {
      loop {
        move(di, si, 1)
        di := di + 1
        si := si + 1
        k := k - 1
        if (bits[32](di) & 7) = 0 {
          break
        }
      }
    }
  }
  // (the words, then the bytes left)
  let c = k >> 3
  move_words(di, si, c)
  di := di + c * 8
  si := si + c * 8
  r := bits[32](k) & 7
  if r = 0 {
    return rv
  }
  loop {
    move(di, si, 1)
    di := di + 1
    si := si + 1
    r := r - 1
    if r = 0 {
      return rv
    }
  }
}

fn memcpy_fun() -> CFun2[World] = (args: Args) => {
  require len(args) >= 3
  let r = memcpy(bits[64](args[0]), bits[64](args[1]), bits[64](args[2]))
  return (result(r), any bits[64])
}

///////////////////////////////////////////////////////////////////////
//  memset (src/string/x86_64/memset.s)
//
//   movzbq sil, rax; movabs 0x0101010101010101, r8; imul r8, rax
//   cmp rdx, 126; ja 2f
//   (up to 126 bytes: from both ends, stores of 1, 2, 4, 8, 2x8, 4x8
//   bytes, each pair overlapping the next's, until they meet)
//   1: mov rdi, rax; ret
//   2: (more: the last 8 bytes; d aligned to 16 -- its first 16 bytes
//   stored, d raised to the boundary --, then rep stosq of the words)

proc[World] memset(d: Addr, c: bits[64], n: bits[64]) -> Addr {
  var cnt: bits[64] = any bits[64]
  var cs: bits[64] = any bits[64]
  var di: bits[64] = any bits[64]
  var e: bits[32] = any bits[32]
  var k: bits[64] = any bits[64]
  var rv: bits[64] = any bits[64]
  var v: bits[64] = any bits[64]
  cs := c
  di := d
  k := n
  // (the byte in every byte of a word)
  v := bits[64](bits[8](cs)) * 72340172838076673
  // (more than 126 bytes: the last 8, then the words from d's 16-byte
  // boundary -- d not aligned: its first 16 bytes stored, d raised to it)
  if k > 126 {
    rv := di
    st64(di, k - 8, v)
    cnt := k
    if (bits[32](di) & 15) != 0 {
      e := (0 - bits[32](di)) & 15
      st64(di, 0, v)
      st64(di, 8, v)
      cnt := cnt - bits[64](e)
      di := di + bits[64](e)
    }
    cnt := cnt >> 3
    fill_words(di, v, cnt)
    return rv
  }
  // (up to 126: from both ends, until the stores meet)
  if bits[32](k) = 0 {
    return di
  }
  st8(di, 0, bits[8](cs))
  st8(di, k - 1, bits[8](cs))
  if bits[32](k) <= 2 {
    return di
  }
  st16(di, 1, bits[16](v))
  st16(di, k - 3, bits[16](v))
  if bits[32](k) <= 6 {
    return di
  }
  st32(di, 3, bits[32](v))
  st32(di, k - 7, bits[32](v))
  if bits[32](k) <= 14 {
    return di
  }
  st64(di, 7, v)
  st64(di, k - 15, v)
  if bits[32](k) <= 30 {
    return di
  }
  st64(di, 15, v)
  st64(di, 23, v)
  st64(di, k - 31, v)
  st64(di, k - 23, v)
  if bits[32](k) <= 62 {
    return di
  }
  st64(di, 31, v)
  st64(di, 39, v)
  st64(di, 47, v)
  st64(di, 55, v)
  st64(di, k - 63, v)
  st64(di, k - 55, v)
  st64(di, k - 47, v)
  st64(di, k - 39, v)
  return di
}

fn memset_fun() -> CFun2[World] = (args: Args) => {
  require len(args) >= 3
  let r = memset(bits[64](args[0]), bits[64](args[1]), bits[64](args[2]))
  return (result(r), any bits[64])
}

///////////////////////////////////////////////////////////////////////
//  __set_thread_area (src/thread/x86_64/__set_thread_area.s)
//
//   mov rsi, rdi; mov edi, 0x1002; mov eax, 158; syscall; ret
//
// arch_prctl(ARCH_SET_FS, p): the thread pointer p (before main)
proc[World] __set_thread_area(p: Addr) -> bits[64] {
  var r: bits[64] = any bits[64]
  r := sys_set_fs(p)
  return r
}
fn __set_thread_area_fun() -> CFun2[World] = (args: Args) => {
  require len(args) >= 1
  let r = __set_thread_area(bits[64](args[0]))
  return (result(r), any bits[64])
}

///////////////////////////////////////////////////////////////////////
//  _init (crti.s / crtn.s: the prologue's and the epilogue's halves)
//
//   push rax; pop rax; ret
//
// nothing (the stack realigned for the calls between the halves: none)
proc[World] _init() {
  return
}
fn _init_fun() -> CFun2[World] = (args: Args) => {
  _init()
  return (any bits[64], any bits[64])
}

///////////////////////////////////////////////////////////////////////
//  register_tm_clones (gcc's crtstuff.c, crtbegin.o: the init_array's
//  one constructor, frame_dummy's tail)
//
//   lea rdi, [__TMC_END__]; lea rsi, [__TMC_END__]; sub rsi, rdi
//   mov rax, rsi; shr rsi, 63; sar rax, 3; add rsi, rax; sar rsi, 1
//   je 1f; mov rax, 0; test rax, rax; je 1f; jmp rax
//   1: ret
//
// the transactional-memory clone table's size (its start and end both
// __TMC_END__: none), and its registration (_ITM_registerTMCloneTable, a
// weak symbol not linked: 0) -- so nothing
const __TMC_END__: Addr = 0x408010
proc[World] register_tm_clones() {
  var ax: bits[64] = any bits[64]
  var di: bits[64] = any bits[64]
  var si: bits[64] = any bits[64]
  di := __TMC_END__
  si := __TMC_END__
  si := si - di
  ax := si
  si := si >> 63
  ax := ax >>s 3
  si := si + ax
  si := si >>s 1
  if si = 0 {
    return
  }
  ax := 0
  if ax = 0 {
    return
  }
  // (jmp rax: no code at 0)
  undefined
}
fn register_tm_clones_fun() -> CFun2[World] = (args: Args) => {
  register_tm_clones()
  return (any bits[64], any bits[64])
}

///////////////////////////////////////////////////////////////////////
//  frame_dummy (crtstuff.c: the init_array's entry)
//
//   endbr64; jmp register_tm_clones
//
// register_tm_clones itself (a jump to it: its run from this entry)
fn frame_dummy_fun() -> CFun2[World] = register_tm_clones_fun()
