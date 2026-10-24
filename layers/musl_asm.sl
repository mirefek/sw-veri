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
