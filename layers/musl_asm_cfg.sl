layer musl_asm_cfg uses musl_asm, gimple, abi, x86_64_linux

// musl's assembly functions (layers/musl_asm.sl) as control-flow graphs,
// as `slc gimple --readable --cfg` makes them: a block per label, `bb` the
// block to run. Beyond the generated ones' guide (F_cfg_live, F_cfg_widths),
// the registers the locals live in (F_cfg_regs: local, register) -- at
// each label a live local is its register's value.

// memcpy: the blocks at 404cf2 (2), the test of d's alignment (3), the
// byte loop (4), the words (5), the bytes left (6)
proc[World] memcpy(d: Addr, s: Addr, n: bits[64]) -> Addr {
  var bb: nat = 2
  var di: bits[64] = any bits[64]
  var k: bits[64] = any bits[64]
  var r: bits[32] = any bits[32]
  var rv: bits[64] = any bits[64]
  var si: bits[64] = any bits[64]
  loop {
    if bb < 4 {
      if bb < 3 {
        // <bb 2>
        rv := d
        di := d
        si := s
        k := n
        if k < 8 {
          bb := 5
        } else {
          bb := 3
        }
      } else {
        // <bb 3>
        if (bits[32](di) & 7) = 0 {
          bb := 5
        } else {
          bb := 4
        }
      }
    } else {
      if bb < 5 {
        // <bb 4>
        move(di, si, 1)
        di := di + 1
        si := si + 1
        k := k - 1
        if (bits[32](di) & 7) != 0 {
          bb := 4
        } else {
          bb := 5
        }
      } else {
        if bb < 6 {
          // <bb 5>
          let c = k >> 3
          move_words(di, si, c)
          di := di + c * 8
          si := si + c * 8
          r := bits[32](k) & 7
          if r = 0 {
            return rv
          } else {
            bb := 6
          }
        } else {
          // <bb 6>
          move(di, si, 1)
          di := di + 1
          si := si + 1
          r := r - 1
          if r != 0 {
            bb := 6
          } else {
            return rv
          }
        }
      }
    }
  }
}
fn memcpy_cfg_live() -> List[(nat, nat)] = [(2, 0), (3, 27), (4, 27), (5, 27), (6, 29)]
fn memcpy_cfg_widths() -> List[nat] = [64, 64, 32, 64, 64]
fn memcpy_cfg_regs() -> List[(nat, nat)] = [(0, 7), (1, 2), (2, 2), (3, 0), (4, 6)]
fn memcpy_fun() -> CFun2[World] = (args: Args) => {
  require len(args) >= 3
  let r = memcpy(bits[64](args[0]), bits[64](args[1]), bits[64](args[2]))
  return (result(r), any bits[64])
}
