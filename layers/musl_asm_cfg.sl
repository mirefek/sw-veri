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

// memset: the blocks at 404d24 (2), the test of n (3), the stores from
// both ends (4 to 9), the return (10), more than 126 bytes (11), the words
// (12), d raised to its 16-byte boundary (13)
proc[World] memset(d: Addr, c: bits[64], n: bits[64]) -> Addr {
  var bb: nat = 2
  var cnt: bits[64] = any bits[64]
  var cs: bits[64] = any bits[64]
  var di: bits[64] = any bits[64]
  var e: bits[32] = any bits[32]
  var k: bits[64] = any bits[64]
  var rv: bits[64] = any bits[64]
  var v: bits[64] = any bits[64]
  loop {
    if bb < 8 {
      if bb < 5 {
        if bb < 3 {
          // <bb 2>
          cs := c
          di := d
          k := n
          v := bits[64](bits[8](cs)) * 72340172838076673
          if k > 126 {
            bb := 11
          } else {
            bb := 3
          }
        } else {
          if bb < 4 {
            // <bb 3>
            if bits[32](k) = 0 {
              bb := 10
            } else {
              bb := 4
            }
          } else {
            // <bb 4>
            st8(di, 0, bits[8](cs))
            st8(di, k - 1, bits[8](cs))
            if bits[32](k) <= 2 {
              bb := 10
            } else {
              bb := 5
            }
          }
        }
      } else {
        if bb < 6 {
          // <bb 5>
          st16(di, 1, bits[16](v))
          st16(di, k - 3, bits[16](v))
          if bits[32](k) <= 6 {
            bb := 10
          } else {
            bb := 6
          }
        } else {
          if bb < 7 {
            // <bb 6>
            st32(di, 3, bits[32](v))
            st32(di, k - 7, bits[32](v))
            if bits[32](k) <= 14 {
              bb := 10
            } else {
              bb := 7
            }
          } else {
            // <bb 7>
            st64(di, 7, v)
            st64(di, k - 15, v)
            if bits[32](k) <= 30 {
              bb := 10
            } else {
              bb := 8
            }
          }
        }
      }
    } else {
      if bb < 11 {
        if bb < 9 {
          // <bb 8>
          st64(di, 15, v)
          st64(di, 23, v)
          st64(di, k - 31, v)
          st64(di, k - 23, v)
          if bits[32](k) <= 62 {
            bb := 10
          } else {
            bb := 9
          }
        } else {
          if bb < 10 {
            // <bb 9>
            st64(di, 31, v)
            st64(di, 39, v)
            st64(di, 47, v)
            st64(di, 55, v)
            st64(di, k - 63, v)
            st64(di, k - 55, v)
            st64(di, k - 47, v)
            st64(di, k - 39, v)
            bb := 10
          } else {
            // <bb 10>
            return di
          }
        }
      } else {
        if bb < 12 {
          // <bb 11>
          rv := di
          st64(di, k - 8, v)
          cnt := k
          if (bits[32](di) & 15) != 0 {
            bb := 13
          } else {
            bb := 12
          }
        } else {
          if bb < 13 {
            // <bb 12>
            cnt := cnt >> 3
            fill_words(di, v, cnt)
            return rv
          } else {
            // <bb 13>
            e := (0 - bits[32](di)) & 15
            st64(di, 0, v)
            st64(di, 8, v)
            cnt := cnt - bits[64](e)
            di := di + bits[64](e)
            bb := 12
          }
        }
      }
    }
  }
}
// (locals: cnt, cs, di, e, k, rv, v -- in rcx, rsi, rdi, edx, rdx, r8, rax)
fn memset_cfg_live() -> List[(nat, nat)] = [(2, 0), (3, 86), (4, 86), (5, 84), (6, 84), (7, 84), (8, 84), (9, 84), (10, 4), (11, 84), (12, 101), (13, 101)]
fn memset_cfg_widths() -> List[nat] = [64, 64, 64, 32, 64, 64, 64]
fn memset_cfg_regs() -> List[(nat, nat)] = [(0, 1), (1, 6), (2, 7), (3, 2), (4, 2), (5, 8), (6, 0)]
fn memset_fun() -> CFun2[World] = (args: Args) => {
  require len(args) >= 3
  let r = memset(bits[64](args[0]), bits[64](args[1]), bits[64](args[2]))
  return (result(r), any bits[64])
}

// __set_thread_area: one block at 40574c (2), its result in rax
proc[World] __set_thread_area(p: Addr) -> bits[64] {
  var bb: nat = 2
  var r: bits[64] = any bits[64]
  loop {
    // <bb 2>
    r := sys_set_fs(p)
    return r
  }
}
fn __set_thread_area_cfg_live() -> List[(nat, nat)] = [(2, 0)]
fn __set_thread_area_cfg_widths() -> List[nat] = [64]
fn __set_thread_area_cfg_regs() -> List[(nat, nat)] = [(0, 0)]
fn __set_thread_area_fun() -> CFun2[World] = (args: Args) => {
  require len(args) >= 1
  let r = __set_thread_area(bits[64](args[0]))
  return (result(r), any bits[64])
}

// _init: one block at 401000 (2)
proc[World] _init() {
  var bb: nat = 2
  var bb_none: nat = 0
  loop {
    // <bb 2>
    return
  }
}
fn _init_cfg_live() -> List[(nat, nat)] = [(2, 0)]
fn _init_cfg_widths() -> List[nat] = []
fn _init_cfg_regs() -> List[(nat, nat)] = []
fn _init_fun() -> CFun2[World] = (args: Args) => {
  _init()
  return (any bits[64], any bits[64])
}

// register_tm_clones: the blocks at 401140 (2), the registration's test
// (3), its call (4)
proc[World] register_tm_clones() {
  var bb: nat = 2
  var ax: bits[64] = any bits[64]
  var di: bits[64] = any bits[64]
  var si: bits[64] = any bits[64]
  loop {
    if bb < 3 {
      // <bb 2>
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
      } else {
        bb := 3
      }
    } else {
      if bb < 4 {
        // <bb 3>
        ax := 0
        if ax = 0 {
          return
        } else {
          bb := 4
        }
      } else {
        // <bb 4>
        undefined
      }
    }
  }
}
// (locals: ax, di, si -- in rax, rdi, rsi)
fn register_tm_clones_cfg_live() -> List[(nat, nat)] = [(2, 0), (3, 0), (4, 1)]
fn register_tm_clones_cfg_widths() -> List[nat] = [64, 64, 64]
fn register_tm_clones_cfg_regs() -> List[(nat, nat)] = [(0, 0), (1, 7), (2, 6)]
fn register_tm_clones_fun() -> CFun2[World] = (args: Args) => {
  register_tm_clones()
  return (any bits[64], any bits[64])
}

// deregister_tm_clones: the blocks at 401110 (2), the deregistration's
// test (3), its call (4)
proc[World] deregister_tm_clones() {
  var bb: nat = 2
  var ax: bits[64] = any bits[64]
  var di: bits[64] = any bits[64]
  loop {
    if bb < 3 {
      // <bb 2>
      di := __TMC_END__
      ax := __TMC_END__
      if ax = di {
        return
      } else {
        bb := 3
      }
    } else {
      if bb < 4 {
        // <bb 3>
        ax := 0
        if ax = 0 {
          return
        } else {
          bb := 4
        }
      } else {
        // <bb 4>
        undefined
      }
    }
  }
}
// (locals: ax, di -- in rax, rdi)
fn deregister_tm_clones_cfg_live() -> List[(nat, nat)] = [(2, 0), (3, 0), (4, 1)]
fn deregister_tm_clones_cfg_widths() -> List[nat] = [64, 64]
fn deregister_tm_clones_cfg_regs() -> List[(nat, nat)] = [(0, 0), (1, 7)]
fn deregister_tm_clones_fun() -> CFun2[World] = (args: Args) => {
  deregister_tm_clones()
  return (any bits[64], any bits[64])
}
