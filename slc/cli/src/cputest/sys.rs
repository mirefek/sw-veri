//! System calls: each case runs in a forked child (so `mmap`, `brk`, `exit`
//! ... cannot disturb the harness) with stdin, stdout and stderr connected
//! to pipes. Which calls and arguments are sampled is the manual part: only
//! calls and argument shapes the spec models, and nothing that would block
//! (a matching `futex` wait) or damage the child (`MAP_FIXED` / `munmap`
//! outside the arena).

use super::cpu::{self, sys, CpuState, Fault};
use super::{Rng, CODE_END, DATA, RO_PAGE, SCRATCH, SCRATCH_LEN, WO_PAGE, XO_PAGE};

pub const PAGE: u64 = 0x1000;
/// pages the memory-management calls work on, prepared per case
pub const ARENA: u64 = 0x1100_0000;
pub const ARENA_PAGES: usize = 8;
const TASK_SIZE: u64 = (1 << 47) - PAGE;

/// What the spec's machine needs beyond registers and scratch memory.
#[derive(Clone, Debug, Default)]
pub struct SysEnv {
    /// arena page i: unmapped, or mapped with prot bits (r=1, w=2, x=4)
    pub arena: [Option<u8>; ARENA_PAGES],
    /// all of stdin (then end of file)
    pub input: Vec<u8>,
    pub brk_start: u64,
    pub brk: u64,
}

/// What the child observed.
pub struct SysResult {
    /// `None`: the child exited through the tested call (`exit`)
    pub fault: Option<Fault>,
    pub after: Vec<u8>,
    pub maps: String,
    pub brk: u64,
    pub exit: Option<u8>,
    pub out: [Vec<u8>; 2],
    pub consumed: usize,
}

fn value_of_status(status: i32) -> Result<u8, String> {
    if status & 0x7f == 0 {
        Ok(((status >> 8) & 0xff) as u8)
    } else {
        Err(format!("child killed by signal {}", status & 0x7f))
    }
}

/// A buffer address: usually in the data area, sometimes somewhere the
/// kernel must refuse (read-only, guard page, non-canonical, kernel half)
/// or across the start of the read-only page.
fn buffer(rng: &mut Rng, n: u64) -> u64 {
    match rng.below(12) {
        0 => RO_PAGE + rng.below(64),
        10 => WO_PAGE + rng.below(64),
        11 => XO_PAGE + rng.below(64),
        1 => CODE_END + rng.below(64),
        2 => 0x8000_0000_0000_0000 | rng.below(1 << 20),
        3 => 0xffff_8000_0000_0000 + rng.below(1 << 20),
        4 => RO_PAGE - rng.below(n.max(1)),
        _ => DATA + rng.below(0x800),
    }
}

/// Current program break and its start (field 47 of /proc/self/stat).
pub fn brk_now() -> (u64, u64) {
    let cur = sys(12, &[0]) as u64;
    let stat = std::fs::read_to_string("/proc/self/stat").unwrap_or_default();
    // fields after the command name "(...)"
    let rest = stat.rsplit_once(')').map(|x| x.1).unwrap_or("");
    let start = rest.split_whitespace().nth(47 - 3).and_then(|x| x.parse().ok()).unwrap_or(cur);
    (start, cur)
}

/// Samples a system call: sets rax and the argument registers, and the
/// process environment the call sees.
pub fn generate(rng: &mut Rng, st: &mut CpuState, scratch: &mut [u8]) -> SysEnv {
    let (brk_start, brk) = brk_now();
    let mut env = SysEnv { brk_start, brk, ..Default::default() };
    for p in env.arena.iter_mut() {
        *p = if rng.chance(25) { None } else { Some(rng.below(8) as u8) };
    }
    let n_in = rng.below(48);
    env.input = (0..n_in).map(|_| rng.next() as u8).collect();
    let arena_addr = |rng: &mut Rng| {
        let a = ARENA + PAGE * rng.below(ARENA_PAGES as u64);
        if rng.chance(10) { a + 1 + rng.below(PAGE - 1) } else { a }
    };
    let length = |rng: &mut Rng| match rng.below(6) {
        0 => 0,
        1 => PAGE * (1 + rng.below(3)) - rng.below(PAGE),
        _ => PAGE * (1 + rng.below(3)),
    };
    let (rax, rdi, rsi, rdx, r10, r8, r9): (u64, u64, u64, u64, u64, u64, u64);
    let r = |rng: &mut Rng| rng.value();
    match rng.below(11) {
        0 => {
            // read(0, buf, count)
            let n = rng.below(64);
            (rax, rdi, rsi, rdx, r10, r8, r9) = (0, 0, buffer(rng, n), n, r(rng), r(rng), r(rng));
        }
        1 => {
            // write(1 or 2, buf, count)
            let n = rng.below(64);
            (rax, rdi, rsi, rdx, r10, r8, r9) = (1, 1 + rng.below(2), buffer(rng, n), n, r(rng), r(rng), r(rng));
        }
        2 => {
            // mmap: anonymous private, fixed only inside the arena
            let fixed = rng.chance(50);
            let addr = if fixed {
                if rng.chance(10) { TASK_SIZE - PAGE } else { arena_addr(rng) }
            } else if rng.chance(50) {
                0
            } else {
                r(rng) & !(PAGE - 1)
            };
            let len = if addr == TASK_SIZE - PAGE { 2 * PAGE } else { length(rng) };
            let flags = if fixed { 0x32 } else { 0x22 };
            let off = if rng.chance(80) { 0 } else { r(rng) };
            (rax, rdi, rsi, rdx, r10, r8, r9) = (9, addr, len, rng.below(8), flags, u64::MAX, off);
        }
        3 => {
            // munmap inside the arena (or a range crossing the end of user space)
            let (a, l) = if rng.chance(10) { (TASK_SIZE - PAGE, 2 * PAGE) } else { (arena_addr(rng), length(rng)) };
            (rax, rdi, rsi, rdx, r10, r8, r9) = (11, a, l, r(rng), r(rng), r(rng), r(rng));
        }
        4 => {
            // mprotect in the arena (possibly running past a hole or its end)
            (rax, rdi, rsi, rdx, r10, r8, r9) = (10, arena_addr(rng), length(rng), rng.below(8), r(rng), r(rng), r(rng));
        }
        5 => {
            // brk: query, grow, shrink within the last page, below the start
            let new = match rng.below(4) {
                0 => 0,
                1 => brk + PAGE * rng.below(4) + rng.below(PAGE),
                2 => brk - rng.below(brk % PAGE + 1),
                _ => brk_start - 1 - rng.below(PAGE),
            };
            (rax, rdi, rsi, rdx, r10, r8, r9) = (12, new, r(rng), r(rng), r(rng), r(rng), r(rng));
        }
        6 => {
            // arch_prctl(ARCH_SET_FS, addr)
            (rax, rdi, rsi, rdx, r10, r8, r9) = (158, 0x1002, r(rng), r(rng), r(rng), r(rng), r(rng));
        }
        7 => {
            // futex: WAKE, or WAIT that must not block (value differs,
            // misaligned, or a faulting address)
            let private = if rng.chance(50) { 128 } else { 0 };
            if rng.chance(30) {
                let uaddr = if rng.chance(50) { buffer(rng, 4) & !3 } else { r(rng) };
                (rax, rdi, rsi, rdx, r10, r8, r9) = (202, uaddr, 1 + private, r(rng), r(rng), r(rng), r(rng));
            } else {
                let word_at = DATA + 4 * rng.below(0x200);
                let word = u32::from_le_bytes(scratch[(word_at - SCRATCH) as usize..][..4].try_into().unwrap());
                let uaddr = match rng.below(6) {
                    0 => word_at + 1 + rng.below(3),
                    1 => 0x8000_0000_0000_0000 | (rng.below(1 << 20) & !3),
                    2 => CODE_END + 4 * rng.below(64),
                    _ => word_at,
                };
                let val = (word ^ (1 + rng.below(0xffff_fffe) as u32)) as u64 | (r(rng) << 32);
                (rax, rdi, rsi, rdx, r10, r8, r9) = (202, uaddr, private, val, 0, r(rng), r(rng));
            }
        }
        8 => {
            // set_tid_address(ptr)
            (rax, rdi, rsi, rdx, r10, r8, r9) = (218, r(rng), r(rng), r(rng), r(rng), r(rng), r(rng));
        }
        _ => {
            // exit / exit_group(status)
            let nr = if rng.chance(50) { 60 } else { 231 };
            (rax, rdi, rsi, rdx, r10, r8, r9) = (nr, r(rng), r(rng), r(rng), r(rng), r(rng), r(rng));
        }
    }
    st.gpr[0] = rax;
    st.gpr[7] = rdi;
    st.gpr[6] = rsi;
    st.gpr[2] = rdx;
    st.gpr[10] = r10;
    st.gpr[8] = r8;
    st.gpr[9] = r9;
    env
}

#[repr(C)]
struct Shared {
    done: u64,
    fault: Fault,
    brk: u64,
    after: [u8; SCRATCH_LEN as usize],
    maps_len: u64,
    maps: [u8; 1 << 16],
}

fn pipe() -> (i32, i32) {
    let mut fds = [0i32; 2];
    sys(22, &[fds.as_mut_ptr() as u64]);
    (fds[0], fds[1])
}

fn read_all(fd: i32) -> Vec<u8> {
    let mut out = Vec::new();
    let mut buf = [0u8; 4096];
    loop {
        let n = sys(0, &[fd as u64, buf.as_mut_ptr() as u64, buf.len() as u64]);
        if n <= 0 {
            return out;
        }
        out.extend(&buf[..n as usize]);
    }
}

/// Runs the case in a child process.
pub fn run(st: &CpuState, insn: &[u8], scratch: &[u8], env: &SysEnv) -> Result<SysResult, String> {
    let shared = sys(9, &[0, std::mem::size_of::<Shared>() as u64, 3, 0x21, u64::MAX, 0]); // MAP_SHARED | MAP_ANONYMOUS
    if shared < 0 {
        return Err("mmap of the shared page failed".into());
    }
    let sh = shared as *mut Shared;
    let (in_r, in_w) = pipe();
    let (o1_r, o1_w) = pipe();
    let (o2_r, o2_w) = pipe();
    sys(1, &[in_w as u64, env.input.as_ptr() as u64, env.input.len() as u64]);
    sys(3, &[in_w as u64]);
    let pid = sys(57, &[]); // fork
    if pid == 0 {
        // the child
        sys(33, &[in_r as u64, 0]);
        sys(33, &[o1_w as u64, 1]);
        sys(33, &[o2_w as u64, 2]);
        for fd in [in_r, o1_r, o1_w, o2_r, o2_w] {
            sys(3, &[fd as u64]);
        }
        sys(9, &[ARENA, PAGE * ARENA_PAGES as u64, 3, 0x32, u64::MAX, 0]); // fresh arena
        for (i, p) in env.arena.iter().enumerate() {
            let a = ARENA + PAGE * i as u64;
            match p {
                None => sys(11, &[a, PAGE]),
                Some(p) => sys(10, &[a, PAGE, *p as u64]),
            };
        }
        sys(37, &[2]); // alarm: a blocked call kills the child
        let f = cpu::run_raw(st, insn, scratch);
        let maps = std::fs::read("/proc/self/maps").unwrap_or_default();
        let after = cpu::scratch_after();
        unsafe {
            let s = &mut *sh;
            s.fault = f;
            s.brk = sys(12, &[0]) as u64;
            s.after.copy_from_slice(&after);
            let n = maps.len().min(s.maps.len());
            s.maps[..n].copy_from_slice(&maps[..n]);
            s.maps_len = n as u64;
            s.done = 1;
        }
        sys(231, &[0]);
        unreachable!();
    }
    for fd in [o1_w, o2_w] {
        sys(3, &[fd as u64]);
    }
    let mut status = 0i32;
    sys(61, &[pid as u64, &mut status as *mut i32 as u64, 0, 0]);
    let out = [read_all(o1_r), read_all(o2_r)];
    let left = read_all(in_r).len();
    for fd in [in_r, o1_r, o2_r] {
        sys(3, &[fd as u64]);
    }
    let r = unsafe {
        let s = &*sh;
        if s.done == 1 {
            Ok(SysResult {
                fault: Some(s.fault),
                after: s.after.to_vec(),
                maps: String::from_utf8_lossy(&s.maps[..s.maps_len as usize]).into_owned(),
                brk: s.brk,
                exit: None,
                out,
                consumed: env.input.len() - left,
            })
        } else {
            value_of_status(status).map(|code| SysResult {
                fault: None,
                after: scratch.to_vec(),
                maps: String::new(),
                brk: 0,
                exit: Some(code),
                out,
                consumed: env.input.len() - left,
            })
        }
    };
    sys(11, &[shared as u64, std::mem::size_of::<Shared>() as u64]);
    r
}
