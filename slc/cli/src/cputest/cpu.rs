//! Running one instruction on this CPU and observing what it did.
//!
//! The instruction is placed at the end of an executable page, preceded by
//! `int3` bytes and followed by an inaccessible guard page, so every case
//! ends with a signal:
//!
//! * falling through: the fetch at the guard page faults (SIGSEGV, address =
//!   rip);
//! * a taken branch: the fetch at its target faults, or an `int3` before the
//!   instruction traps (SIGTRAP, rip = target + 1);
//! * the instruction itself raises: SIGSEGV / SIGFPE / SIGILL / SIGBUS with
//!   rip still at the instruction.
//!
//! The handler (on an alternate stack, since rsp belongs to the test) copies
//! the registers from the signal context and resumes the harness.

use super::{CODE, CODE_END, RO_PAGE, SCRATCH, SCRATCH_LEN, WO_PAGE, XO_PAGE};

/// The state the trampoline loads (and the handler stores).
#[repr(C)]
#[derive(Clone, Copy, Default, Debug)]
pub struct CpuState {
    pub gpr: [u64; 16], // rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8..r15
    pub flags: u64,
    pub xmm: [[u64; 2]; 16],
    /// segment bases for the case
    pub fs: u64,
    pub gs: u64,
}

/// How a case ended.
#[repr(C)]
#[derive(Clone, Copy, Default, Debug)]
pub struct Fault {
    pub signo: i32,
    pub code: i32,
    pub addr: u64,
    pub rip: u64,
    pub fs: u64,
    pub gs: u64,
    pub st: CpuState,
}

pub const SIGILL: i32 = 4;
pub const SIGTRAP: i32 = 5;
pub const SIGBUS: i32 = 7;
pub const SIGFPE: i32 = 8;
pub const SIGSEGV: i32 = 11;

std::arch::global_asm!(
    r#"
    .data
    .p2align 3
    .globl sl_saved_rsp
sl_saved_rsp: .quad 0
    .globl sl_saved_fs
sl_saved_fs:  .quad 0
    .globl sl_saved_gs
sl_saved_gs:  .quad 0
sl_code_ptr:  .quad 0
    .text
    .globl sl_run_case
sl_run_case:
    push rbx
    push rbp
    push r12
    push r13
    push r14
    push r15
    mov [rip + sl_saved_rsp], rsp
    mov [rip + sl_code_ptr], rsi
    // the case's segment bases: arch_prctl(ARCH_SET_FS / ARCH_SET_GS)
    mov r12, rdi
    mov eax, 158
    mov edi, 0x1002
    mov rsi, [r12 + 392]
    syscall
    mov eax, 158
    mov edi, 0x1001
    mov rsi, [r12 + 400]
    syscall
    mov rdi, r12
    movdqu xmm0,  [rdi + 136]
    movdqu xmm1,  [rdi + 152]
    movdqu xmm2,  [rdi + 168]
    movdqu xmm3,  [rdi + 184]
    movdqu xmm4,  [rdi + 200]
    movdqu xmm5,  [rdi + 216]
    movdqu xmm6,  [rdi + 232]
    movdqu xmm7,  [rdi + 248]
    movdqu xmm8,  [rdi + 264]
    movdqu xmm9,  [rdi + 280]
    movdqu xmm10, [rdi + 296]
    movdqu xmm11, [rdi + 312]
    movdqu xmm12, [rdi + 328]
    movdqu xmm13, [rdi + 344]
    movdqu xmm14, [rdi + 360]
    movdqu xmm15, [rdi + 376]
    push qword ptr [rdi + 128]
    popfq
    mov rax, [rdi + 0]
    mov rcx, [rdi + 8]
    mov rdx, [rdi + 16]
    mov rbx, [rdi + 24]
    mov rsp, [rdi + 32]
    mov rbp, [rdi + 40]
    mov rsi, [rdi + 48]
    mov r8,  [rdi + 64]
    mov r9,  [rdi + 72]
    mov r10, [rdi + 80]
    mov r11, [rdi + 88]
    mov r12, [rdi + 96]
    mov r13, [rdi + 104]
    mov r14, [rdi + 112]
    mov r15, [rdi + 120]
    mov rdi, [rdi + 56]
    jmp qword ptr [rip + sl_code_ptr]

    // the signal handler returns here, on the harness stack
    .globl sl_resume
sl_resume:
    mov eax, 158              // arch_prctl(ARCH_SET_FS / _GS, saved): back to the harness's
    mov edi, 0x1002
    mov rsi, [rip + sl_saved_fs]
    syscall
    mov eax, 158
    mov edi, 0x1001
    mov rsi, [rip + sl_saved_gs]
    syscall
    cld
    pop r15
    pop r14
    pop r13
    pop r12
    pop rbp
    pop rbx
    ret

    .globl sl_restorer
sl_restorer:
    mov eax, 15               // rt_sigreturn
    syscall
"#
);

extern "C" {
    fn sl_run_case(state: *const CpuState, code: *const u8);
    fn sl_resume();
    fn sl_restorer();
    static mut sl_saved_rsp: u64;
    static mut sl_saved_fs: u64;
    static mut sl_saved_gs: u64;
}

static mut FAULT: Fault =
    Fault { signo: 0, code: 0, addr: 0, rip: 0, fs: 0, gs: 0, st: CpuState { gpr: [0; 16], flags: 0, xmm: [[0; 2]; 16], fs: 0, gs: 0 } };
#[repr(C, align(64))]
struct AltStack([u8; 1 << 16]);
static mut ALT_STACK: AltStack = AltStack([0; 1 << 16]);
/// set while a case runs: other faults are the harness's own
static mut IN_CASE: bool = false;

pub unsafe fn syscall6(nr: u64, a: [u64; 6]) -> i64 {
    let r: i64;
    std::arch::asm!("syscall", inlateout("rax") nr as i64 => r, in("rdi") a[0], in("rsi") a[1], in("rdx") a[2],
        in("r10") a[3], in("r8") a[4], in("r9") a[5], lateout("rcx") _, lateout("r11") _);
    r
}

pub fn sys(nr: u64, a: &[u64]) -> i64 {
    let mut v = [0u64; 6];
    v[..a.len()].copy_from_slice(a);
    unsafe { syscall6(nr, v) }
}

/// The signal handler: records the state, then resumes `sl_resume` on the
/// harness stack. Uses no thread-local storage (fs may belong to the test).
extern "C" fn handler(sig: i32, info: *const u8, uc: *mut u8) {
    unsafe {
        if !IN_CASE {
            // a fault of the harness itself: default action (crash) on return
            let dfl = [0u64; 4];
            syscall6(13, [sig as u64, dfl.as_ptr() as u64, 0, 8, 0, 0]);
            return;
        }
        IN_CASE = false;
        // struct sigcontext at uc + 40: r8..r15, rdi, rsi, rbp, rbx, rdx,
        // rax, rcx, rsp, rip, eflags, ..., fpstate at index 23
        let g = uc.add(40) as *mut u64;
        const ORDER: [usize; 16] = [13, 14, 12, 11, 15, 10, 9, 8, 0, 1, 2, 3, 4, 5, 6, 7];
        let mut st = CpuState::default();
        for (i, &j) in ORDER.iter().enumerate() {
            st.gpr[i] = *g.add(j);
        }
        st.flags = *g.add(17);
        let fp = *g.add(23) as *const u64;
        if !fp.is_null() {
            for i in 0..16 {
                st.xmm[i] = [*fp.add(20 + 2 * i), *fp.add(21 + 2 * i)]; // fxsave: xmm0 at byte 160
            }
        }
        let (mut fs, mut gs) = (0u64, 0u64);
        syscall6(158, [0x1003, &mut fs as *mut u64 as u64, 0, 0, 0, 0]); // ARCH_GET_FS
        syscall6(158, [0x1004, &mut gs as *mut u64 as u64, 0, 0, 0, 0]); // ARCH_GET_GS
        st.fs = fs;
        st.gs = gs;
        FAULT = Fault {
            signo: sig,
            code: *(info.add(8) as *const i32),
            addr: *(info.add(16) as *const u64),
            rip: *g.add(16),
            fs,
            gs,
            st,
        };
        *g.add(16) = sl_resume as *const () as u64;
        *g.add(15) = sl_saved_rsp;
        *g.add(17) = 0x202;
    }
}

unsafe fn mmap_fixed(addr: u64, len: u64, prot: u64) -> Result<(), String> {
    // MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED_NOREPLACE
    let r = syscall6(9, [addr, len, prot, 0x22 | 0x100000, u64::MAX, 0]);
    if r as u64 != addr {
        return Err(format!("mmap at {:#x} failed ({})", addr, r));
    }
    Ok(())
}

/// Address ranges this process can execute besides the test page (the
/// harness itself, libraries, vDSO): a branch there must not be run.
pub struct Setup {
    pub exec: Vec<(u64, u64)>,
}

/// Maps the test pages and installs the signal handlers.
pub fn setup() -> Result<Setup, String> {
    unsafe {
        mmap_fixed(SCRATCH, SCRATCH_LEN, 3)?;
        mmap_fixed(CODE, CODE_END - CODE, 7)?;
        mmap_fixed(CODE_END, 0x1000, 0)?; // guard page
        // alternate signal stack
        let ss = [std::ptr::addr_of_mut!(ALT_STACK) as u64, 0, 1 << 16];
        if sys(131, &[ss.as_ptr() as u64, 0]) != 0 {
            return Err("sigaltstack failed".into());
        }
        // SA_SIGINFO | SA_ONSTACK | SA_RESTORER
        let act = [handler as *const () as u64, 4 | 0x0800_0000 | 0x0400_0000, sl_restorer as *const () as u64, 0];
        for sig in [SIGILL, SIGTRAP, SIGBUS, SIGFPE, SIGSEGV] {
            if sys(13, &[sig as u64, act.as_ptr() as u64, 0, 8]) != 0 {
                return Err(format!("rt_sigaction({}) failed", sig));
            }
        }
        let (mut fs, mut gs) = (0u64, 0u64);
        sys(158, &[0x1003, &mut fs as *mut u64 as u64]);
        sys(158, &[0x1004, &mut gs as *mut u64 as u64]);
        sl_saved_fs = fs;
        sl_saved_gs = gs;
    }
    let maps = std::fs::read_to_string("/proc/self/maps").map_err(|e| e.to_string())?;
    let mut exec: Vec<(u64, u64)> = parse_maps(&maps).into_iter().filter(|m| m.2.x && m.0 != CODE).map(|m| (m.0, m.1)).collect();
    exec.push((XO_PAGE, XO_PAGE + 0x1000)); // executable during a case: random bytes
    Ok(Setup { exec })
}

/// The fs and gs bases the harness runs with.
pub fn saved_segs() -> (u64, u64) {
    unsafe { (sl_saved_fs, sl_saved_gs) }
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Perm {
    pub r: bool,
    pub w: bool,
    pub x: bool,
}

/// `start end perms` of /proc/self/maps.
pub fn parse_maps(text: &str) -> Vec<(u64, u64, Perm)> {
    let mut out = Vec::new();
    for l in text.lines() {
        let mut it = l.split_whitespace();
        let (Some(range), Some(p)) = (it.next(), it.next()) else { continue };
        let Some((a, b)) = range.split_once('-') else { continue };
        let (Ok(a), Ok(b)) = (u64::from_str_radix(a, 16), u64::from_str_radix(b, 16)) else { continue };
        let p = p.as_bytes();
        out.push((a, b, Perm { r: p[0] == b'r', w: p[1] == b'w', x: p[2] == b'x' }));
    }
    out
}

/// Runs `insn` at the end of the code page from state `st` and scratch
/// contents `scratch`; returns how it ended and the scratch area after.
pub fn run(st: &CpuState, insn: &[u8], scratch: &[u8]) -> (Fault, Vec<u8>) {
    let f = run_raw(st, insn, scratch);
    (f, scratch_after())
}

/// The scratch area after a case (makes all of it readable again).
pub fn scratch_after() -> Vec<u8> {
    sys(10, &[RO_PAGE, 0x3000, 3]);
    unsafe { std::slice::from_raw_parts(SCRATCH as *const u8, SCRATCH_LEN as usize).to_vec() }
}

/// `run`, leaving the protections of the case in place (for a child that
/// reports its memory map); `scratch_after` reads the result.
pub fn run_raw(st: &CpuState, insn: &[u8], scratch: &[u8]) -> Fault {
    unsafe {
        let code = CODE as *mut u8;
        std::ptr::write_bytes(code, 0xcc, (CODE_END - CODE) as usize);
        let start = CODE_END - insn.len() as u64;
        std::ptr::copy_nonoverlapping(insn.as_ptr(), start as *mut u8, insn.len());
        std::ptr::copy_nonoverlapping(scratch.as_ptr(), SCRATCH as *mut u8, scratch.len());
        // read-only, write-only and exec-only during the case
        sys(10, &[RO_PAGE, 0x1000, 1]);
        sys(10, &[WO_PAGE, 0x1000, 2]);
        sys(10, &[XO_PAGE, 0x1000, 4]);
        FAULT = Fault::default();
        IN_CASE = true;
        sl_run_case(st, start as *const u8);
        FAULT
    }
}
