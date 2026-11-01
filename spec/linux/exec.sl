spec x86_64_linux

// Process start (execve) of a static, non-PIE ELF64 executable.
//
// Only what Linux guarantees is stated. Randomized addresses (stack, brk),
// the vDSO, and the values of most auxiliary vector entries stay open.

type File = Seq[bits[8]]

// little-endian unsigned number of n bytes at `off`
fn le_at(f: File, off: nat, n: nat) -> nat = sum i in 0..n. uint(f[off + i]) * 256^i

///////////////////////////////////////////////////////////////////////
//  ELF header and program headers

const ET_EXEC   : nat = 2
const EM_X86_64 : nat = 0x3e
const PT_LOAD   : nat = 1

pred elf_ok(f: File) =
  len(f) >= 64 && le_at(f, 0, 4) = 0x464c457f &&     // "\x7fELF"
  uint(f[4]) = 2 && uint(f[5]) = 1 &&                // 64-bit, little-endian
  le_at(f, 16, 2) = ET_EXEC && le_at(f, 18, 2) = EM_X86_64 &&
  le_at(f, 54, 2) = 56                               // program header size

fn entry_of(f: File) -> nat = le_at(f, 24, 8)
fn phoff(f: File) -> nat = le_at(f, 32, 8)
fn phnum(f: File) -> nat = le_at(f, 56, 2)
fn ph(f: File, i: nat) -> nat = phoff(f) + 56 * i

record Segment { flags: nat, offset: nat, vaddr: nat, filesz: nat, memsz: nat }

pred is_load(f: File, i: nat) = i < phnum(f) && le_at(f, ph(f, i), 4) = PT_LOAD

fn segment(f: File, i: nat) -> Segment =
  Segment { flags: le_at(f, ph(f, i) + 4, 4), offset: le_at(f, ph(f, i) + 8, 8),
            vaddr: le_at(f, ph(f, i) + 16, 8), filesz: le_at(f, ph(f, i) + 32, 8),
            memsz: le_at(f, ph(f, i) + 40, 8) }

// PF_X = 1, PF_W = 2, PF_R = 4
fn seg_prot(s: Segment) -> Prot = Prot { r: s.flags[2], w: s.flags[1], x: s.flags[0] }

pred seg_page(s: Segment, p: nat) =
  s.memsz > 0 && s.vaddr / PAGE <= p && p <= (s.vaddr + s.memsz - 1) / PAGE

// segments are mapped in order: a page shared by two segments gets the
// protection of the later one
pred last_on_page(f: File, i: nat, p: nat) =
  is_load(f, i) && seg_page(segment(f, i), p) &&
  (all j: nat. is_load(f, j) && j > i -> !seg_page(segment(f, j), p))

pred covered(f: File, p: nat) = ex i: nat. is_load(f, i) && seg_page(segment(f, i), p)

pred segment_bytes(f: File, s: Segment, vm: Vm) =
  (all a: nat. s.vaddr <= a && a < s.vaddr + s.filesz ->
     vm.bytes[bits[64](a)] = f[s.offset + (a - s.vaddr)]) &&
  (all a: nat. s.vaddr + s.filesz <= a && a < s.vaddr + s.memsz ->     // bss
     vm.bytes[bits[64](a)] = 0)

pred image_loaded(f: File, vm: Vm) =
  (all i: nat, p: nat. last_on_page(f, i, p) ->
     vm.pages[p] = some(Page { prot: seg_prot(segment(f, i)), kind: anon })) &&
  (all i: nat. is_load(f, i) -> segment_bytes(f, segment(f, i), vm))

// end of the highest segment
fn image_end(f: File) -> nat = max({e: nat | ex i: nat. is_load(f, i) && e = segment(f, i).vaddr + segment(f, i).memsz})

///////////////////////////////////////////////////////////////////////
//  Initial stack: argc, argv, envp, auxv

const AT_NULL   : nat = 0
const AT_PHDR   : nat = 3
const AT_PHENT  : nat = 4
const AT_PHNUM  : nat = 5
const AT_PAGESZ : nat = 6
const AT_ENTRY  : nat = 9
const AT_UID    : nat = 11
const AT_EUID   : nat = 12
const AT_GID    : nat = 13
const AT_EGID   : nat = 14
const AT_SECURE : nat = 23
const AT_RANDOM : nat = 25
const AT_EXECFN : nat = 31

fn u64_at(vm: Vm, a: nat) -> nat = uint(le(vm.bytes, bits[64](a), 8))

// a NUL-terminated string at `q`
pred cstring(vm: Vm, q: nat, s: List[bits[8]]) =
  (all i: nat. i < len(s) -> vm.bytes[bits[64](q + i)] = s[i]) && vm.bytes[bits[64](q + len(s))] = 0

pred readable(vm: Vm, a: nat, n: nat) =
  all i: nat. i < n -> mapped(vm, (a + i) / PAGE) && vm.pages[(a + i) / PAGE].value.prot.r

// argc at sp, then argv[], 0, envp[], 0, auxv pairs ending with (AT_NULL, 0)
pred stack_layout(vm: Vm, sp: nat, argv: List[List[bits[8]]], envp: List[List[bits[8]]], auxv: List[(nat, nat)]) =
  u64_at(vm, sp) = len(argv) &&
  (all i: nat. i < len(argv) -> cstring(vm, u64_at(vm, sp + 8 + 8 * i), argv[i]) &&
     readable(vm, u64_at(vm, sp + 8 + 8 * i), len(argv[i]) + 1)) &&
  u64_at(vm, sp + 8 + 8 * len(argv)) = 0 &&
  (all i: nat. i < len(envp) -> cstring(vm, u64_at(vm, sp + 16 + 8 * len(argv) + 8 * i), envp[i]) &&
     readable(vm, u64_at(vm, sp + 16 + 8 * len(argv) + 8 * i), len(envp[i]) + 1)) &&
  u64_at(vm, sp + 16 + 8 * len(argv) + 8 * len(envp)) = 0 &&
  auxv_at(vm, sp + 24 + 8 * len(argv) + 8 * len(envp), auxv)

pred auxv_at(vm: Vm, a: nat, auxv: List[(nat, nat)]) =
  len(auxv) >= 1 &&
  (all k: nat. k < len(auxv) -> u64_at(vm, a + 16 * k) = auxv[k][0] && u64_at(vm, a + 16 * k + 8) = auxv[k][1]) &&
  auxv[len(auxv) - 1] = (AT_NULL, 0) &&
  (all k: nat. k + 1 < len(auxv) -> auxv[k][0] != AT_NULL)

// the value of an auxv entry (keys are unique)
pred aux(auxv: List[(nat, nat)], key: nat, v: nat) = ex k: nat. k < len(auxv) && auxv[k] = (key, v)

// the n bytes at a within [sp, top): the initial stack's data
pred in_stack(sp: nat, top: nat, a: nat, n: nat) = sp <= a && a + n <= top

// where the initial stack's data lies (Linux's create_elf_tables): all of it
// between sp and the stack's top -- the tables (argc, argv, envp, auxv), the
// argument and environment strings, AT_RANDOM's 16 bytes, and the
// executable's name, a string AT_EXECFN points to
pred stack_data(vm: Vm, sp: nat, top: nat, argv: List[List[bits[8]]], envp: List[List[bits[8]]], auxv: List[(nat, nat)]) =
  in_stack(sp, top, sp, 24 + 8 * len(argv) + 8 * len(envp) + 16 * len(auxv)) &&
  (all i: nat. i < len(argv) -> in_stack(sp, top, u64_at(vm, sp + 8 + 8 * i), len(argv[i]) + 1)) &&
  (all i: nat. i < len(envp) -> in_stack(sp, top, u64_at(vm, sp + 16 + 8 * len(argv) + 8 * i), len(envp[i]) + 1)) &&
  (ex q: nat. aux(auxv, AT_RANDOM, q) && in_stack(sp, top, q, 16)) &&
  (ex q: nat, s: List[bits[8]]. aux(auxv, AT_EXECFN, q) && cstring(vm, q, s) && in_stack(sp, top, q, len(s) + 1))

pred auxv_ok(f: File, vm: Vm, os: Os, auxv: List[(nat, nat)]) =
  aux(auxv, AT_PAGESZ, PAGE) && aux(auxv, AT_ENTRY, entry_of(f)) &&
  aux(auxv, AT_PHENT, 56) && aux(auxv, AT_PHNUM, phnum(f)) &&
  // the kernel reports the credentials and secure-execution mode
  aux(auxv, AT_SECURE, if os.secure { 1 } else { 0 }) &&
  aux(auxv, AT_UID, uint(os.creds.uid)) && aux(auxv, AT_EUID, uint(os.creds.euid)) &&
  aux(auxv, AT_GID, uint(os.creds.gid)) && aux(auxv, AT_EGID, uint(os.creds.egid)) &&
  (ex q: nat. aux(auxv, AT_PHDR, q) && readable(vm, q, 56 * phnum(f)) &&
     (all i: nat. i < 56 * phnum(f) -> vm.bytes[bits[64](q + i)] = f[phoff(f) + i])) &&
  (ex q: nat. aux(auxv, AT_RANDOM, q) && readable(vm, q, 16)) &&
  (all k: nat, j: nat. k < len(auxv) && j < len(auxv) && k != j -> auxv[k][0] != auxv[j][0] || auxv[k][0] = AT_NULL)

///////////////////////////////////////////////////////////////////////
//  The initial process state

pred stack_pages(vm: Vm, lo: nat, top: nat) =
  lo < top && top <= TASK_SIZE / PAGE && uint(vm.stack_top) = top * PAGE &&
  vm.stack_limit >= (top - lo) * PAGE &&
  (all p: nat. lo <= p && p < top ->
     vm.pages[p] = some(Page { prot: Prot { r: true, w: true, x: false }, kind: stack })) &&
  (all p: nat. (p < lo || p >= top) && mapped(vm, p) -> vm.pages[p].value.kind != stack)

pred exec_state(f: File, argv: List[List[bits[8]]], envp: List[List[bits[8]]], m: Machine) =
  elf_ok(f) &&
  image_loaded(f, m.vm) &&
  (ex lo: nat, top: nat, auxv: List[(nat, nat)].
     stack_pages(m.vm, lo, top) &&
     // other mappings (vDSO, vvar) are not writable
     (all p: nat. mapped(m.vm, p) && !covered(f, p) && !(lo <= p && p < top) -> !m.vm.pages[p].value.prot.w) &&
     // the stack is above the image (Linux puts it at the top of the address
     // space; a non-PIE image is where the file says, far below)
     (all i: nat, p: nat. is_load(f, i) && seg_page(segment(f, i), p) -> p < lo) &&
     // nothing at page 0 unless the image puts it there (assumes the process
     // was not started with the SVr4 personality MMAP_PAGE_ZERO, which maps it)
     (!covered(f, 0) -> !mapped(m.vm, 0)) &&
     lo * PAGE <= uint(m.gpr[rsp]) && uint(m.gpr[rsp]) < top * PAGE &&
     stack_layout(m.vm, uint(m.gpr[rsp]), argv, envp, auxv) && auxv_ok(f, m.vm, m.os, auxv) &&
     stack_data(m.vm, uint(m.gpr[rsp]), top * PAGE, argv, envp, auxv)) &&
  // brk: page aligned, somewhere above the image (randomized), empty, in
  // the user space
  uint(m.vm.brk_start) % PAGE = 0 && uint(m.vm.brk_start) >= image_end(f) && uint(m.vm.brk_start) >= PAGE &&
  uint(m.vm.brk_start) <= TASK_SIZE &&
  m.vm.brk = m.vm.brk_start &&
  // registers: rip at the entry point, rsp 16-byte aligned, the rest zero
  uint(m.rip) = entry_of(f) && uint(m.gpr[rsp]) % 16 = 0 &&
  (all r: Reg. r != rsp -> m.gpr[r] = 0) &&
  (all r: Reg. m.xmm[r] = 0) &&
  m.flags = Flags { cf: false, pf: false, af: false, zf: false, sf: false, df: false, of: false } &&
  m.fs_base = 0 && m.gs_base = 0 &&
  m.os.events = []
