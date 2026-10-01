#!/usr/bin/env python3
"""Generate proofs/get_slot_index_abi.core: get_slot_index's machine code
implements its readable GIMPLE under the ABI (abi.implements2_at).

    scripts/gen-get-slot-index-abi.py > proofs/get_slot_index_abi.core

The proof spells out the states it relates (the machine's final state, the
ABI's world views and its normal return), which are large terms: they are
built here. The reasoning is in the theorems it uses:
  - get_slot_index.run (proofs/get_slot_index_run.core): the machine's run;
  - gsi.fun_ok / gsi.fun_raises (proofs/get_slot_index.core): the spec;
  - abi.ret_intro / abi.ub_intro (proofs/abi_restore.core, proofs/abi.core):
    abi_function's normal return and its undefined-behavior case;
  - gsi.stack_access / gsi.store_view (proofs/get_slot_index_stack.core):
    the stack slot and the return address, from entry_ok.
"""

SPEC = 'c_src_malloc_mallocng_malloc.get_slot_index_fun()'
CODE = 'get_slot_index.code()'
ARGS = 'set_select(list_type(bits(64)), x0. ord_le(seq_len(x0), 6))'
KEYS = 'insert("gpr", insert("xmm", insert("rip", insert("flags", insert("cpu", insert("fs_base", insert("gs_base", insert("vm", insert("os", empty)))))))))'
WKEYS = 'insert("vm", insert("os", insert("fs_base", insert("cpu", insert("sp", empty)))))'
FK = 'insert("cf", insert("pf", insert("af", insert("zf", insert("sf", insert("df", insert("of", empty)))))))'
ARG_REGS = 'seq_concat(seq_concat(seq_concat(seq_concat(seq_concat(seq_one(7), seq_one(6)), seq_one(2)), seq_one(1)), seq_one(8)), seq_one(9))'

# the entry state s: rsp, rdi; the caller's sp, the return address
RSP = 'app(app(s, "gpr"), 4)'
RDI = 'app(app(s, "gpr"), 7)'
SP = 'bits_add(64, %s, 8)' % RSP
RET = 'x86_64_linux.le(app(app(s, "vm"), "bytes"), %s, 8)' % RSP

# the memory after the store of rdi to the slot at rsp - 8; the ABI's view of
# memory is chosen to be it (the slot is scratch space)
SL = 'x86_64_linux.store_le(app(app(s, "vm"), "bytes"), bits_add(64, %s, 18446744073709551608), 8, %s)' % (RSP, RDI)
VM1 = 'fn_update(app(s, "vm"), "bytes", %s)' % SL


def world(m):
    return ('fn_update(fn_update(fn_update(fn_update(fn_update(empty, "vm", %s), "os", app(%s, "os")), '
            '"fs_base", app(%s, "fs_base")), "cpu", app(%s, "cpu")), "sp", %s)' % (VM1, m, m, m, SP))


# abi_function's states, as abi.ret_intro names them
X7 = 'rec_merge(%s, ghost_part(s, %s))' % (world('s'), KEYS)
S1 = 'fn_update(fn_update(fn_update(s, "vm", app(s, "vm")), "os", app(s, "os")), "fs_base", app(s, "fs_base"))'
M1 = 'rec_merge(restrict(%s, %s), ghost_part(%s, %s))' % (S1, KEYS, X7, WKEYS)
IN1 = 'rec_merge(%s, ghost_part(%s, %s))' % (world(M1), M1, KEYS)      # the spec's world
IN0 = 'rec_merge(%s, ghost_part(s, %s))' % (world('s'), KEYS)          # the entry world

# the spec's result, and the machine's
P = 'bits_of_int(64, app(args, 0))'
R0 = 'bits_and(32, bits_of_int(8, gimple.bytes_at(app(%s, "vm"), int_sub(%s, 3), 1)), 31)' % (IN1, P)
R = 'bits_and(32, x86_64_linux.le(app(%s, "bytes"), bits_add(64, %s, 18446744073709551613), 1), 31)' % (VM1, RDI)

# the machine's final state (get_slot_index.run, with af the undefined AF)
FL_UPDATES = [("zf", '%s = 0' % R), ("sf", 'bit(%s, 31)' % R), ("pf", 'x86_64_linux.even_parity(bits_slice(%s, 7, 0))' % R),
              ("cf", "false"), ("of", "false"), ("af", "af")]
FL = 'app(s, "flags")'
for k, val in FL_UPDATES:
    FL = 'fn_update(%s, "%s", %s)' % (FL, k, val)
GPR = 'fn_update(fn_update(app(s, "gpr"), 0, %s), 4, %s)' % (R, SP)
FINAL = 'fn_update(fn_update(fn_update(fn_update(s, "vm", %s), "flags", %s), "gpr", %s), "rip", %s)' % (VM1, FL, GPR, RET)

# abi.ret_intro's final state N, for: v = nv = VM1, w2 = IN1, r0 = R0,
# r1 = rdx, the havoc's choice g, xm, fl = the machine's gpr, xmm, flags
r1 = 'app(app(s, "gpr"), 2)'
M2 = 'fn_update(fn_update(fn_update(%s, "vm", %s), "os", app(%s, "os")), "fs_base", app(%s, "fs_base"))' % (M1, VM1, IN1, IN1)
X12 = 'rec_merge(restrict(%s, %s), ghost_part(%s, %s))' % (M2, KEYS, IN1, WKEYS)
X = 'fn_update(fn_update(fn_update(%s, "gpr", app(s, "gpr")), "xmm", app(s, "xmm")), "flags", %s)' % (X12, FL)
G = 'app(%s, "gpr")' % X
for r in [3, 5, 12, 13, 14, 15]:
    G = 'fn_update(%s, %d, app(app(s, "gpr"), %d))' % (G, r, r)
XF = 'fn_update(%s, "gpr", %s)' % (X, G)
A = 'fn_update(%s, "gpr", fn_update(app(%s, "gpr"), 4, %s))' % (XF, XF, SP)
B = 'fn_update(%s, "gpr", fn_update(app(%s, "gpr"), 0, %s))' % (A, A, R0)
C = 'fn_update(%s, "gpr", fn_update(app(%s, "gpr"), 2, %s))' % (B, B, r1)
D = 'fn_update(%s, "flags", fn_update(app(%s, "flags"), "df", false))' % (C, C)
N = 'fn_update(%s, "rip", %s)' % (D, RET)

# when the spec is defined (gsi.fun_ok), on the view VM1
COND = 'int_le(3, %s) && !(int_sub(%s, 3) = 0) && gimple.usable(%s, int_sub(%s, 3), 1, false)' % (P, P, VM1, P)
COND0 = COND.replace(VM1, 'app(%s, "vm")' % IN0)

# the run's memory accesses (get_slot_index.run's hypotheses)
A1 = '(all i. i in omega -> int_lt(i, 8) -> x86_64_linux.can_access(app(s, "vm"), bits_add(64, bits_add(64, %s, 18446744073709551608), bits_of_int(64, i)), 1))' % RSP
A2 = '(all i. i in omega -> int_lt(i, 8) -> x86_64_linux.can_access(app(s, "vm"), bits_add(64, bits_add(64, %s, 18446744073709551608), bits_of_int(64, i)), 0))' % RSP
A4 = '(all i. i in omega -> int_lt(i, 1) -> x86_64_linux.can_access(app(s, "vm"), bits_add(64, bits_add(64, %s, 18446744073709551613), bits_of_int(64, i)), 0))' % RDI
A7 = '(all i. i in omega -> int_lt(i, 8) -> x86_64_linux.can_access(app(s, "vm"), bits_add(64, %s, bits_of_int(64, i)), 0))' % RSP


def inst(name, args):
    t = name
    for a in args:
        t = 'all_elim(%s, {%s})' % (t, a)
    return t


def mps(t, hs):
    for h in hs:
        t = 'mp(%s, %s)' % (t, h)
    return t


def flags_pred(x):
    return ('(((((((is_fun(%s) && dom(%s) = %s) && app(%s, "cf") in bool) && app(%s, "pf") in bool) && app(%s, "af") in bool) && '
            'app(%s, "zf") in bool) && app(%s, "sf") in bool) && app(%s, "df") in bool) && app(%s, "of") in bool' % ((x, x, FK) + (x,) * 7))


# the final flags are a function on the flags' keys, field by field
chain = ''
F = 'app(s, "flags")'
for i, (k, val) in enumerate(FL_UPDATES):
    G2 = 'fn_update(%s, "%s", %s)' % (F, k, val)
    chain += '  have k%d: "%s" in %s by simp()\n' % (i, k, FK)
    chain += '  have c%d := mp(mp(mp(fn_update_fd[f := %s, k := "%s", v := %s, d := %s], cf%d), cd%d), k%d)\n' % (i, F, k, val, FK, i, i, i)
    chain += '  have cf%d: is_fun(%s) by taut(c%d)\n  have cd%d: dom(%s) = %s by taut(c%d)\n' % (i + 1, G2, i, i + 1, G2, FK, i)
    F = G2
assert F == FL
fields = ''
SRC = {"zf": "bz", "sf": "bsf", "pf": "bpf", "cf": "bf", "of": "bf", "af": "baf"}
for k, val in FL_UPDATES:
    fields += '  have e_%s: app(%s, "%s") = (%s) by simp()\n  have fb_%s := rewrite(sym(e_%s), %s)\n' % (k, FL, k, val, k, k, SRC[k])
fields += ('  have e_df: app(%s, "df") = app(app(s, "flags"), "df") by simp()\n  have b_df: app(app(s, "flags"), "df") in bool by taut(pf0)\n'
           '  have fb_df := rewrite(sym(e_df), b_df)\n' % FL)

V = dict(SPEC=SPEC, CODE=CODE, ARGS=ARGS, KEYS=KEYS, FK=FK, SP=SP, SL=SL, VM1=VM1, IN0=IN0, IN1=IN1, W0=world('s'),
         P=P, R0=R0, R=R, FL=FL, FINAL=FINAL, N=N, COND=COND, COND0=COND0, A1=A1, A2=A2, A4=A4, A7=A7, L=ARG_REGS,
         chain=chain, fields=fields, PF0=flags_pred('app(s, "flags")'), PFL=flags_pred(FL), PX=flags_pred('x0'),
         hspec=mps(inst('gsi.fun_ok', [IN1, 'args', r1]), ['hw2', 'hA', 'h1', 'c1', 'c2', 'c3']),
         rt=mps(inst('abi.ret_intro', ['f', SPEC, 'args', 's', VM1, VM1, IN1, R0, r1, 'app(s, "gpr")', 'app(s, "xmm")', FL]),
                ['fbu', 'su', 'hvu', 'hv', 'hsv', 'hsp', 'hsv1', 'hm1', 'hspec', 'hw2', 'h0', 'h1', 'hvu', 'hv', 'hnm', 'gu', 'tg', 'xu', 'tx', 'fu', 'tf']),
         ub=mps(inst('abi.ub_intro', ['f', SPEC, 'args', 's', 'o', VM1]), ['hp', 'ho', 'hvu', 'hv', 'hsv1', 'hm1', 'hsv', 'hsp', 'hra']))

print('''// Generated by scripts/gen-get-slot-index-abi.py: get_slot_index's machine
// code (at -O0, at 0x402103) implements its readable GIMPLE under the ABI
// (C1 for this function): `gsi.implements`.
//
//   slc kernel-check core/prelude.core core/logic.core core/sets.core core/nat.core core/records.core \\
//     core/list.core core/loop.core build/c_mallocng_malloc.core proofs/x86.core proofs/x86_code.core \\
//     build/get_slot_index_steps.core proofs/get_slot_index_run.core proofs/abi.core proofs/abi_restore.core \\
//     proofs/gimple.core proofs/get_slot_index.core proofs/get_slot_index_stack.core proofs/get_slot_index_abi.core
//
// The cases of abi_function: its precondition fails (anything is allowed);
// the spec raises (undefined behavior: `gsi.ub`); the normal return
// (`gsi.normal`): the machine's run ends in the state abi.ret_intro
// describes, with the ABI's view of memory showing the stack slot as the
// machine wrote it, and the havoc choosing the machine's registers.
// Conditional on the open loop lemmas (core/loop.core), through the run and
// abi_restore.''')

print('''
// the normal case: the spec's result is the machine's
theorem gsi.normal: all f args s af. s in x86_64_linux.Machine -> args in %(ARGS)s -> abi.entry_ok(s, args) -> int_lt(0, seq_len(args)) ->
  %(COND)s -> (af = false || af = true) -> pair(s, ok(%(FINAL)s, empty)) in univ(1) ->
  runs(abi.abi_function(single(empty), f, %(SPEC)s, args), s, ok(%(FINAL)s, empty))
proof
  fix f
  fix args
  fix s
  fix af
  assume hM: s in x86_64_linux.Machine
  assume hA: args in %(ARGS)s
  assume he: abi.entry_ok(s, args)
  assume hl: int_lt(0, seq_len(args))
  assume hc: %(COND)s
  assume haf: af = false || af = true
  assume hp: pair(s, ok(%(FINAL)s, empty)) in univ(1)
  have mtyp: s in powerset(cart(%(KEYS)s, univ(1))) && is_fun(s) && dom(s) = %(KEYS)s && app(s, "gpr") in fn_space(x86_64_linux.Reg, bits(64)) && app(s, "xmm") in fn_space(x86_64_linux.Reg, bits(128)) && app(s, "rip") in bits(64) && app(s, "flags") in x86_64_linux.Flags && app(s, "cpu") in x86_64_linux.Cpu && app(s, "fs_base") in bits(64) && app(s, "gs_base") in bits(64) && app(s, "vm") in x86_64_linux.Vm && app(s, "os") in x86_64_linux.Os by simp(expand(hM, x86_64_linux.Machine))
  have and_l0: s in powerset(cart(%(KEYS)s, univ(1))) by taut(mtyp)
  have tg: app(s, "gpr") in fn_space(x86_64_linux.Reg, bits(64)) by taut(mtyp)
  have tx: app(s, "xmm") in fn_space(x86_64_linux.Reg, bits(128)) by taut(mtyp)
  have hsv: app(s, "vm") in x86_64_linux.Vm by taut(mtyp)
  have tfl: app(s, "flags") in x86_64_linux.Flags by taut(mtyp)
  have r4: 4 in x86_64_linux.Reg by defs(simp(), x86_64_linux.Reg)
  have hsp := mp(mp(fn_space_app[a := x86_64_linux.Reg, b := bits(64), f := app(s, "gpr"), x := 4], tg), r4)
  have ok0 := mp(all_elim(all_elim(abi.ok_univ, {s}), {%(FINAL)s}), hp)
  have su: s in univ(1) by taut(ok0)
  have finu: %(FINAL)s in univ(1) by taut(ok0)
  // the final flags: the havoc's choice (a Flags record)
  have e_fl: app(%(FINAL)s, "flags") = %(FL)s by simp()
  have fu := rewrite(e_fl, mp(app_univ[u := 1, f := %(FINAL)s, k := "flags"], finu))
  have pf0: %(PF0)s by taut(set_select_def[s := powerset(cart(%(FK)s, univ(1))), p := x0. %(PX)s, z := app(s, "flags")], expand(tfl, x86_64_linux.Flags))
  have cf0: is_fun(app(s, "flags")) by taut(pf0)
  have cd0: dom(app(s, "flags")) = %(FK)s by taut(pf0)
%(chain)s  have bz := eq_bool[a := %(R)s, b := 0]
  have bsf: bit(%(R)s, 31) in bool by defs(eq_bool[a := int_mod(int_div(%(R)s, pow2(31)), 2), b := 1], bit)
  have bpf: x86_64_linux.even_parity(bits_slice(%(R)s, 7, 0)) in bool by defs(eq_bool[a := int_mod(int_sum(0, 8, x0. ite(bit(bits_slice(%(R)s, 7, 0), x0), 1, 0)), 2), b := 0], x86_64_linux.even_parity)
  have bf: false in bool by defs(simp(), bool)
  have baf: af in bool by defs(simp(haf), bool)
%(fields)s  have pfl: %(PFL)s by taut(cf6, cd6, fb_cf, fb_pf, fb_af, fb_zf, fb_sf, fb_df, fb_of)
  have tf: %(FL)s in x86_64_linux.Flags by defs(mp(mp(mp(mp(rec_type_intro[u := 1, k := %(FK)s, p := x0. %(PX)s, r := %(FL)s], fu), cf6), cd6), pfl), x86_64_linux.Flags)
  // false is a value (df at entry)
  have dfu := mp(app_univ[u := 1, f := app(s, "flags"), k := "df"], mp(app_univ[u := 1, f := s, k := "flags"], su))
  have ndf: !app(app(s, "flags"), "df") by simp(expand(he, abi.entry_ok))
  have dff := mp(mp(not_eq_false[a := app(app(s, "flags"), "df")], b_df), ndf)
  have fbu := rewrite(dff, dfu)
  // the memory after the store: the view, and the memory written back
  have e_vm: app(%(FINAL)s, "vm") = %(VM1)s by simp()
  have hvu := rewrite(e_vm, mp(app_univ[u := 1, f := %(FINAL)s, k := "vm"], finu))
  have hv := mp(mp(all_elim(all_elim(all_elim(all_elim(x86.store_vm, {app(s, "vm")}), {bits_add(64, app(app(s, "gpr"), 4), 18446744073709551608)}), {8}), {app(app(s, "gpr"), 7)}), hsv), hvu)
  have spg: abi.stack_page(app(s, "vm"), int_div(app(app(s, "gpr"), 4), 4096)) by simp(expand(he, abi.entry_ok), keep(abi.stack_page))
  have m16: int_mod(bits_add(64, app(app(s, "gpr"), 4), 8), 16) = 0 by simp(expand(he, abi.entry_ok))
  have wsp: x86_64_linux.can_access(app(s, "vm"), app(app(s, "gpr"), 4), 1) by simp(expand(he, abi.entry_ok), keep(x86_64_linux.can_access))
  have mp0: int_lt(int_div(app(app(s, "gpr"), 4), 4096), 34359738367) by simp(expand(expand(expand(wsp, x86_64_linux.can_access), x86_64_linux.mapped), x86_64_linux.page_of, x86_64_linux.TASK_SIZE, x86_64_linux.PAGE))
  have lt47: int_lt(app(app(s, "gpr"), 4), 140737488355328) by simp(hsp, mp0)
  have sv := mp(mp(mp(mp(mp(all_elim(all_elim(all_elim(gsi.store_view, {app(s, "vm")}), {app(app(s, "gpr"), 4)}), {app(app(s, "gpr"), 7)}), hsv), hsp), spg), m16), lt47)
  have hsv1: abi.scratch_view(%(VM1)s, app(s, "vm"), %(SP)s) by taut(sv)
  have hm1: abi.world_matches(app(s, "vm"), app(s, "vm"), %(VM1)s, %(SP)s) by taut(sv)
  have hnm: abi.world_matches(app(s, "vm"), %(VM1)s, app(%(IN1)s, "vm"), %(SP)s) by defs(simp(keep(abi.scratch, abi.scratch_page, abi.stack_page)), abi.world_matches)
  // the argument p is rdi
  have ac: all x0. x0 in omega -> int_lt(x0, seq_len(args)) -> app(app(s, "gpr"), app(abi.ARG_REGS, x0)) = app(args, x0) by taut(expand(he, abi.entry_ok))
  have z0: 0 in omega by simp()
  have a0 := mp(mp(all_elim(ac, {0}), z0), hl)
  have ar0 := at({app(%(L)s, 0)})
  have pa: app(app(s, "gpr"), 7) = app(args, 0) by simp(expand(a0, abi.ARG_REGS), ar0)
  have r7: 7 in x86_64_linux.Reg by defs(simp(), x86_64_linux.Reg)
  have hdi := mp(mp(fn_space_app[a := x86_64_linux.Reg, b := bits(64), f := app(s, "gpr"), x := 7], tg), r7)
  have r2: 2 in x86_64_linux.Reg by defs(simp(), x86_64_linux.Reg)
  have h1 := mp(mp(fn_space_app[a := x86_64_linux.Reg, b := bits(64), f := app(s, "gpr"), x := 2], tg), r2)
  // the spec's run on its world
  have c1: int_le(3, %(P)s) by taut(hc)
  have c2: !(int_sub(%(P)s, 3) = 0) by taut(hc)
  have c3: gimple.usable(app(%(IN1)s, "vm"), int_sub(%(P)s, 3), 1, false) by simp(hc)
  have stu: %(SL)s in univ(1) by simp(mp(app_univ[u := 1, f := %(VM1)s, k := "bytes"], hvu))
  have hw2: %(IN1)s in univ(1) by simp(su, stu, keep(x86_64_linux.store_le))
  have hspec := %(hspec)s
  have h0: %(R0)s in bits(64) by simp()
  have gu := mp(app_univ[u := 1, f := s, k := "gpr"], su)
  have xu := mp(app_univ[u := 1, f := s, k := "xmm"], su)
  // abi_function's normal return, and its state: the machine's
  have rt := %(rt)s
  have kf := mp(pow_cart_fst[a := %(KEYS)s, b := univ(1), f := s], and_l0)
  have rs0 := mp(restrict_all[f := s, d := %(KEYS)s], kf)
  have gs0 := mp(ghost_part_none[f := s, d := %(KEYS)s], kf)
  have req: %(R0)s = %(R)s by defs(simp(pa, hdi, c1), gimple.bytes_at, x86_64_linux.le)
  have sfd: is_fun(s) && dom(s) = %(KEYS)s by taut(mtyp)
  have gfd: is_fun(app(s, "gpr")) && dom(app(s, "gpr")) = x86_64_linux.Reg by simp(expand(tg, fn_space))
  have neq: %(N)s = %(FINAL)s by simp(rs0, gs0, req, dff, sfd, gfd, cf0, cd0, expand(gfd, x86_64_linux.Reg), keep(x86_64_linux.store_le))
  show := rewrite(neq, rt)
qed''' % V)

print('''
// undefined behavior: the spec raises from the world the ABI shows (with
// the stack slot as the machine will have written it)
theorem gsi.ub: all f args s o. s in x86_64_linux.Machine -> args in %(ARGS)s -> abi.entry_ok(s, args) ->
  !(%(COND)s) -> pair(s, o) in univ(1) -> ((ex m1 e. o = ok(m1, e)) || (ex m1 e. o = exc(m1, e)) || (ex t. o = diverge(t))) ->
  runs(abi.abi_function(single(empty), f, %(SPEC)s, args), s, o)
proof
  fix f
  fix args
  fix s
  fix o
  assume hM: s in x86_64_linux.Machine
  assume hA: args in %(ARGS)s
  assume he: abi.entry_ok(s, args)
  assume hnc: !(%(COND)s)
  assume hp: pair(s, o) in univ(1)
  assume ho: (ex m1 e. o = ok(m1, e)) || (ex m1 e. o = exc(m1, e)) || (ex t. o = diverge(t))
  have su: s in univ(1) by simp(hp)
  have mtyp: s in powerset(cart(%(KEYS)s, univ(1))) && is_fun(s) && dom(s) = %(KEYS)s && app(s, "gpr") in fn_space(x86_64_linux.Reg, bits(64)) && app(s, "vm") in x86_64_linux.Vm by simp(expand(hM, x86_64_linux.Machine))
  have and_l0: s in powerset(cart(%(KEYS)s, univ(1))) by taut(mtyp)
  have tg: app(s, "gpr") in fn_space(x86_64_linux.Reg, bits(64)) by taut(mtyp)
  have hsv: app(s, "vm") in x86_64_linux.Vm by taut(mtyp)
  have r4: 4 in x86_64_linux.Reg by defs(simp(), x86_64_linux.Reg)
  have hsp := mp(mp(fn_space_app[a := x86_64_linux.Reg, b := bits(64), f := app(s, "gpr"), x := 4], tg), r4)
  have bt: app(app(s, "vm"), "bytes") in fn_space(bits(64), bits(8)) by simp(expand(hsv, x86_64_linux.Vm))
  have stt := mp(all_elim(all_elim(all_elim(all_elim(x86.store_typed, {app(app(s, "vm"), "bytes")}), {bits_add(64, app(app(s, "gpr"), 4), 18446744073709551608)}), {8}), {app(app(s, "gpr"), 7)}), bt)
  have stu := mp(mp(mp(fn_space_univ[u := 1, a := bits(64), b := bits(8), f := %(SL)s], bits_univ[n := 64]), bits_univ[n := 8]), stt)
  have hvu: %(VM1)s in univ(1) by simp(su, stu, keep(x86_64_linux.store_le))
  have hv := mp(mp(all_elim(all_elim(all_elim(all_elim(x86.store_vm, {app(s, "vm")}), {bits_add(64, app(app(s, "gpr"), 4), 18446744073709551608)}), {8}), {app(app(s, "gpr"), 7)}), hsv), hvu)
  have spg: abi.stack_page(app(s, "vm"), int_div(app(app(s, "gpr"), 4), 4096)) by simp(expand(he, abi.entry_ok), keep(abi.stack_page))
  have m16: int_mod(bits_add(64, app(app(s, "gpr"), 4), 8), 16) = 0 by simp(expand(he, abi.entry_ok))
  have wsp: x86_64_linux.can_access(app(s, "vm"), app(app(s, "gpr"), 4), 1) by simp(expand(he, abi.entry_ok), keep(x86_64_linux.can_access))
  have mp0: int_lt(int_div(app(app(s, "gpr"), 4), 4096), 34359738367) by simp(expand(expand(expand(wsp, x86_64_linux.can_access), x86_64_linux.mapped), x86_64_linux.page_of, x86_64_linux.TASK_SIZE, x86_64_linux.PAGE))
  have lt47: int_lt(app(app(s, "gpr"), 4), 140737488355328) by simp(hsp, mp0)
  have sv := mp(mp(mp(mp(mp(all_elim(all_elim(all_elim(gsi.store_view, {app(s, "vm")}), {app(app(s, "gpr"), 4)}), {app(app(s, "gpr"), 7)}), hsv), hsp), spg), m16), lt47)
  have hsv1: abi.scratch_view(%(VM1)s, app(s, "vm"), %(SP)s) by taut(sv)
  have hm1: abi.world_matches(app(s, "vm"), app(s, "vm"), %(VM1)s, %(SP)s) by taut(sv)
  // the world is a World, and the spec raises from it
  have spb: %(SP)s in bits(64) by simp(hsp)
  have w0u: %(W0)s in univ(1) by simp(su, hvu, stu, keep(x86_64_linux.store_le))
  have wt := mp(mp(mp(mp(all_elim(all_elim(all_elim(abi.world_typed, {s}), {%(VM1)s}), {%(SP)s}), hM), hv), spb), w0u)
  have kf := mp(pow_cart_fst[a := %(KEYS)s, b := univ(1), f := s], and_l0)
  have gs0 := mp(ghost_part_none[f := s, d := %(KEYS)s], kf)
  have gi: ghost_part(s, %(KEYS)s) in single(empty) by simp(gs0)
  have ra: %(IN0)s in rec_and(abi.World, single(empty)) by defs(mp(mp(rec_and_intro[a := abi.World, b := single(empty), x := %(W0)s, y := ghost_part(s, %(KEYS)s)], wt), gi), rec_merge)
  have eu: empty in univ(1) by simp()
  have in0u: %(IN0)s in univ(1) by simp(su, stu, w0u, mp(ghost_part_univ[u := 1, f := s, d := %(KEYS)s], su), keep(x86_64_linux.store_le))
  have nc0: !(%(COND0)s) by simp(hnc)
  have fr := mp(mp(mp(mp(all_elim(all_elim(all_elim(gsi.fun_raises, {%(IN0)s}), {args}), {empty}), in0u), eu), hA), nc0)
  have hra := mp(mp(mp(all_elim(all_elim(all_elim(all_elim(abi.raises_intro, {%(IN0)s}), {%(SPEC)s}), {args}), {empty}), ra), eu), fr)
  show := %(ub)s
qed''' % V)

print('''
// a run of get_slot_index from its entry is one abi_function allows
theorem gsi.machine: all args s o. args in %(ARGS)s -> s in x86_64_linux.Machine -> abi.code_at(app(s, "vm"), 4202755, %(CODE)s) -> runs(abi.run_to_return(), s, o) ->
  runs(abi.abi_function(single(empty), 4202755, %(SPEC)s, args), s, o)
proof
  fix args
  fix s
  fix o
  assume hA: args in %(ARGS)s
  assume hM: s in x86_64_linux.Machine
  assume hc: abi.code_at(app(s, "vm"), 4202755, %(CODE)s)
  assume hr: runs(abi.run_to_return(), s, o)
  have hp := mp(all_elim(all_elim(abi.run_univ, {s}), {o}), hr)
  have hsh := mp(all_elim(all_elim(abi.run_shape, {s}), {o}), hr)
  have ho: (ex m1 e. o = ok(m1, e)) || (ex m1 e. o = exc(m1, e)) || (ex t. o = diverge(t)) by simp(hsh)
  have pre: !(app(s, "rip") = 4202755 && abi.entry_ok(s, args)) -> runs(abi.abi_function(single(empty), 4202755, %(SPEC)s, args), s, o) proof
    assume hn: !(app(s, "rip") = 4202755 && abi.entry_ok(s, args))
    show by simp(hp, hn, keep(abi.entry_ok, abi.world.get, abi.world.set, abi.abi_call, abi.abi_restore, abi.abi_set_result, abi.spec_raises, abi.scratch, abi.crash_io_ok))
  qed
  have en_case: app(s, "rip") = 4202755 && abi.entry_ok(s, args) -> runs(abi.abi_function(single(empty), 4202755, %(SPEC)s, args), s, o) proof
    assume hy: app(s, "rip") = 4202755 && abi.entry_ok(s, args)
    have hrip: app(s, "rip") = 4202755 by taut(hy)
    have he: abi.entry_ok(s, args) by taut(hy)
    have ub_case: !(%(COND)s) -> runs(abi.abi_function(single(empty), 4202755, %(SPEC)s, args), s, o) proof
      assume hnc: !(%(COND)s)
      show := mp(mp(mp(mp(mp(mp(all_elim(all_elim(all_elim(all_elim(gsi.ub, {4202755}), {args}), {s}), {o}), hM), hA), he), hnc), hp), ho)
    qed
    have ok_case: %(COND)s -> runs(abi.abi_function(single(empty), 4202755, %(SPEC)s, args), s, o) proof
      assume hcd: %(COND)s
      have c1: int_le(3, %(P)s) by taut(hcd)
      have lt: args in list_type(bits(64)) by simp(hA)
      have ae := all_elim(abi.args_empty, {args})
      have nz: app(args, 0) = empty -> false proof
        assume e0: app(args, 0) = empty
        have c1e := rewrite(e0, c1)
        show by simp(c1e)
      qed
      have hl: int_lt(0, seq_len(args)) by taut(ae, lt, nz)
      have mtyp: app(s, "gpr") in fn_space(x86_64_linux.Reg, bits(64)) by simp(expand(hM, x86_64_linux.Machine))
      have r4: 4 in x86_64_linux.Reg by defs(simp(), x86_64_linux.Reg)
      have r7: 7 in x86_64_linux.Reg by defs(simp(), x86_64_linux.Reg)
      have hsp := mp(mp(fn_space_app[a := x86_64_linux.Reg, b := bits(64), f := app(s, "gpr"), x := 4], mtyp), r4)
      have hdi := mp(mp(fn_space_app[a := x86_64_linux.Reg, b := bits(64), f := app(s, "gpr"), x := 7], mtyp), r7)
      have wsp: x86_64_linux.can_access(app(s, "vm"), app(app(s, "gpr"), 4), 1) by simp(expand(he, abi.entry_ok), keep(x86_64_linux.can_access))
      have m16: int_mod(bits_add(64, app(app(s, "gpr"), 4), 8), 16) = 0 by simp(expand(he, abi.entry_ok))
      have sa := mp(mp(mp(all_elim(all_elim(gsi.stack_access, {app(s, "vm")}), {app(app(s, "gpr"), 4)}), hsp), wsp), m16)
      have a1: %(A1)s by taut(sa)
      have a2: %(A2)s by taut(sa)
      have a7: %(A7)s by taut(sa)
      have ac: all x0. x0 in omega -> int_lt(x0, seq_len(args)) -> app(app(s, "gpr"), app(abi.ARG_REGS, x0)) = app(args, x0) by taut(expand(he, abi.entry_ok))
      have z0: 0 in omega by simp()
      have a0 := mp(mp(all_elim(ac, {0}), z0), hl)
      have ar0 := at({app(%(L)s, 0)})
      have pa: app(app(s, "gpr"), 7) = app(args, 0) by simp(expand(a0, abi.ARG_REGS), ar0)
      have us: gimple.usable(%(VM1)s, int_sub(%(P)s, 3), 1, false) by taut(hcd)
      have lt01: int_lt(0, 1) by simp()
      have u0 := mp(mp(all_elim(expand(us, gimple.usable), {0}), z0), lt01)
      have a4: %(A4)s proof
        fix i
        assume i1: i in omega
        assume i2: int_lt(i, 1)
        have i0: i = 0 by simp(i1, i2)
        have ea: bits_add(64, bits_add(64, app(app(s, "gpr"), 7), 18446744073709551613), bits_of_int(64, i)) = int_sub(%(P)s, 3) by simp(i0, pa, hdi, c1)
        show by defs(simp(u0, ea), x86_64_linux.can_access, x86_64_linux.page_of, x86_64_linux.hw_allows, x86_64_linux.accessible)
      qed
      have run := mp(mp(mp(mp(mp(mp(mp(mp(mp(get_slot_index.run[m := s, o := o], hc), hrip), hsp), hdi), a1), a2), a4), a7), hr)
      obtain af, haf from run
      have eo: o = ok(%(FINAL)s, empty) by taut(haf)
      have hafb: af = false || af = true by taut(haf)
      have hp2 := rewrite(eo, hp)
      have nm := mp(mp(mp(mp(mp(mp(mp(all_elim(all_elim(all_elim(all_elim(gsi.normal, {4202755}), {args}), {s}), {af}), hM), hA), he), hl), hcd), hafb), hp2)
      show := rewrite(sym(eo), nm)
    qed
    show by taut(ub_case, ok_case)
  qed
  show by taut(pre, en_case)
qed''' % V)

print('''
// get_slot_index's machine code (at -O0) implements its readable GIMPLE,
// under the ABI: C1 for this function
theorem gsi.implements: abi.implements2_at(single(empty), 4202755, %(SPEC)s, 4202755, %(CODE)s)
proof
  have main: all x0. x0 in %(ARGS)s -> (all s h o. s in x86_64_linux.Machine -> h in single(empty) -> runs(abi.run_to_return(), s, o) -> (ex h2. h2 in single(empty) && runs(mkprog(x1 x2. !abi.code_at(app(x1, "vm"), 4202755, %(CODE)s) || bind_rel(abi.abi_function(single(empty), 4202755, %(SPEC)s, x0), x1, x3 x4. x2 = ok(x3, empty), x3 x4. x2 = exc(x3, x4), x3. x2 = diverge(x3))), union2(s, h), with_ghost(o, h2)))) proof
    fix args
    assume hA: args in %(ARGS)s
    show all s h o. s in x86_64_linux.Machine -> h in single(empty) -> runs(abi.run_to_return(), s, o) -> (ex h2. h2 in single(empty) && runs(mkprog(x1 x2. !abi.code_at(app(x1, "vm"), 4202755, %(CODE)s) || bind_rel(abi.abi_function(single(empty), 4202755, %(SPEC)s, args), x1, x3 x4. x2 = ok(x3, empty), x3 x4. x2 = exc(x3, x4), x3. x2 = diverge(x3))), union2(s, h), with_ghost(o, h2))) proof
      fix s
      fix h
      fix o
      assume hM: s in x86_64_linux.Machine
      assume hh: h in single(empty)
      assume hr: runs(abi.run_to_return(), s, o)
      have hp := mp(all_elim(all_elim(abi.run_univ, {s}), {o}), hr)
      have hsh := mp(all_elim(all_elim(abi.run_shape, {s}), {o}), hr)
      have mc: abi.code_at(app(s, "vm"), 4202755, %(CODE)s) -> runs(abi.abi_function(single(empty), 4202755, %(SPEC)s, args), s, o) proof
        assume hc: abi.code_at(app(s, "vm"), 4202755, %(CODE)s)
        show := mp(mp(mp(mp(all_elim(all_elim(all_elim(gsi.machine, {args}), {s}), {o}), hA), hM), hc), hr)
      qed
      have mc2: !abi.code_at(app(s, "vm"), 4202755, %(CODE)s) || runs(abi.abi_function(single(empty), 4202755, %(SPEC)s, args), s, o) by taut(mc)
      show by defs(ex_intro({empty}, simp(hh, hp, hsh, mc2, keep(abi.abi_function, abi.code_at, abi.run_to_return))), with_ghost)
    qed
  qed
  show by defs(main, abi.implements2_at, refines_ghost)
qed''' % V)
