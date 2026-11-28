#!/usr/bin/env python3
"""Rows "Table 2: for the monotone six-input f with table A * 2^32 + B: each AND/OR/NOT circuit of fan-in at most
two has an AND/OR one no larger", for the larger functions (monotone size 11 to 13) by the table engine.

The proof text is that of the merged L_meta_39269 (Ming-Chih Kao, same repository, Apache-2.0; its header names its
sources: the search engine of L_meta_1673 by Trey Kind and the NOT-aware root of L-meta-15028 by edmoreno).  Its
search runs inside Lean.  Only the data of the function changes; this program computes that data:

  rows       64 true inputs outside the pairs; then the pairs (x true, y false) grouped by x; then grouped by y
  pairs      (least true point, greatest false point), (least true point, all-zero input), and every
             (x true, x with one input switched off false)
  tables     AND/OR circuit sizes of the function with one, two or three inputs fixed to false
  witness    an AND/OR circuit of the least size found (m gates); the root bound is m - 1

  python3 gen6t.py <step id> <statement file> <out.lean> [seed]
Exit 0: file written (it still has to compile: the bounds are checked by Lean).  Exit 1: the method does not apply."""
import itertools, json, os, random, re, subprocess, sys, time
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(HERE, '..', 'encoder'))
import gen6, msynth
N = 6
TEMPLATE_ID = 'L_meta_39269'
T_OLD = '4277074632 * 2 ^ 32 + 4276805824'

def template():
    return subprocess.run(['git', '-C', '/home/user/pequalnp-proofs', 'show', f'upstream/main:lean/PEqualNP/Outside/{TEMPLATE_ID}.lean'],
                          capture_output=True, text=True, check=True).stdout

def restrict(T, Z):
    """The function with the inputs of Z fixed to false, as a predicate on all 64 inputs (it ignores Z)."""
    zm = sum(1 << v for v in Z)
    return lambda x: T >> (x & ~zm) & 1

def least(g, vs, lo, hi, secs):
    """Least k in lo..hi with an AND/OR circuit for g on the inputs vs: (k, gates, output wire, sure).  A size
    whose search times out is passed over and `sure` becomes False (the size found may then not be the least).
    Rows: the least true points and the greatest false points of g (enough for a monotone circuit)."""
    vs = sorted(vs); n = len(vs)
    pts = [sum(1 << vs[i] for i in range(n) if r >> i & 1) for r in range(1 << n)]
    tr = [r for r in range(1 << n) if g(pts[r])]
    if not tr: return 0, [], None, True                       # constant false
    if len(tr) == 1 << n: return 0, [], None, True            # constant true
    mint = [r for r in tr if all(not g(pts[r ^ (1 << j)]) for j in range(n) if r >> j & 1)]
    if len(mint) == 1 and bin(mint[0]).count('1') == 1: return 0, [], None, True     # one input itself
    maxf = [r for r in range(1 << n) if not g(pts[r]) and all(g(pts[r | (1 << j)]) for j in range(n) if not r >> j & 1)]
    rows = mint + maxf; R = len(rows)
    incols = [sum(1 << j for j, r in enumerate(rows) if r >> i & 1) for i in range(n)]
    target = sum(1 << j for j, r in enumerate(rows) if g(pts[r]))
    sure = True
    for k in range(max(1, lo), hi + 1):
        res = msynth.search(n, incols, R, [target], k, 'andor', secs(k) if callable(secs) else secs, 0)
        if isinstance(res, tuple):
            gates, outw = res[0], res[1][0]
            def ev(r):
                w = [bool(r >> i & 1) for i in range(n)]
                for op, a, b in gates: w.append((w[a] and w[b]) if op == 'and' else (w[a] or w[b]))
                return w[outw]
            assert all(ev(r) == bool(g(pts[r])) for r in range(1 << n))
            return k, gates, outw, sure
        if res is not None: sure = False
    return None, None, None, False

def big(v):
    words = []
    while True:
        words.append(v & (2 ** 64 - 1)); v >>= 64
        if v == 0: break
    words.reverse(); e = hex(words[0])
    for w in words[1:]: e = f'Nat.lor (Nat.shiftLeft ({e}) 64) {hex(w)}'
    return e

def build(step, stmt, seed=1, log=print, max_m=13, min_m=0):
    p = gen6.parse(stmt)
    if not p: return None
    expr, T = p; expr = expr[1:-1]
    f = lambda x: T >> x & 1
    V = list(range(N))
    for j in V:
        if all(f(x) == f(x ^ (1 << j)) for x in range(64)): log(f'the function ignores input {j}: not this method'); return None
    if any(f(x) and not f(x | (1 << j)) for x in range(64) for j in V): log('not monotone'); return None
    tr = [x for x in range(64) if f(x)]
    mint = [x for x in tr if all(not f(x ^ (1 << j)) for j in V if x >> j & 1)]
    maxf = [x for x in range(64) if not f(x) and all(f(x | (1 << j)) for j in V if not x >> j & 1)]
    pairs = set((x, y) for x in mint for y in maxf) | set((x, 0) for x in mint)
    pairs |= set((x, x ^ (1 << v)) for x in tr for v in V if x >> v & 1 and not f(x ^ (1 << v)))
    xs = sorted(set(x for x, _ in pairs)); ys = sorted(set(y for _, y in pairs))
    free = [x for x in tr if x not in set(xs)]
    if not free: log('no true input outside the pairs: not this method'); return None
    rnd = random.Random(seed)
    fp = (sorted(free) * 64)[:64] if len(free) >= 64 else sorted(free) + [rnd.choice(free) for _ in range(64 - len(free))]
    rows = [(x, 0, 'f') for x in fp]; segsX = []; segsY = []
    for x in xs:
        s = len(rows) - 1 if not segsX else segsX[-1][1]
        for y in ys:
            if (x, y) in pairs: rows.append((x, y, 'p'))
        rows.append((0, 0, 'h')); segsX.append((s, len(rows) - 1))
    for y in ys:
        s = segsX[-1][1] if not segsY else segsY[-1][1]
        for x in xs:
            if (x, y) in pairs: rows.append((x, y, 'p'))
        rows.append((0, 0, 'h')); segsY.append((s, len(rows) - 1))
    NN = len(rows)
    AA = sum(1 << i for i, r in enumerate(rows) if r[2] == 'p')
    HX = sum(1 << e for _, e in segsX); HY = sum(1 << e for _, e in segsY)
    raw = [sum(((r[0] >> v & 1) << i) | ((r[1] >> v & 1) << (NN + i)) for i, r in enumerate(rows)) for v in V]
    TG = sum(1 << i for i, r in enumerate(rows) if r[2] != 'h' and f(r[0]))
    # tables: AND/OR sizes of the function with three, two, one inputs fixed to false (exact: every smaller size is
    # refuted by the SAT search, which is quick at these sizes)
    size = {}; t0 = time.time(); unsure = []
    def depends(Z, v):
        g = restrict(T, Z); return any(g(x) != g(x ^ (1 << v)) for x in range(64))
    def lower(Z):
        return max([size[tuple(sorted(Z + (v,)))] + (1 if depends(Z, v) else 0) for v in V if v not in Z] + [0])
    for d in (3, 2, 1):
        for Z in itertools.combinations(V, d):
            k, _, _, sure = least(restrict(T, Z), [v for v in V if v not in Z], lower(Z) if d < 3 else 1, 12, 120)
            if k is None: log('no circuit found for the function with inputs', Z, 'off'); return None
            size[Z] = k
            if not sure: unsure.append(Z)
    lo = max(lower(()), min_m)      # min_m: the caller already looked for smaller circuits and found none in its time
    m, gates, outw, sure = least(f, V, lo, max_m, lambda k: 45 if k < 12 else 70)
    if m is None: log(f'no circuit of at most {max_m} gates found for the function'); return None
    L = m - 1
    if L < 6: log('fewer than 7 gates: not this method'); return None
    log(f'sizes: the function {m}; one input off {[size[(v,)] for v in V]}; searches took {time.time() - t0:.0f} s; rows {NN}'
        + ('' if sure and not unsure else ' (some smaller size was not refuted in the time)'))
    def tab(d):
        # as in the template: an entry is listed when its size is at least 1 and larger than the size with any
        # further input off (otherwise the deeper entry already gives the bound)
        def deeper(Z): return max([size[tuple(sorted(Z + (v,)))] for v in V if v not in Z] + [0]) if d < 3 else 0
        ent = [(sum(1 << v for v in Z), size[Z]) for Z in itertools.combinations(V, d) if size[Z] >= 1 and size[Z] > deeper(Z)]
        return '[' + ', '.join(f'({a}, {b})' for a, b in sorted(ent)) + ']'
    t = template()
    assert T_OLD in t; t = t.replace(T_OLD, expr)        # the table, wherever the template names it
    def sub_line(prefix, new, count=1):
        nonlocal t
        lines = t.split('\n'); n = 0
        for i, l in enumerate(lines):
            if l.startswith(prefix): lines[i] = new; n += 1
        assert n == count, (prefix, n)
        t = '\n'.join(lines)
    vals = [AA, HX, HY] + raw + [TG]
    for k, v in enumerate(vals): sub_line(f'def bigNat_{k} : Nat := ', f'def bigNat_{k} : Nat := {big(v)}')
    sub_line('def NN : Nat := ', f'def NN : Nat := {NN}')
    fmt = lambda S: '[' + ', '.join(f'({a}, {b})' for a, b in S) + ']'
    sub_line('def segsX : List (ℕ × ℕ) := ', 'def segsX : List (ℕ × ℕ) := ' + fmt(segsX))
    sub_line('def segsY : List (ℕ × ℕ) := ', 'def segsY : List (ℕ × ℕ) := ' + fmt(segsY))
    for d in (1, 2, 3): sub_line(f'def rt{d} : List (ℕ × ℕ) := ', f'def rt{d} : List (ℕ × ℕ) := ' + tab(d))
    # the root block (the template's, with its bound 11 replaced by L)
    i0 = t.index('theorem root_0 : chk [] rt 0 '); i0 = t.rfind('set_option maxRecDepth', 0, t.rfind('set_option maxHeartbeats', 0, i0))
    i1 = t.index('open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity\nsection circuit')
    old = t[i0:i1]
    j0 = old.index('set_option maxRecDepth 100000 in\nset_option maxHeartbeats 0 in\ntheorem proot_1_0 : '); j1 = old.index('set_option maxRecDepth 100000 in\nset_option maxHeartbeats 0 in\ntheorem proot_2 : ')
    p1 = old[j0:j1]
    assert p1.count('chk [] rt 0 11 1 ') == 10, p1.count('chk [] rt 0 11 1 ')
    p1 = p1.replace('chk [] rt 0 11 1 ', f'chk [] rt 0 {L} 1 ')
    so = 'set_option maxRecDepth 100000 in\nset_option maxHeartbeats 0 in\n'
    blk = ''
    for q in range(4): blk += so + f'theorem root_{q} : chk [] rt 0 {L - 1} {q} FF 1 = false := by decide +kernel\n'
    hi = list(range(4, L))
    blk += so + f'theorem root_hi : okT [] rt 0 {L} {hi} = true := by decide +kernel\n'
    blk += f'lemma iroot : Imp [] 0 {L} := imp_ts (Or.inl rfl) root_p (by norm_num) ir (fun t ht => by\n  have h := root_hi\n'
    blk += '  simp only [okT, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, Bool.not_eq_true\'] at h\n'
    blk += '  obtain ⟨' + ', '.join(f'h{q}' for q in hi) + '⟩ := h\n  interval_cases t\n'
    blk += '\n'.join([f'  · exact one root_{q}' for q in range(4)] + [f'  · exact one h{q}' for q in hi]) + ')\n'
    blk += p1
    for q in (2, 3, 4): blk += so + f'theorem proot_{q} : chk [] rt 0 {L} {q} FF 1 = false := by decide +kernel\n'
    hi2 = list(range(5, L + 1))
    blk += so + f'theorem proot_hi : okT [] rt 0 {L + 1} {hi2} = true := by decide +kernel\n'
    blk += 'lemma iroot_pos {t : ℕ} {S : Finset ℕ} (ht1 : 1 ≤ t) (hS : (S : Set ℕ) ⊆ C (mz 0) (WZ [] 0))\n'
    blk += f'    (hl : Live Z0 (mz 0) (tz 0) {L} t S) : False := by\n'
    blk += f'  have hmin : ∀ q < {L}, ¬ Sol Z0 (mz 0) (tz 0) q (C (mz 0) (WZ [] 0)) := fun q hq => iroot q hq\n'
    blk += f'  have hm0 : Min Z0 (mz 0) (tz 0) {L} t S := ⟨hl, fun q hq hs => hmin q hq (hs.mono le_rfl (by rintro x (hx | hx); exact hS hx; exact Or.inr hx))⟩\n'
    blk += f'  have htk : t < {L + 1} := by have := hm0.size.2; omega\n'
    blk += f'  have hM : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk [] rt 0 {L} t p.1 p.2 = false := by\n    have h := proot_hi\n'
    blk += '    simp only [okT, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, Bool.not_eq_true\'] at h\n'
    blk += '    obtain ⟨' + ', '.join(f'h{q}' for q in hi2) + '⟩ := h\n    interval_cases t\n'
    blk += '\n'.join(['    · exact pex_1'] + [f'    · exact one proot_{q}' for q in (2, 3, 4)] + [f'    · exact one h{q}' for q in hi2]) + '\n'
    blk += f'  exact imp_of_live (L := {L + 1}) (Or.inl rfl) root_p (by norm_num) ir (by omega) hS hl hmin (Or.inr hM)\n'
    t = t[:i0] + blk + t[i1:]
    # the function as an OR of its least true points, and the same over the rows
    term = lambda x: '(' + ' && '.join(f'x {v}' for v in V if x >> v & 1) + ')'
    fx = ' || '.join(term(x) for x in mint)
    def eterm(x):
        vs = [v for v in V if x >> v & 1]; e = f'rawP.getD {vs[0]} 0'
        for v in vs[1:]: e = f'({e} &&& rawP.getD {v} 0)'
        return e if len(vs) == 1 else e
    ef = None
    for x in mint:
        e = eterm(x); e = e if e.startswith('(') else e
        ef = (e if e.startswith('(') or len(mint) == 1 else e) if ef is None else f'({ef} ||| {e})'
    if any(bin(x).count('1') == 1 for x in mint): log('a least true point with one input: not this method'); return None
    sub_line('def f (x : Fin 6 → Bool) : Bool := ', f'def f (x : Fin 6 → Bool) : Bool := {fx}')
    sub_line('def EF : ℕ := ', f'def EF : ℕ := {ef}')
    gl = ', '.join(f'⟨.{op}, [{a}, {b}]⟩' for op, a, b in gates)
    i0 = t.index('def witness : Circuit :=\n'); i1 = t.index('\n', i0 + len('def witness : Circuit :=\n'))
    t = t[:i0] + f'def witness : Circuit :=\n  ⟨[{gl}], {outw}⟩' + t[i1:]
    sub_line('  have hws : witness.size = ', f'  have hws : witness.size = {m} := rfl')
    sub_line('  · have hge : ', f'  · have hge : {m} ≤ gates.length := by')
    sub_line('      by_cases hlt2 : gates.length < ', f'      by_cases hlt2 : gates.length < {L}')
    sub_line('      · have heq : gates.length = ', f'      · have heq : gates.length = {L} := by omega')
    i0 = t.index(f'theorem PEqualNP.Outside.{TEMPLATE_ID} : '); i1 = t.index(f' := by\n  exact PEqualNP.Outside.{TEMPLATE_ID}.solve', i0)
    t = t[:i0] + f'theorem PEqualNP.Outside.{TEMPLATE_ID} : ' + stmt + t[i1:]
    t = t.replace(TEMPLATE_ID, step.replace('-', '_'))
    note = ('-- The whole proof text is that of the merged ' + TEMPLATE_ID + ' (Ming-Chih Kao, same repository, Apache-2.0), whose header\n'
            '-- follows; only the data of this function (rows, tables of sub-bounds, bounds, witness) was computed anew.\n')
    t = t.replace('import PEqualNP.Defs\n', 'import PEqualNP.Defs\n\n' + note, 1)
    return t, dict(m=m, L=L, NN=NN, sure=bool(sure and not unsure), sizes={''.join(map(str, Z)): s for Z, s in size.items()})

if __name__ == '__main__':
    step, sf, out = sys.argv[1:4]; seed = int(sys.argv[4]) if len(sys.argv) > 4 else 1
    min_m = int(sys.argv[5]) if len(sys.argv) > 5 else 0; max_m = int(sys.argv[6]) if len(sys.argv) > 6 else 13
    r = build(step, open(sf).read().strip(), seed, min_m=min_m, max_m=max_m)
    if not r: sys.exit(1)
    open(out, 'w').write(r[0]); json.dump(r[1], open(out + '.json', 'w'))
    print('written:', {k: v for k, v in r[1].items() if k != 'sizes'}); sys.exit(0)
