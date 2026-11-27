#!/usr/bin/env python3
"""Rows "At fan-in two, one NOT gate saves nothing on edges ..." on eight vertices, dense graphs.

The proof text is that of the merged L_meta_28304 (same repository, Apache-2.0; its header names its own sources:
the search engine of L_meta_1673 and the NOT-aware root of L-meta-15028).  Its search runs inside Lean.  Only the
data of the graph changes; this program computes that data:

  rows       64 true inputs outside the pairs; then the pairs (x true, y false) grouped by x; then grouped by y
  pairs      (edge, maximal independent set), (edge, empty set), every (x true, x minus one vertex false)
  tables     AND/OR circuit sizes of the graph with one, two or three vertices deleted (lower bounds the file proves)
  witness    an AND/OR circuit of the least size found; the root bound is that size minus one

  python3 gen8k.py <step id> <statement file> <out.lean> [seconds per search]
Exit 0: file written (it still has to compile: the bounds are checked by Lean).  Exit 3: not such a row."""
import itertools, json, os, random, re, subprocess, sys, time
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'encoder'))
import msynth
TEMPLATE_ID = 'L_meta_28304'

def template():
    return subprocess.run(['git', '-C', '/home/user/pequalnp-proofs', 'show', f'upstream/main:lean/PEqualNP/Outside/{TEMPLATE_ID}.lean'],
                          capture_output=True, text=True, check=True).stdout

def parse(stmt):
    if stmt.startswith('¬'): return None
    m = re.search(r'∀ x : Fin 8 → Bool, PEqualNP\.CircuitLowerBounds\.Circuit\.eval ⟨gates, o⟩ \(List\.ofFn x\) = decide \(∃ i < \(\[([0-9, ]+)\] : List ℕ\)\.length / 2', stmt)
    if not m or 'gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not' not in stmt: return None
    v = [int(x) for x in m.group(1).split(',')]
    return [(v[2 * i], v[2 * i + 1]) for i in range(len(v) // 2)], m.group(1)

def fval(E, x): return any(x >> a & 1 and x >> b & 1 for a, b in E)

def mono(E, vs, lo, hi, secs, shaped=False):
    """Least k in lo..hi with an AND/OR circuit for the edge function on vs found within the time; (k, gates, out).
    A circuit of AND and OR gates is monotone, so it is right everywhere once it is right on the edges (the least
    true inputs) and on the maximal independent sets (the greatest false inputs): only those rows are given."""
    vs = sorted(vs); n = len(vs); idx = {v: i for i, v in enumerate(vs)}
    ed = [(idx[a], idx[b]) for a, b in E if a in idx and b in idx]
    if not ed: return 0, [], None
    f = lambda r: any(r >> a & 1 and r >> b & 1 for a, b in ed)
    rows = sorted(set((1 << a) | (1 << b) for a, b in ed)) + [r for r in range(1 << n) if not f(r) and all(f(r | 1 << v) for v in range(n) if not r >> v & 1)]
    R = len(rows); incols = [sum(1 << j for j, r in enumerate(rows) if r >> i & 1) for i in range(n)]
    target = sum(1 << j for j, r in enumerate(rows) if f(r))
    for k in range(max(1, lo), hi + 1):
        res = None
        if shaped:
            # the usual shape of a least circuit: p ORs of inputs, then q ANDs of those, then q - 1 ORs joining them
            for q in range(1, k // 2 + 2):
                pp = k - 2 * q + 1
                if pp < 0: break
                def extra(L, pp=pp, q=q):
                    cl = []; op, sa, sb = L['op'], L['sa'], L['sb']
                    for g in range(k):
                        isand = pp <= g < pp + q
                        cl.append([op[g]] if isand else [-op[g]])
                        for j in range(n + g):
                            if isand and j >= n + pp: cl += [[-sa[g][j]], [-sb[g][j]]]
                            if g >= pp + q and j < n + pp: cl += [[-sa[g][j]], [-sb[g][j]]]
                    return cl
                res = msynth.search(n, incols, R, [target], k, 'andor', secs, 0, extra)
                if isinstance(res, tuple): break
        else:
            res = msynth.search(n, incols, R, [target], k, 'andor', secs, 0)
        if isinstance(res, tuple):
            gates, outw = res[0], res[1][0]
            def ev(r):
                w = [bool(r >> i & 1) for i in range(n)]
                for op, a, b in gates: w.append((w[a] and w[b]) if op == 'and' else (w[a] or w[b]))
                return w[outw]
            assert all(ev(r) == f(r) for r in range(1 << n))
            return k, gates, outw
    return None, None, None

def big(v):
    words = []
    while True:
        words.append(v & (2 ** 64 - 1)); v >>= 64
        if v == 0: break
    words.reverse(); e = hex(words[0])
    for w in words[1:]: e = f'Nat.lor (Nat.shiftLeft ({e}) 64) {hex(w)}'
    return e

def build(step, stmt, secs=20.0, seed=1, log=print):
    p = parse(stmt)
    if not p: return None
    E, flat = p; V = list(range(8)); pc = lambda s: bin(s).count('1')
    true_pts = [s for s in range(256) if fval(E, s)]; indep = [s for s in range(256) if not fval(E, s)]
    mis = [s for s in indep if all(fval(E, s | 1 << v) for v in V if not s >> v & 1)]
    edges = sorted((1 << a) | (1 << b) for a, b in E)
    pairs = set((x, y) for x in edges for y in mis) | set((x, 0) for x in edges)
    pairs |= set((x, x ^ (1 << v)) for x in true_pts for v in V if x >> v & 1 and not fval(E, x ^ (1 << v)))
    xs = sorted(set(x for x, _ in pairs)); ys = sorted(set(y for _, y in pairs))
    free = [s for s in true_pts if s not in set(xs)]
    if len(free) < 64: log('fewer than 64 spare true inputs'); return None
    rnd = random.Random(seed); fp = rnd.sample(free, 64)
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
    TG = sum(1 << i for i, r in enumerate(rows) if r[2] != 'h' and fval(E, r[0]))
    # tables: AND/OR sizes of the graph minus one, two, three vertices
    size = {}
    def c(Z, lo):
        k, _, _ = mono(E, [v for v in V if v not in Z], lo, 15, secs if len(Z) < 3 else 60, shaped=len(Z) < 3)
        return k
    t0 = time.time()
    for Z in itertools.combinations(V, 3): size[Z] = c(Z, 1)
    def deg(v, Z): return sum(1 for a, b in E if (a == v and b not in Z) or (b == v and a not in Z))
    def lower(Z):
        # deleting a vertex that still has an edge removes at least one gate of an AND/OR circuit
        return max(size[tuple(sorted(Z + (v,)))] + (1 if deg(v, Z) else 0) for v in V if v not in Z)
    for d in (2, 1):
        for Z in itertools.combinations(V, d):
            size[Z] = c(Z, lower(Z))
            if size[Z] is None: log('no circuit found for the graph minus', Z); return None
    m, gates, outw = mono(E, V, lower(()), 16, max(secs, 40), shaped=True)
    if m is None: log('no circuit found for the whole graph'); return None
    log(f'sizes: whole graph {m}; minus one vertex {[size[(v,)] for v in V]}; searches took {time.time() - t0:.0f} s; rows {NN}')
    L = m - 1
    def tab(d):
        ent = [(sum(1 << v for v in Z), size[Z]) for Z in itertools.combinations(V, d) if size[Z] >= 1]
        return '[' + ', '.join(f'({a}, {b})' for a, b in sorted(ent)) + ']'
    t = template()
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
    # the root block
    i0 = t.index('theorem root_0 : chk [] rt 0 '); i0 = t.rfind('set_option maxRecDepth', 0, t.rfind('set_option maxHeartbeats', 0, i0))
    i1 = t.index('open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity\nsection circuit')
    so = 'set_option maxRecDepth 100000 in\nset_option maxHeartbeats 0 in\n'
    blk = ''
    for q in range(4): blk += so + f'theorem root_{q} : chk [] rt 0 {L - 1} {q} FF 1 = false := by decide +kernel\n'
    hi = list(range(4, L))
    blk += so + f'theorem root_hi : okT [] rt 0 {L} {hi} = true := by decide +kernel\n'
    blk += f'lemma iroot : Imp [] 0 {L} := imp_ts (Or.inl rfl) root_p (by norm_num) ir (fun t ht => by\n  have h := root_hi\n'
    blk += '  simp only [okT, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, Bool.not_eq_true\'] at h\n'
    blk += '  obtain ⟨' + ', '.join(f'h{q}' for q in hi) + '⟩ := h\n  interval_cases t\n'
    cases = [f'  · exact one root_{q}' for q in range(4)] + [f'  · exact one h{q}' for q in hi]
    blk += '\n'.join(cases) + ')\n'
    for q in (1, 2, 3): blk += so + f'theorem proot_{q} : chk [] rt 0 {L} {q} FF 1 = false := by decide +kernel\n'
    hi2 = list(range(4, L + 1))
    blk += so + f'theorem proot_hi : okT [] rt 0 {L + 1} {hi2} = true := by decide +kernel\n'
    blk += 'lemma iroot_pos {t : ℕ} {S : Finset ℕ} (ht1 : 1 ≤ t) (hS : (S : Set ℕ) ⊆ C (mz 0) (WZ [] 0))\n'
    blk += f'    (hl : Live Z0 (mz 0) (tz 0) {L} t S) : False := by\n'
    blk += f'  have hmin : ∀ q < {L}, ¬ Sol Z0 (mz 0) (tz 0) q (C (mz 0) (WZ [] 0)) := fun q hq => iroot q hq\n'
    blk += f'  have hm0 : Min Z0 (mz 0) (tz 0) {L} t S := ⟨hl, fun q hq hs => hmin q hq (hs.mono le_rfl (by rintro x (hx | hx); exact hS hx; exact Or.inr hx))⟩\n'
    blk += f'  have htk : t < {L + 1} := by have := hm0.size.2; omega\n'
    blk += f'  have hM : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk [] rt 0 {L} t p.1 p.2 = false := by\n    have h := proot_hi\n'
    blk += '    simp only [okT, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, Bool.not_eq_true\'] at h\n'
    blk += '    obtain ⟨' + ', '.join(f'h{q}' for q in hi2) + '⟩ := h\n    interval_cases t\n'
    blk += '\n'.join([f'    · exact one proot_{q}' for q in (1, 2, 3)] + [f'    · exact one h{q}' for q in hi2]) + '\n'
    blk += f'  exact imp_of_live (L := {L + 1}) (Or.inl rfl) root_p (by norm_num) ir (by omega) hS hl hmin (Or.inr hM)\n'
    t = t[:i0] + blk + t[i1:]
    fx = ' || '.join(f'(x {a} && x {b})' for a, b in E)
    ef = None
    for a, b in E:
        term = f'(rawP.getD {a} 0 &&& rawP.getD {b} 0)'; ef = term if ef is None else f'({ef} ||| {term})'
    sub_line('def f (x : Fin 8 → Bool) : Bool := ', f'def f (x : Fin 8 → Bool) : Bool := {fx}')
    sub_line('def EF : ℕ := ', f'def EF : ℕ := {ef}')
    sub_line('theorem final : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 ', f'theorem final : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => {fx}) t → {L} ≤ t := by')
    sub_line("  have hlt' : t < ", f"  have hlt' : t < {L} := by omega")
    gl = ', '.join(f'⟨.{op}, [{a}, {b}]⟩' for op, a, b in gates)
    sub_line('def onWit : List Gate := ', f'def onWit : List Gate := [{gl}]')
    sub_line('  rcases hg with rfl | ', '  rcases hg with ' + ' | '.join(['rfl'] * m) + ' <;> simp')
    sub_line('    Circuit.eval ⟨onWit, ', f'    Circuit.eval ⟨onWit, {outw}⟩ (List.ofFn x) = f x := by')
    old_flat = re.search(r'theorem onGraphCorrect : ∀ x : Fin 8 → Bool, f x = decide \(∃ i < \(\[([0-9, ]+)\] : List ℕ\)', t).group(1)
    lines = t.split('\n')
    for i, l in enumerate(lines):
        if l.startswith('theorem onGraphCorrect : '): lines[i] = l.replace('[' + old_flat + ']', '[' + flat + ']')
    t = '\n'.join(lines)
    sub_line('  · have hge : ', f'  · have hge : {m} ≤ gates.length := by')
    sub_line('      by_cases hlt2 : gates.length < ', f'      by_cases hlt2 : gates.length < {L}')
    sub_line('      · have heq : gates.length = ', f'      · have heq : gates.length = {L} := by omega')
    sub_line('    have hw : onWit.length = ', f'    have hw : onWit.length = {m} := rfl')
    sub_line('    exact ⟨onWit, ', f'    exact ⟨onWit, {outw}, onWitBasis, by omega, fun x => (onWitCorrect x).trans (onGraphCorrect x)⟩')
    # the two statements: the posted one, verbatim
    i0 = t.index('theorem onFinal :\n') + len('theorem onFinal :\n'); i1 = t.index(' := by\n  intro gates o hfit _hone hev', i0)
    t = t[:i0] + stmt + t[i1:]
    i0 = t.index(f'theorem PEqualNP.Outside.{TEMPLATE_ID} :\n') + len(f'theorem PEqualNP.Outside.{TEMPLATE_ID} :\n'); i1 = t.index(f' :=\n  PEqualNP.Outside.{TEMPLATE_ID}.onFinal', i0)
    t = t[:i0] + stmt + t[i1:]
    t = t.replace(TEMPLATE_ID, step.replace('-', '_'))
    t = t.replace('import PEqualNP.Defs\n', 'import PEqualNP.Defs\n\n-- The whole proof text is that of the merged ' + TEMPLATE_ID + ' (same repository, Apache-2.0), whose header follows;\n-- only the data of this graph (rows, tables of sub-bounds, bounds, witness) was computed anew.\n', 1)
    return t, dict(m=m, L=L, NN=NN, sizes={''.join(map(str, Z)): s for Z, s in size.items()})

if __name__ == '__main__':
    step, sf, out = sys.argv[1:4]; secs = float(sys.argv[4]) if len(sys.argv) > 4 else 20.0
    r = build(step, open(sf).read().strip(), secs)
    if not r: print('not a row of this family, or no data'); sys.exit(3)
    open(out, 'w').write(r[0]); json.dump(r[1], open(out + '.json', 'w')); print('written', r[1]['m'], 'gates witness, root bound', r[1]['L'], 'rows', r[1]['NN']); sys.exit(0)
