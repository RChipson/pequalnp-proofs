#!/usr/bin/env python3
"""Proof generator for the rows "At fan-in two, one NOT gate saves nothing on edges ..." (7 inputs).

Route: (1) find an AND/OR circuit with m gates for the edge function (annealing on the decisive
rows, then checked on all 128 inputs); (2) replay the compact search of the accepted proof
L-meta-528 (it treats negations as free, so it bounds every AND/OR/NOT circuit) with a budget of
m - 1 gates; if it closes, no circuit of fewer than m gates exists at all, so the m-gate AND/OR
circuit is never longer than a given circuit.  The Lean file is L-meta-528 ported to 7 inputs
plus a short wrapper.  Nothing is written unless both parts succeed here first.

Usage: gen1not.py <step id> <statement file> <out file> [max positions, default 250000]"""
import re, subprocess, sys, os, tempfile, itertools
S = '/tmp/claude-0/-home-user-pequalnp-proofs/740307a3-5578-556b-b545-0397351cd4f4/scratchpad'
N = 7

def parse(stmt):
    m = re.search(r'\(\[([0-9, ]+)\] : List ℕ\)', stmt)
    L = [int(x) for x in m.group(1).split(',')]
    return L, [(L[2 * i], L[2 * i + 1]) for i in range(len(L) // 2)]

def mis(n, edges):
    adj = [set() for _ in range(n)]
    for a, b in edges: adj[a].add(b); adj[b].add(a)
    out = []
    def rec(cur, cand, excl):
        if not cand and not excl: out.append(frozenset(cur)); return
        for v in list(cand):
            rec(cur | {v}, cand - adj[v] - {v}, excl - adj[v] - {v})
            cand = cand - {v}; excl = excl | {v}
    rec(set(), set(range(n)), set())
    return out

def anneal(E, lo=7, hi=16, secs=20):
    """smallest AND/OR circuit found: list of (op, a, b) with wire numbers, output = last gate"""
    f = lambda x: any(x >> a & 1 and x >> b & 1 for a, b in E)
    rows = [(1 << a) | (1 << b) for a, b in E] + [sum(1 << v for v in m) for m in mis(N, E)]
    assert len(rows) <= 64
    cols = [sum(((rows[k] >> v) & 1) << k for k in range(len(rows))) for v in range(N)]
    base = open(S + '/desk/L-meta-3004/sa14.c').read()
    src = re.sub(r'static u64 cols\[14\]=\{[^}]*\}', 'static u64 cols[7]={' + ', '.join(f'{c}ULL' for c in cols) + '}', base)
    src = src.replace('target=2097151ULL', f'target={(1 << len(E)) - 1}ULL').replace('#define NI 14', '#define NI 7')
    d = tempfile.mkdtemp(dir=S)
    open(d + '/a.c', 'w').write(src)
    subprocess.run(['gcc', '-O2', '-o', d + '/a', d + '/a.c', '-lm'], check=True)
    best = None
    for n in range(hi, lo - 1, -1):
        ok = None
        for seed in (3, 4, 5):
            r = subprocess.run(['timeout', str(secs), d + '/a', str(n), str(seed), '20000000', '1.0', '0.1', '60'], capture_output=True, text=True)
            if 'FOUND' in r.stdout: ok = r.stdout; break
        if not ok: break
        gates = [(l.split()[1], int(l.split()[2]), int(l.split()[3])) for l in ok.strip().split('\n')[1:]]
        # check on all inputs
        for x in range(1 << N):
            w = [bool(x >> i & 1) for i in range(N)]
            for op, a, b in gates: w.append((w[a] and w[b]) if op == 'AND' else (w[a] or w[b]))
            assert w[-1] == f(x), 'annealed circuit wrong off the decisive rows'
        best = gates
    return best

def replay(E, K, cap):
    f = lambda x: any(x >> a & 1 and x >> b & 1 for a, b in E)
    prs = [(x, i) for x in range(1 << N) for i in range(N) if not f(x) and not x >> i & 1 and f(x | 1 << i)]
    M = len(prs); rws = [x for x, i in prs] + [x | 1 << i for x, i in prs]
    raw = [sum(((rws[k] >> v) & 1) << k for k in range(2 * M)) for v in range(N)]
    sites = [next(k for k, (x, i) in enumerate(prs) if i == v) for v in range(N)]
    FULL = (1 << (2 * M)) - 1; LOW = (1 << M) - 1
    neg = lambda x: x ^ FULL
    canon = lambda x: neg(x) if x & 1 else x
    sep = lambda x: (x ^ (x >> M)) & LOW
    goal = canon(LOW << M); inputs = [canon(v) for v in raw]
    def singles(l):
        if not l: return []
        a, rest = l[0], l[1:]
        return [(a, rest)] + [(b, [a] + bs) for b, bs in singles(rest)]
    def pairs(l):
        if not l: return []
        a, rest = l[0], l[1:]
        return [(a, b, bs) for b, bs in singles(rest)] + [(b, c, [a] + bs) for b, c, bs in pairs(rest)]
    cnt = [0]
    def cuts(ws):
        v = 0
        for w in ws: v |= sep(w)
        return v
    class Cap(Exception): pass
    def dispatch(extra, k, a, b, r):
        base = cuts(r)
        for w in (a & b, a & neg(b), neg(a) & b, neg(a) & neg(b)):
            v = sep(w) | base
            if v == LOW and opt(k, extra, [canon(w)] + r): return True
            if extra != 0:
                if (v | sep(a)) == LOW and opt(k, extra - 1, [canon(w), a] + r): return True
                if (v | sep(b)) == LOW and opt(k, extra - 1, [canon(w), b] + r): return True
            if extra >= 2 and (v | sep(a) | sep(b)) == LOW and opt(k, extra - 2, [canon(w), a, b] + r): return True
        return False
    def opt(k, extra, ws):
        cnt[0] += 1
        if cnt[0] > cap: raise Cap()
        if ws == [goal]: return True
        if k == 0: return False
        return any(dispatch(extra, k - 1, a, b, r) for a, b, r in pairs(ws))
    try:
        res = opt(K, K + 1 - N, inputs)
    except Cap:
        return None, cnt[0], M, raw, sites
    return (not res), cnt[0], M, raw, sites

def main():
    step, stmt_file, out = sys.argv[1], sys.argv[2], sys.argv[3]
    cap = int(sys.argv[4]) if len(sys.argv) > 4 else 250000
    ident = step.replace('-', '_')
    stmt = open(stmt_file).read().strip()
    L, E = parse(stmt)
    assert set(v for e in E for v in e) <= set(range(N)) and stmt.count(str(L).replace(' ', '')) == 0
    circ = anneal(E)
    if not circ: sys.exit('no AND/OR circuit found')
    m = len(circ); K = m - 1; X = K + 1 - N
    if X < 0: sys.exit('circuit smaller than the number of inputs minus one: not this route')
    closes, positions, M, raw, sites = replay(E, K, cap)
    print(f'{step}: {len(E)} edges, AND/OR circuit of {m} gates, search with budget {K}: closes={closes}, positions={positions}')
    if not closes: sys.exit('the search does not close within the cap: no file written')
    src = subprocess.run(['git', '-C', '/home/user/pequalnp-proofs', 'show', 'upstream/main:lean/PEqualNP/Outside/L_meta_528.lean'],
                         capture_output=True, text=True, check=True).stdout
    mm = re.search(r'def rawInputs : List W :=\s*\[(.*?)\]', src, re.S)
    src = src[:mm.start()] + '@@RAW@@' + src[mm.end():]
    assert '0x' not in src
    src = re.sub(r'\b340\b', str(2 * M), src); src = re.sub(r'\b170\b', str(M), src)
    src = src.replace('@@RAW@@', 'def rawInputs : List W :=\n  [' + ',\n   '.join(hex(v) for v in raw) + ']')
    old_sites = '[1, 0, 2, 7, 17, 25, 48, 93]'; assert old_sites in src
    src = src.replace(old_sites, '[' + ', '.join(map(str, sites)) + ']')
    g_old = ('  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) ||\n'
             '  (x 0 && x 5) || (x 0 && x 6) || (x 2 && x 7)'); assert g_old in src
    gexpr = ' || '.join(f'(x {a} && x {b})' for a, b in E)
    src = src.replace(g_old, '  ' + gexpr)
    h_old = ('(x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||\n'
             '      (x 4 &&& x 5) ||| (x 0 &&& x 5) ||| (x 0 &&& x 6) ||| (x 2 &&& x 7) ='); assert h_old in src
    src = src.replace(h_old, ' ||| '.join(f'(x {a} &&& x {b})' for a, b in E) + ' =')
    src = re.sub(r'Fin 8\b', 'Fin 7', src).replace('HasCircuitSize 8', 'HasCircuitSize 7')
    # the bound proved by the optimised search
    a = src.index('theorem lower_of_optimized'); b = src.index('end Check528', a)
    blk = src[a:b]
    for o, n_ in (('optimized 9 2 inputs', f'optimized {K} {X} inputs'), ('10 ≤ s', f'{m} ≤ s'),
                  ('C.gates.length ≤ 9', f'C.gates.length ≤ {K}'), ('optimized_complete 9 inputs 2', f'optimized_complete {K} inputs {X}')):
        assert o in blk, o; blk = blk.replace(o, n_)
    src = src[:a] + blk + src[b:]
    o = 'dispatch 2 (optimized 8)'; assert o in src; src = src.replace(o, f'dispatch {X} (optimized {K - 1})')
    # 21 root pairs instead of 28
    # all kernel checks go inside one proof, one after another: as separate theorems Lean checks
    # them at the same time and runs out of memory
    for i in range(28):
        pat = re.compile(r'set_option maxRecDepth 16000 in\nset_option maxHeartbeats 8000000 in\ntheorem frontier%d : rootF %d = false := by decide \+kernel\n\n' % (i, i))
        assert pat.search(src), i; src = pat.sub('', src)
    for i in range(21, 28):
        line = f'    · exact frontier{i}\n'; assert line in src; src = src.replace(line, '')
    o = 'set_option maxHeartbeats 2000000 in\ntheorem all_front'; assert o in src
    src = src.replace(o, 'set_option maxHeartbeats 8000000 in\ntheorem all_front')
    o = '  have hlen : (pairs inputs).length = 28 := by decide\n'; assert o in src
    src = src.replace(o, ''.join(f'  have frontier{i} : rootF {i} = false := by decide +kernel\n' for i in range(21)) + o)
    for o, n_ in (('optimized 9 2 inputs = false', f'optimized {K} {X} inputs = false'), ('(pairs inputs).length = 28', '(pairs inputs).length = 21'),
                  ('∀ i : Fin 28', '∀ i : Fin 21')):
        assert o in src, o; src = src.replace(o, n_)
    i = src.index('theorem PEqualNP.Outside.L_meta_528'); src = src[:i]
    j = src.rindex('end Check528'); body, tail = src[:j], src[j:]
    av = [f'a{i}' for i in range(N)]
    lst = '[' + ', '.join(av) + ']'
    Ls = '[' + ', '.join(map(str, L)) + ']'
    gexpr_a = ' || '.join(f'(a{a} && a{b})' for a, b in E)
    gates_lean = '[' + ', '.join(f'⟨GateOp.{op.lower()}, [{a}, {b}]⟩' for op, a, b in circ) + ']'
    outw = N + m - 1
    wrap = f'''
-- The wrapper for this row: the search bounds every AND/OR/NOT circuit, and an AND/OR circuit of
-- {m} gates is exhibited.
theorem ofFn7 (x : Fin 7 → Bool) : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
  rfl

theorem tableL : ∀ {' '.join(av)} : Bool,
    decide (∃ i < ({Ls} : List ℕ).length / 2,
      ({lst} : List Bool).getD (({Ls} : List ℕ).getD (2 * i) 0) false = true ∧
      ({lst} : List Bool).getD (({Ls} : List ℕ).getD (2 * i + 1) 0) false = true) =
    ({gexpr_a}) := by
  decide

def small : Circuit := ⟨{gates_lean}, {outw}⟩

theorem tableC : ∀ {' '.join(av)} : Bool,
    small.eval {lst} = ({gexpr_a}) := by
  decide

theorem graph_eq (x : Fin 7 → Bool) : graph x =
    ({' || '.join(f'(x {a} && x {b})' for a, b in E)}) := rfl

end Check528

theorem PEqualNP.Outside.L_meta_528 : {stmt} := by
  intro gates o hg _ he
  have hfan : PEqualNP.MetaComplexity.FanInTwo ⟨gates, o⟩ := by
    intro g hgm
    refine ⟨?_, (hg g hgm).2⟩
    rcases (hg g hgm).1 with h | h | h <;> simp [h]
  have hbr : ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = Check528.graph x := by
    intro x
    rw [he x, Check528.ofFn7 x, Check528.tableL, Check528.graph_eq]
  have hsize : {m} ≤ gates.length :=
    Check528.lower_of_optimized Check528.all_front gates.length ⟨⟨gates, o⟩, hfan, le_refl _, hbr⟩
  refine ⟨Check528.small.gates, Check528.small.output, ?_, ?_, ?_⟩
  · intro g hgm
    simp only [Check528.small, List.mem_cons, List.not_mem_nil, or_false] at hgm
    rcases hgm with {' | '.join(['rfl'] * m)} <;> simp
  · exact hsize
  · intro x
    have h := Check528.tableC (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)
    rw [Check528.ofFn7 x, Check528.tableL]
    exact h
'''
    assert tail.strip() == 'end Check528', tail[:80]
    src = body + wrap
    src = src.replace('Live528', f'PEqualNP.Outside.{ident}.Live').replace('Check528', f'PEqualNP.Outside.{ident}.Check').replace('L_meta_528', ident)
    src = src.replace('import PEqualNP.Defs\n', 'import PEqualNP.Defs\n\n-- Search checker adapted from the accepted proof L-meta-528 (7 inputs here); the rows are the\n-- sensitive pairs of this graph.\n', 1)
    assert src.count(chr(34)) == 0
    open(out, 'w').write(src)
    print('wrote', out, len(src.encode()), 'bytes')

if __name__ == '__main__':
    main()
