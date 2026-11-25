#!/usr/bin/env python3
"""Rows "for the monotone six-input f with table A * 2^32 + B: each AND/OR/NOT circuit of fan-in at
most two has an AND/OR one no larger" (and the "symmetric in inputs" rows of the same shape).

Method: the accepted proof of the five-input class row L-meta-8718 (k-sandhu, Apache-2.0; it says
it follows L-meta-8463 and L-meta-1449), ported to six inputs.  That proof shows: a circuit with a
NOT gate has fewer binary gates than gates; and a kernel-checked search over 32 pairs (true point,
false point) shows that more than n binary gates are needed even when NOT gates are free.  With a
monotone circuit of n + 2 gates as witness, the statement follows.

  python3 gen6.py <step id> <statement file> <out.lean>

Exit 0: file written.  Exit 1: the method does not apply to this function (the free-NOT bound is
too weak on every sample tried, or no small monotone circuit was found)."""
import itertools, os, random, re, subprocess, sys
from pysat.solvers import Cadical153
HERE = os.path.dirname(os.path.abspath(__file__))
N = 6

def parse(stmt):
    m = re.search(r'Nat\.testBit \((\d+) \* 2 \^ 32 \+ (\d+)\) \(∑ i : Fin 6, if x i then 2 \^ \(i : ℕ\) else 0\)', stmt)
    if not m or stmt.startswith('¬'): return None
    expr = f'({m.group(1)} * 2 ^ 32 + {m.group(2)})'
    return expr, int(m.group(1)) * 2 ** 32 + int(m.group(2))

def monotone_circuit(T, k):
    """A circuit of exactly k AND/OR gates of fan-in two for the table T, or None (SAT)."""
    nv = [0]
    def new():
        nv[0] += 1; return nv[0]
    cls = []; R = 1 << N
    val = [[bool(r >> i & 1) for r in range(R)] for i in range(N)]
    typ = []; sel = []
    for g in range(k):
        c = new(); typ.append(c)
        pairs = list(itertools.combinations(range(N + g), 2))
        ps = [new() for _ in pairs]; sel.append((pairs, ps))
        cls.append(list(ps))
        for a, b in itertools.combinations(ps, 2): cls.append([-a, -b])
        row = [new() for _ in range(R)]
        for (i, j), p in zip(pairs, ps):
            for r in range(R):
                x, y, v = val[i][r], val[j][r], row[r]
                # p -> (v <-> (c ? x&y : x|y))
                def lit(z): return z
                for cv in (True, False):
                    for xv in ((True, False) if not isinstance(x, bool) else (x,)):
                        for yv in ((True, False) if not isinstance(y, bool) else (y,)):
                            out = (xv and yv) if cv else (xv or yv)
                            cl = [-p, -c if cv else c]
                            if not isinstance(x, bool): cl.append(-x if xv else x)
                            if not isinstance(y, bool): cl.append(-y if yv else y)
                            cl.append(v if out else -v)
                            cls.append(cl)
        val.append(row)
    for r in range(R): cls.append([val[-1][r] if T >> r & 1 else -val[-1][r]])
    with Cadical153(bootstrap_with=cls) as s:
        if not s.solve(): return None
        mod = set(l for l in s.get_model() if l > 0)
    gates = []
    for g in range(k):
        pairs, ps = sel[g]
        i, j = next(pr for pr, p in zip(pairs, ps) if p in mod)
        gates.append(('and' if typ[g] in mod else 'or', i, j))
    return gates

def check_circuit(T, gates):
    for r in range(1 << N):
        w = [bool(r >> i & 1) for i in range(N)]
        for op, a, b in gates: w.append((w[a] and w[b]) if op == 'and' else (w[a] or w[b]))
        if w[-1] != bool(T >> r & 1): return False
    return True

def words(pairs):
    ws = []
    for j in range(N):
        w = 0
        for i, (p, q) in enumerate(pairs):
            w |= (p >> j & 1) << i; w |= (q >> j & 1) << (32 + i)
        ws.append(w)
    return ws

def samples(T, n, tries=400, seed=1):
    """32 pairs (true point, false point) on which the search with n steps answers false, with the fewest calls."""
    exe = '/tmp/livesearch_gen6'
    subprocess.run(['gcc', '-O2', '-o', exe, f'{HERE}/livesearch.c'], check=True)
    tr = [r for r in range(1 << N) if T >> r & 1]; fa = [r for r in range(1 << N) if not T >> r & 1]
    near = [(p, q) for p in tr for q in fa if bin(p ^ q).count('1') == 1]
    far = [(p, q) for p in tr for q in fa if bin(p ^ q).count('1') == 2]
    rest = [(p, q) for p in tr for q in fa if bin(p ^ q).count('1') > 2]
    rnd = random.Random(seed); best = None
    for t in range(tries):
        a, b, c = near[:], far[:], rest[:]
        rnd.shuffle(a); rnd.shuffle(b); rnd.shuffle(c)
        if t % 3 == 1: pool = a + b + c
        elif t % 3 == 2: pool = sorted(a + b, key=lambda _: rnd.random()) + c
        else: pool = a + b + c
        pairs = pool[:32]
        if len(pairs) < 32: continue
        ws = words(pairs)
        if len(set(ws)) < N: continue
        out = subprocess.run([exe, str(n)] + ['%x' % w for w in ws], capture_output=True, text=True, timeout=120).stdout.split()
        if out and out[0] == 'false':
            calls = int(out[1])
            if best is None or calls < best[0]: best = (calls, pairs, ws)
            if calls < 20000 and t >= 20: break
    return best

def lean(step, stmt, expr, n, m, ws, gates):
    ns = step.replace('-', '_')
    s = open(f'{HERE}/template_8718.lean').read()
    s = s.replace('L_meta_8718', ns)
    s = s.replace('-- The signed live-wire search follows', '-- Ported to six inputs from the checked proof of L-meta-8718.\n-- The signed live-wire search follows')
    head, tail = s.split('def targetFun (T : ℕ)', 1)
    tail = 'def targetFun (T : ℕ)' + tail
    tail = tail.split(f'end PEqualNP.Outside.{ns}')[0]
    tail = tail.replace('Fin 5', 'Fin 6').replace('inputs.length = 5', 'inputs.length = 6')
    tail = tail.replace('search 5 inputs', f'search {n} inputs').replace('5 < binaryCost gs', f'{n} < binaryCost gs')
    tail = tail.replace('search_complete ht 5 inputs', f'search_complete ht {n} inputs')
    tail = tail.replace('search 5 rows', f'search {n} rows').replace('HasCircuitSize 5', 'HasCircuitSize 6')
    tail = tail.replace('0xfeeeeeea', expr).replace('change 7 ≤ s', f'change {m} ≤ s')
    a = tail.index('def rows : List W :='); b = tail.index('set_option maxRecDepth 16000 in')
    g = ', '.join(f'⟨.{op}, [{i}, {j}]⟩' for op, i, j in gates)
    tail = (tail[:a] + 'def rows : List W :=\n  [' + ', '.join('0x%016x' % w for w in ws) + ']\n\n'
            + f'def witness : Circuit :=\n  ⟨[{g}], {N + len(gates) - 1}⟩\n\n' + tail[b:])
    tail = tail.replace('refine ⟨witness, by simp [Monotone2, witness], ?_, by decide⟩', 'refine ⟨witness, by simp [Monotone2, witness], ?_, by decide +kernel⟩')
    for bad in ('Fin 5', 'feeeeeea', 'inputs.length = 5', 'HasCircuitSize 5'): assert bad not in tail, bad
    final = (f'end PEqualNP.Outside.{ns}\n\ntheorem PEqualNP.Outside.{ns} :\n    {stmt} := by\n'
             f'  exact PEqualNP.Outside.{ns}.solve\n')
    return head + tail + final

SYNTH_SECONDS = 90
def main():
    if sys.argv[1] == 'synth':
        g = monotone_circuit(int(sys.argv[2]), int(sys.argv[3]))
        print('GATES' + repr(g) if g else 'NONE'); return 0
    step, sf, out = sys.argv[1:4]
    stmt = open(sf).read().strip()
    p = parse(stmt)
    if not p: print('not a six-input row of this shape'); return 2
    expr, T = p
    # the smallest k for which a circuit is found; a size that does not answer within the time
    # limit is skipped (the witness need not be proved least: the search below is what counts)
    gates = None
    for k in range(2, 12):
        try:
            r = subprocess.run([sys.executable, os.path.abspath(__file__), 'synth', str(T), str(k)], capture_output=True, text=True, timeout=SYNTH_SECONDS)
        except subprocess.TimeoutExpired:
            continue
        if r.stdout.startswith('GATES'):
            gates = eval(r.stdout[5:]); break
    if not gates or not check_circuit(T, gates): print('no monotone circuit with at most 11 gates found'); return 1
    m = len(gates); n = m - 2
    if n < 1: print('function too small for this method'); return 1
    best = samples(T, n)
    if not best: print(f'monotone size {m}: the free-NOT search with {n} steps finds a circuit on every sample tried'); return 1
    calls, pairs, ws = best
    open(out, 'w').write(lean(step, stmt, expr, n, m, ws, gates))
    print(f'wrote {out}: monotone size {m}, search depth {n}, {calls} calls'); return 0

if __name__ == '__main__':
    sys.exit(main())
