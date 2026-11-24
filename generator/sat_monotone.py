"""Search for a monotone circuit (AND/OR gates, each reading two distinct earlier wires)
with exactly N gates that computes the edge function of a graph.  Because such a circuit
computes a monotone function, it is right on every input as soon as it is right on the
minimal true inputs (the edges) and on the maximal false inputs (the maximal independent
sets).  Usage: python3 sat_monotone.py <N> <n vertices> <edge list like 0-6,0-7,...>
"""
import sys, itertools, time
from pysat.solvers import Cadical153
from pysat.card import CardEnc, EncType

def main():
    N = int(sys.argv[1]); n = int(sys.argv[2])
    E = [tuple(map(int, e.split('-'))) for e in sys.argv[3].split(',')]
    adj = {v: set() for v in range(n)}
    for a, b in E: adj[a].add(b); adj[b].add(a)
    def indep(S): return all(not (adj[v] & S) for v in S)
    mis = []
    for m in range(1 << n):
        S = {v for v in range(n) if m >> v & 1}
        if indep(S) and all((adj[v] & S) for v in range(n) if v not in S): mis.append(S)
    rows = [({a, b}, True) for a, b in E] + [(S, False) for S in mis]
    R = len(rows)
    print(f'N={N} vertices={n} edges={len(E)} maximal independent sets={len(mis)} rows={R}', flush=True)
    cnt = [0]
    def new():
        cnt[0] += 1; return cnt[0]
    W = n + N
    val = {}
    for w in range(n, W):
        for r in range(R): val[w, r] = new()
    typ = {w: new() for w in range(n, W)}          # true = OR
    sel = {}
    cls = []
    def lit(w, r):                                  # (is_const, value or literal)
        if w < n: return (True, w in rows[r][0])
        return (False, val[w, r])
    def add(clause):
        out = []
        for c in clause:
            if c is True: return
            if c is False: continue
            out.append(c)
        cls.append(out)
    def pos(x): return x[1] if x[0] else x[1]
    def neg(x): return (not x[1]) if x[0] else -x[1]
    for w in range(n, W):
        opts = []
        for j, k in itertools.combinations(range(w), 2):
            s = new(); sel[w, j, k] = s; opts.append(s)
            for r in range(R):
                a, b, o = lit(j, r), lit(k, r), val[w, r]
                add([-s, neg(a), neg(b), o])
                add([-s, pos(a), pos(b), -o])
                add([-s, neg(a), pos(b), -typ[w], o]); add([-s, neg(a), pos(b), typ[w], -o])
                add([-s, pos(a), neg(b), -typ[w], o]); add([-s, pos(a), neg(b), typ[w], -o])
        cls.append(opts)
        enc = CardEnc.atmost(lits=opts, bound=1, top_id=cnt[0], encoding=EncType.seqcounter)
        cnt[0] = max(cnt[0], enc.nv); cls.extend(enc.clauses)
    for r in range(R):
        cls.append([val[W - 1, r] if rows[r][1] else -val[W - 1, r]])
    FIRST = sys.argv[4] if len(sys.argv) > 4 else ''
    if FIRST: cls.append([typ[n]] if FIRST == 'or' else [-typ[n]])
    # no gate repeats another gate; gates that do not depend on each other come in a fixed order
    pairs = {w: list(itertools.combinations(range(w), 2)) for w in range(n, W)}
    if not FIRST:
        for w in range(n, W - 1):
            for (j, k) in pairs[w]:
                for (j2, k2) in pairs[w + 1]:
                    if k2 != w and j2 != w and (k2, j2) < (k, j):
                        cls.append([-sel[w, j, k], -sel[w + 1, j2, k2]])
    for w in range(n, W):
        for w2 in range(w + 1, W):
            for (j, k) in pairs[w]:
                cls.append([-sel[w, j, k], -sel[w2, j, k], typ[w], typ[w2]])
                cls.append([-sel[w, j, k], -sel[w2, j, k], -typ[w], -typ[w2]])
    for w in range(n, W - 1):                       # every gate but the last is read by a later gate
        cls.append([sel[x, j, k] for (x, j, k) in sel if x > w and (j == w or k == w)])
    print(f'variables={cnt[0]} clauses={len(cls)}', flush=True)
    t0 = time.time()
    from pysat.solvers import Glucose4
    s = (Glucose4 if (len(sys.argv) > 5 and sys.argv[5] == 'glucose') else Cadical153)(bootstrap_with=cls)
    ok = s.solve()
    print(f'result={"SAT" if ok else "UNSAT"} time={time.time()-t0:.0f}s', flush=True)
    if ok:
        m = set(x for x in s.get_model() if x > 0)
        gates = []
        for w in range(n, W):
            j, k = next((j, k) for (x, j, k) in sel if x == w and sel[x, j, k] in m)
            gates.append(('or' if typ[w] in m else 'and', j, k))
        print('GATES', gates, flush=True)

main()
