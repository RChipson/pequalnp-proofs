#!/usr/bin/env python3
"""Mixed-OR circuits for the large key tables (32 by 32, 128 by 128).

The blocks (S_i x T_i) of a cover are paired: blocks i and j with no common row and no common column share one
AND gate, (OR S_i or OR T_j) AND (OR S_j or OR T_i).  The pairing is chosen to make the mixed sets share
(row, column) pairs: two mixed sets (S_i, T_p(i)) and (S_k, T_p(k)) can share |S_i and S_k| * |T_p(i) and T_p(k)|
such pairs.  That count is maximised by simulated annealing over pairings; then the ORs are shared for real
(pairsa.pre_pairs, cse.paar) and the circuit is checked by simulation.

  python3 bigmixed.py <table dir> <n> <seconds for the pairing> <seconds for the pair matching> [seed] [cover file]
writes <table dir>/bigmixed_<seed>.json  ({"gates": [...], "out": w})"""
import json, math, os, random, sys, time
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import gencover, pairsa
from cse import paar

def main():
    d, n = sys.argv[1], int(sys.argv[2]); t_pair, t_cse = float(sys.argv[3]), float(sys.argv[4])
    seed = int(sys.argv[5]) if len(sys.argv) > 5 else 1
    cov = sys.argv[6] if len(sys.argv) > 6 else f'{d}/best.txt'
    rnd = random.Random(seed)
    rows = json.load(open(f'{d}/table.json'))
    target = sum(rows[u] << (u * n) for u in range(n))
    B = gencover.load_blocks(cov); m = len(B)
    Sm = np.array([[(S >> u) & 1 for u in range(n)] for S, T in B], dtype=np.int32)
    Tm = np.array([[(T >> v) & 1 for v in range(n)] for S, T in B], dtype=np.int32)
    R = Sm @ Sm.T; C = Tm @ Tm.T
    ok = (R == 0) & (C == 0)
    np.fill_diagonal(R, 0)
    p = list(range(m))                         # partner; p[i] = i: unpaired
    order = list(range(m)); rnd.shuffle(order)
    for i in order:
        if p[i] != i: continue
        cand = [j for j in order if j != i and p[j] == j and ok[i, j]]
        if cand: j = rnd.choice(cand); p[i] = j; p[j] = i
    MODE = os.environ.get('BM_MODE', 'prod')
    Cz = C.copy(); np.fill_diagonal(Cz, 0)
    def score(p):
        pa = np.array(p); paired = (pa != np.arange(m))
        Cp = Cz[np.ix_(pa, pa)] * np.outer(paired, paired)
        if MODE == 'prod': return int((R * Cp).sum()) // 2
        Tt = R + Cp                                     # size of the common part of two mixed sets
        if MODE == 'lin': return int(np.maximum(Tt - 1, 0).sum()) // 2
        if MODE == 'sq': return int((np.maximum(Tt - 1, 0) ** 2).sum()) // 2
        # 'best': every set counts only its largest overlaps (it cannot share everything with everybody)
        Z = np.maximum(Tt - 1, 0); Zs = np.sort(Z, axis=1)[:, -3:]
        return int(Zs.sum())
    cur = score(p); best = cur; bestp = p[:]
    t0 = time.time(); it = 0; T = 3.0
    while True:
        it += 1
        if it % 256 == 0:
            el = time.time() - t0
            if el > t_pair: break
            T = 3.0 * (1 - el / t_pair) + 0.05
        i, k = rnd.sample(range(m), 2)
        if p[i] == k: continue
        j, l = p[i], p[k]
        q = p[:]
        # re-pair i with k's partner (or with k), keeping everything valid
        if rnd.random() < 0.5:
            a, b, c, e = i, (l if l != k else k), k, (j if j != i else i)
        else:
            a, b, c, e = i, k, (j if j != i else None), (l if l != k else None)
        def setpair(x, y):
            if x is None or y is None:
                z = x if y is None else y
                if z is not None: q[z] = z
                return True
            if x == y: q[x] = x; return True
            if not ok[x, y]: return False
            q[x] = y; q[y] = x; return True
        for z in {i, j, k, l}: q[z] = z
        if not setpair(a, b): continue
        if c is not None and e is not None and c != e and (c in (a, b) or e in (a, b)): continue
        if not setpair(c, e): continue
        if any(q[q[z]] != z for z in (i, j, k, l)): continue
        s = score(q)
        if s >= cur or rnd.random() < math.exp((s - cur) / T):
            p, cur = q, s
            if cur > best: best = cur; bestp = p[:]
    p = bestp
    print('pairing score', best, 'paired', sum(1 for i in range(m) if p[i] != i), 'of', m, 'after', it, 'moves', flush=True)
    terms = []
    sets_of = lambda i: ({u for u in range(n) if B[i][0] >> u & 1}, {n + v for v in range(n) if B[i][1] >> v & 1})
    for i in range(m):
        Si, Ti = sets_of(i)
        if p[i] == i: terms.append((Si, Ti))
        elif i < p[i]:
            Sj, Tj = sets_of(p[i]); terms.append((Si | Tj, Sj | Ti))
    sets = []
    for a, b in terms: sets += [frozenset(a), frozenset(b)]
    pre, defs0 = pairsa.pre_pairs(sets, t_cse, rnd)
    g, defs, cur_sets = paar([frozenset(x) for x in pre], rnd)
    gates = []; wire = {i: i for i in range(2 * n)}
    for z, a, b in defs0 + defs:
        gates.append(('or', wire[a], wire[b])); wire[z] = 2 * n + len(gates) - 1
    outw = []; memo = {}
    for s in cur_sets:
        k = frozenset(s)
        if k not in memo:
            l = sorted(wire[i] for i in s); w = l[0]
            for x in l[1:]:
                gates.append(('or', min(w, x), max(w, x))); w = 2 * n + len(gates) - 1
            memo[k] = w
        outw.append(memo[k])
    acc = None
    for t in range(len(terms)):
        x, y = outw[2 * t], outw[2 * t + 1]
        gates.append(('and', min(x, y), max(x, y))); w = 2 * n + len(gates) - 1
        if acc is None: acc = w
        else: gates.append(('or', acc, w)); acc = 2 * n + len(gates) - 1
    assert gencover.simulate(n, gates, acc) == target, 'circuit is wrong'
    print('gates', len(gates), flush=True)
    json.dump({'gates': gates, 'out': acc}, open(f'{d}/bigmixed_{seed}.json', 'w'))

main()
