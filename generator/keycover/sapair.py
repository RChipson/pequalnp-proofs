#!/usr/bin/env python3
"""Pairing of key blocks by simulated annealing on the TRUE cost: the number of OR gates cse.paar needs for the
mixed sets (plus one AND per term and the ORs joining the terms).  For tables up to about 32 by 32 in Python.

  python3 sapair.py <table dir> <n> <cover file> <seconds> <seed>     -> <table dir>/sapair_<seed>.json"""
import json, math, os, random, sys, time
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import gencover, pairsa
from cse import paar

def main():
    d, n, cov, secs, seed = sys.argv[1], int(sys.argv[2]), sys.argv[3], float(sys.argv[4]), int(sys.argv[5])
    rnd = random.Random(seed)
    rows = json.load(open(f'{d}/table.json')); target = sum(rows[u] << (u * n) for u in range(n))
    B = [(frozenset(u for u in range(n) if S >> u & 1), frozenset(n + v for v in range(n) if T >> v & 1)) for S, T in gencover.load_blocks(cov)]
    m = len(B)
    ok = [[not (B[i][0] & B[j][0]) and not (B[i][1] & B[j][1]) for j in range(m)] for i in range(m)]
    def terms(p):
        T = []
        for i in range(m):
            if p[i] == i: T.append((B[i][0], B[i][1]))
            elif i < p[i]: T.append((B[i][0] | B[p[i]][1], B[p[i]][0] | B[i][1]))
        return T
    def cost(p):
        T = terms(p); sets = []
        for a, b in T: sets += [a, b]
        g, _, _ = paar(sets)
        return g + 2 * len(T) - 1
    p = list(range(m)); order = list(range(m)); rnd.shuffle(order)
    for i in order:
        if p[i] != i: continue
        c = [j for j in order if j != i and p[j] == j and ok[i][j]]
        if c: j = rnd.choice(c); p[i] = j; p[j] = i
    cur = cost(p); best = cur; bestp = p[:]
    t0 = time.time(); it = 0
    while time.time() - t0 < secs:
        it += 1
        T = 1.6 * (1 - (time.time() - t0) / secs) + 0.15
        i, k = rnd.sample(range(m), 2)
        if p[i] == k: continue
        j, l = p[i], p[k]; q = p[:]
        for z in {i, j, k, l}: q[z] = z
        if rnd.random() < 0.5: pairs = [(i, k), (j, l)]
        else: pairs = [(i, l), (j, k)]
        good = True
        for a, b in pairs:
            if a == b: continue
            if q[a] != a or q[b] != b or not ok[a][b]: good = False; break
            q[a] = b; q[b] = a
        if not good: continue
        c = cost(q)
        if c <= cur or rnd.random() < math.exp((cur - c) / T):
            p, cur = q, c
            if cur < best: best = cur; bestp = p[:]; print(round(time.time() - t0), 's', best, flush=True)
    # final build with the stronger sharing
    T = terms(bestp); sets = []
    for a, b in T: sets += [a, b]
    bestc = None
    for trial in range(6):
        r2 = random.Random(seed * 100 + trial)
        pre, defs0 = (pairsa.pre_pairs(sets, 4, r2) if trial % 2 else ([set(x) for x in sets], []))
        g, defs, cur_sets = paar([frozenset(x) for x in pre], r2)
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
        for t in range(len(T)):
            x, y = outw[2 * t], outw[2 * t + 1]
            gates.append(('and', min(x, y), max(x, y))); w = 2 * n + len(gates) - 1
            if acc is None: acc = w
            else: gates.append(('or', acc, w)); acc = 2 * n + len(gates) - 1
        if gencover.simulate(n, gates, acc) == target and (bestc is None or len(gates) < len(bestc[0])): bestc = (gates, acc)
    print('moves', it, '| final gates', len(bestc[0]), flush=True)
    json.dump({'gates': bestc[0], 'out': bestc[1]}, open(f'{d}/sapair_{seed}.json', 'w'))
main()
