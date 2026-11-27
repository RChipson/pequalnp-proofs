#!/usr/bin/env python3
"""Build and check the circuit for a cover-with-pairing found by jointsa (lines "B S S T T partner"), and keep
it as the table's best if it is smaller than what is held.
  python3 joint_build.py <table dir> <n> <joint file> [tries]"""
import json, os, random, sys
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import gencover, pairsa
from cse import paar
d, n, jf = sys.argv[1], int(sys.argv[2]), sys.argv[3]; tries = int(sys.argv[4]) if len(sys.argv) > 4 else 6
rows = json.load(open(f'{d}/table.json')); target = sum(rows[u] << (u * n) for u in range(n))
B = []; P = []
for l in open(jf):
    q = l.split()
    if q and q[0] == 'B': B.append((int(q[1] + q[2], 16), int(q[3] + q[4], 16))); P.append(int(q[5]) if len(q) > 5 else len(P))
bits = lambda S, off: {off + i for i in range(n) if S >> i & 1}
T = []
for i, (S, Tm) in enumerate(B):
    if S == 0: continue
    if P[i] == i: T.append((bits(S, 0), bits(Tm, n)))
    elif i < P[i]: T.append((bits(S, 0) | bits(B[P[i]][1], n), bits(B[P[i]][0], 0) | bits(Tm, n)))
sets = []
for a, b in T: sets += [frozenset(a), frozenset(b)]
best = None
for t in range(tries):
    r = random.Random(t)
    pre, defs0 = (pairsa.pre_pairs(sets, 3 if n <= 32 else 30, r) if t % 3 == 2 else ([set(x) for x in sets], []))
    g, defs, cur = paar([frozenset(x) for x in pre], r if t else None)
    gates = []; wire = {i: i for i in range(2 * n)}
    for z, a, b in defs0 + defs:
        gates.append(('or', wire[a], wire[b])); wire[z] = 2 * n + len(gates) - 1
    outw = []; memo = {}
    for s in cur:
        k = frozenset(s)
        if k not in memo:
            l = sorted(wire[i] for i in s); w = l[0]
            for x in l[1:]:
                gates.append(('or', min(w, x), max(w, x))); w = 2 * n + len(gates) - 1
            memo[k] = w
        outw.append(memo[k])
    acc = None
    for t2 in range(len(T)):
        x, y = outw[2 * t2], outw[2 * t2 + 1]
        gates.append(('and', min(x, y), max(x, y))); w = 2 * n + len(gates) - 1
        if acc is None: acc = w
        else: gates.append(('or', acc, w)); acc = 2 * n + len(gates) - 1
    if gencover.simulate(n, gates, acc) == target and (best is None or len(gates) < len(best[0])): best = (gates, acc)
if best is None: print('no correct circuit built'); sys.exit(1)
held = json.load(open(f'{d}/best.json'))['gates']
print('circuit', len(best[0]), 'gates | held before', held)
if len(best[0]) < held:
    json.dump({'gates': best[0], 'out': best[1]}, open(f'{d}/best_circuit.json.new', 'w')); os.replace(f'{d}/best_circuit.json.new', f'{d}/best_circuit.json')
    json.dump({'gates': len(best[0]), 'circuit': 'best_circuit.json'}, open(f'{d}/best.json.new', 'w')); os.replace(f'{d}/best.json.new', f'{d}/best.json')
    print('kept as the best for this table')
