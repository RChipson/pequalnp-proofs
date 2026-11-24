"""Search for an AND-count circuit (step L-meta-1992): N AND gates, each the AND of two
sides, a side being an OR of bare variables and earlier gates; the output is an OR of gates.
Each variable may be bare in at most two gates.  The circuit must be false on each listed
set, and true on each listed set of size three with one more vertex added.
Usage: python3 sat_andcount.py <N> [max bare count, default 2]
"""
import sys, itertools, time
from pysat.solvers import Cadical153
from pysat.card import CardEnc, EncType

N = int(sys.argv[1]); CAP = int(sys.argv[2]) if len(sys.argv) > 2 else 2
n = 10
SETS = [50, 69, 104, 116, 138, 201, 208, 276, 385, 402, 521, 548, 554, 770, 773]
pts = []
for m in SETS:
    U = {v for v in range(n) if m >> v & 1}
    pts.append((frozenset(U), False))
    if len(U) == 3:
        for w in range(n):
            if w not in U: pts.append((frozenset(U | {w}), True))
cnt = [0]
def new():
    cnt[0] += 1; return cnt[0]
cls = []
LV = {(i, v): new() for i in range(N) for v in range(n)}
RV = {(i, v): new() for i in range(N) for v in range(n)}
LG = {(i, j): new() for i in range(N) for j in range(i)}
RG = {(i, j): new() for i in range(N) for j in range(i)}
OG = {i: new() for i in range(N)}
val = {(i, p): new() for i in range(N) for p in range(len(pts))}
def equiv_or(x, lits):
    for l in lits: cls.append([-l, x])
    cls.append([-x] + lits)
def and2(a, b):
    x = new(); cls.extend([[-x, a], [-x, b], [x, -a, -b]]); return x
for p, (U, want) in enumerate(pts):
    outs = []
    for i in range(N):
        sides = []
        for V, G in ((LV, LG), (RV, RG)):
            s = new()
            equiv_or(s, [V[i, v] for v in U] + [and2(G[i, j], val[j, p]) for j in range(i)])
            sides.append(s)
        cls.extend([[-val[i, p], sides[0]], [-val[i, p], sides[1]], [val[i, p], -sides[0], -sides[1]]])
        outs.append(and2(OG[i], val[i, p]))
    if want: cls.append(outs)
    else: cls.extend([[-o] for o in outs])
for v in range(n):
    bare = []
    for i in range(N):
        b = new(); equiv_or(b, [LV[i, v], RV[i, v]]); bare.append(b)
    enc = CardEnc.atmost(lits=bare, bound=CAP, top_id=cnt[0], encoding=EncType.seqcounter)
    cnt[0] = max(cnt[0], enc.nv); cls.extend(enc.clauses)
print(f'N={N} cap={CAP} points={len(pts)} variables={cnt[0]} clauses={len(cls)}', flush=True)
t0 = time.time()
s = Cadical153(bootstrap_with=cls)
ok = s.solve()
print(f'result={"SAT" if ok else "UNSAT"} time={time.time()-t0:.0f}s', flush=True)
if ok:
    m = set(x for x in s.get_model() if x > 0)
    for i in range(N):
        print('GATE', i, 'L vars', [v for v in range(n) if LV[i, v] in m], 'gates', [j for j in range(i) if LG[i, j] in m],
              '| R vars', [v for v in range(n) if RV[i, v] in m], 'gates', [j for j in range(i) if RG[i, j] in m], flush=True)
    print('OUT gates', [i for i in range(N) if OG[i] in m], flush=True)
