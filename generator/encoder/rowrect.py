#!/usr/bin/env python3
"""One row "the n by m bipartite graph with mask M has a fan-in-two AND/OR circuit of at most k gates on the
one-a-side promise" (RepSizeAtMost, rectangular mask form), by exact SAT search (msynth.py).
  python3 rowrect.py <step id> <statement file> <out.lean>
exit 0: witness written; 1: no circuit of any size up to the bar (exhaustive): the row is false; 3: undecided"""
import os, re, sys
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(HERE, '..', 'respond'))
from msynth import search
import auto_respond as A
step, sf, out = sys.argv[1:4]
stmt = open(sf).read().strip()
m = re.fullmatch(r'PEqualNP\.Represents\.RepSizeAtMost \(fun \(u : Fin (\d+)\) \(v : Fin (\d+)\) => \((\d+) : ℕ\)\.testBit \((\d+) \* u\.val \+ v\.val\)\) (\d+)', ' '.join(stmt.split()))
if not m or m.group(2) != m.group(4): print('not a row of this family'); sys.exit(3)
n, mm, mask, bar = int(m.group(1)), int(m.group(2)), int(m.group(3)), int(m.group(5))
prom = [((1 << u) | (1 << (n + v)), mask >> (mm * u + v) & 1) for u in range(n) for v in range(mm)]
R = len(prom); incols = [sum(1 << r for r in range(R) if prom[r][0] >> i & 1) for i in range(n + mm)]
target = sum(1 << r for r in range(R) if prom[r][1])
for k in range(1, bar + 1):
    res = search(n + mm, incols, R, [target], k, 'andor', 60)
    if isinstance(res, tuple):
        open(out, 'w').write(A.witness_lean(step, stmt, [(op, [a, b]) for op, a, b in res[0]], res[1][0]))
        print(f'{k} gates for the bar {bar}'); sys.exit(0)
    if res == 'timeout': print(f'undecided at {k} gates'); sys.exit(3)
print(f'no AND/OR circuit of at most {bar} gates (exhaustive search)'); sys.exit(1)
