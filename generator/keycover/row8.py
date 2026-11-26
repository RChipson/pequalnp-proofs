#!/usr/bin/env python3
"""One row "the n by n graph with mask M is represented on the one-a-side promise by an AND/OR circuit of fan-in
two with at most k gates": build a circuit with mixed.py and, if it meets the bar, write the witness proof.
  python3 row8.py <step id> <statement file> <out.lean>      exit 0: written; 3: our circuit is above the bar"""
import os, re, sys
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(HERE, '..', 'respond'))
import mixed, auto_respond as A
step, sf, out = sys.argv[1:4]
stmt = open(sf).read().strip()
m = re.fullmatch(r'PEqualNP\.Represents\.RepSizeAtMost \(fun u v : Fin (\d+) => \((\d+) : ℕ\)\.testBit \((\d+) \* u\.val \+ v\.val\)\) (\d+)', ' '.join(stmt.split()))
if not m or m.group(1) != m.group(3) or int(m.group(1)) > 16: print('not a row of this family'); sys.exit(3)
n, mask, bar = int(m.group(1)), int(m.group(2)), int(m.group(4))
best = None
for seed in (1, 2):
    c = mixed.best(n, mask, 6, 5.0, seed)
    if c and (best is None or len(c[0]) < len(best[0])): best = c
    if best and len(best[0]) <= bar: break
if not best or len(best[0]) > bar: print(f'our circuit has {len(best[0]) if best else "no"} gates, the bar is {bar}'); sys.exit(3)
open(out, 'w').write(A.witness_lean(step, stmt, [(op, [a, b]) for op, a, b in best[0]], best[1]))
print(f'{len(best[0])} gates for the bar {bar}'); sys.exit(0)
