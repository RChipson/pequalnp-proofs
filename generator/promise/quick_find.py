#!/usr/bin/env python3
"""A "find" row of the promise family, settled quickly if possible.
  python3 quick_find.py <step id> <statement file> <out.lean>
exit 0: a circuit was found and the proof written;
exit 1: the exhaustive search (genprom.circuit, every size up to the bar) ended without a circuit: the row is false;
exit 3: undecided (the bar is above 7 gates and none of the quick shapes of xorsynth.py fits)."""
import os, sys
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(HERE, '..', 'mux'))
import genprom, unread, xorsynth
step, sf, out = sys.argv[1:4]
stmt = open(sf).read().strip(); p = genprom.parse(' '.join(stmt.split()))
if not p: print('not a row of this family'); sys.exit(3)
n, mask, bar = p
g = None
if bar >= 8: g = xorsynth.find(n, mask, bar, 25)          # the quick shapes first: most rows with a high bar fall to them
if not g:
    for k in range(1, min(bar, 7) + 1):
        g = genprom.circuit(n, mask, k)
        if g: break
if not g and bar >= 8: g = xorsynth.find(n, mask, bar, 25)
if g and unread.check(n, mask, g):
    open(out, 'w').write(genprom.lean(step, stmt, n, g)); print(f'{len(g)} gates for the bar {bar}'); sys.exit(0)
if bar <= 7: print(f'no circuit with at most {bar} gates (exhaustive search)'); sys.exit(1)
print('undecided: no circuit of up to 7 gates and none of the quick shapes'); sys.exit(3)
