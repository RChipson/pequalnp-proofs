#!/usr/bin/env python3
"""One sweep over the open "find" rows of the promise family that have no pull request: prepare the proof
with the responder's handlers and send it.  Several copies can run side by side on different rows:
  python3 generator/respond/sweep.py <worker index> <workers> <lowest step number>"""
import json, os, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import auto_respond as A
wi, nw, lo = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
G = A.gaps()
q = json.load(open(A.RETRY)) if os.path.exists(A.RETRY) else {}
rows = sorted((i for i, g in G.items() if 'is represented on the one-a-side promise' in g.get('title', '') and A.num(i) >= lo
               and A.is_open(g) and i not in q and A.num(i) % nw == wi), key=A.num)
A.log(f'[{wi}]', len(rows), 'rows')
for step in rows:
    if os.path.exists(f'{A.D}/{step}.swept'): continue
    open(f'{A.D}/{step}.swept', 'w').write('1')
    try: g = A.gaps().get(step)
    except Exception: g = G[step]
    if not A.is_open(g): A.log(f'[{wi}]', step, 'already taken'); continue
    t = time.time(); out = A.h_find(step, g, g['statement'].strip())
    if not out: A.log(f'[{wi}]', step, 'no circuit found quickly', round(time.time() - t)); continue
    A.send(step, out)
A.log(f'[{wi}] sweep done')
