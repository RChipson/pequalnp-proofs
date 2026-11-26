#!/usr/bin/env python3
"""Promise rows on graphs with equal rows or equal columns: look for an AND/OR/NOT circuit that leaves a
whole class of equal rows (and/or equal columns) unread.  On the promise inputs that class is "none of the
other left (right) inputs is on", so the search runs on fewer inputs: the read rows and columns only.

  python3 unread.py <n> <mask> <k> <seconds>     prints a circuit on the original wire numbers, or none"""
import itertools, sys, time, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'mux'))
import synth_not

def classes(n, mask):
    rows = [tuple(mask >> (n * u + v) & 1 for v in range(n)) for u in range(n)]
    cols = [tuple(mask >> (n * u + v) & 1 for u in range(n)) for v in range(n)]
    def cl(vecs):
        d = {}
        for i, x in enumerate(vecs): d.setdefault(x, []).append(i)
        return list(d.values())
    return cl(rows), cl(cols)

def attempt(n, mask, k, skip_rows, skip_cols, order=True):
    """skip_rows / skip_cols: lists of input indices left unread (each a full class of equal rows / columns, or empty)"""
    keep = [i for i in range(n) if i not in skip_rows] + [n + j for j in range(n) if j not in skip_cols]
    pos = {w: i for i, w in enumerate(keep)}
    S = synth_not.Synth(len(keep), k, order)
    seen = set()
    for u in range(n):
        for v in range(n):
            x = 0
            if u not in skip_rows: x |= 1 << pos[u]
            if v not in skip_cols: x |= 1 << pos[n + v]
            o = bool(mask >> (n * u + v) & 1)
            if (x, o) in seen: continue
            seen.add((x, o)); S.add_row(x, o)
    g = S.solve()
    if not g: return None
    m = len(keep)
    def w(i): return keep[i] if i < m else 2 * n + (i - m)
    return [(t, w(a), w(b)) for t, a, b in g]

def check(n, mask, gates):
    for u in range(n):
        for v in range(n):
            x = (1 << u) | (1 << (n + v))
            if synth_not.evalc(2 * n, gates, x) != bool(mask >> (n * u + v) & 1): return False
    return True

if __name__ == '__main__':
    n, mask, k = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    rc, cc = classes(n, mask)
    opts_r = [[]] + [c for c in rc]; opts_c = [[]] + [c for c in cc]
    which = sys.argv[4] if len(sys.argv) > 4 else 'twins'
    if which == 'twins': opts_r = [c for c in rc if len(c) > 1] or [[]]; opts_c = [c for c in cc if len(c) > 1] or [[]]
    for sr in opts_r:
        for sc in opts_c:
            t = time.time(); g = attempt(n, mask, k, sr, sc)
            print(n, mask, k, 'unread rows', sr, 'cols', sc, ('CIRCUIT ' + repr(g) + ' ok=' + str(check(n, mask, g))) if g else 'none', round(time.time() - t, 1), flush=True)
            if g: sys.exit(0)
