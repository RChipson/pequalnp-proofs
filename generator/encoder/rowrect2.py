#!/usr/bin/env python3
"""One row "the n by m bipartite graph with mask M has a fan-in-two AND/OR circuit of at most k gates on the
one-a-side promise" (RepSizeAtMost, rectangular mask form): a search aimed at the bar itself.

rowrect.py looks for the least circuit, size by size, and gives up at the first size it cannot settle.  A row
only asks for SOME circuit within its bar, and the circuits that exist usually have the shape of a cover by
rectangles: ORs of inputs first, then ANDs of those, then ORs joining the ANDs.  This program looks for a circuit of
that shape with exactly `bar` gates (then bar - 1, bar - 2), and after that for any circuit of `bar` gates.

  python3 rowrect2.py <step id> <statement file> <out.lean> [seconds per search, default 20]
exit 0: witness written; 3: none found in the time (the row is NOT thereby shown false)"""
import os, re, sys
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(HERE, '..', 'respond'))
from msynth import search
import auto_respond as A

def find(n, mm, mask, bar, secs=20):
    prom = [((1 << u) | (1 << (n + v)), mask >> (mm * u + v) & 1) for u in range(n) for v in range(mm)]
    R = len(prom); N = n + mm
    incols = [sum(1 << r for r in range(R) if prom[r][0] >> i & 1) for i in range(N)]
    target = sum(1 << r for r in range(R) if prom[r][1])
    def ok(gates, outw):
        for x, want in prom:
            w = [bool(x >> i & 1) for i in range(N)]
            for op, a, b in gates: w.append((w[a] and w[b]) if op == 'and' else (w[a] or w[b]))
            if w[outw] != bool(want): return False
        return True
    for k in (bar, bar - 1, bar - 2):
        if k < 1: continue
        for q in range(1, k // 2 + 2):
            pp = k - 2 * q + 1
            if pp < 0: break
            def extra(L, pp=pp, q=q, k=k):
                cl = []; op, sa, sb = L['op'], L['sa'], L['sb']
                for g in range(k):
                    isand = pp <= g < pp + q
                    cl.append([op[g]] if isand else [-op[g]])
                    for j in range(N + g):
                        if isand and j >= N + pp: cl += [[-sa[g][j]], [-sb[g][j]]]
                        if g >= pp + q and j < N + pp: cl += [[-sa[g][j]], [-sb[g][j]]]
                return cl
            res = search(N, incols, R, [target], k, 'andor', secs, 0, extra)
            if isinstance(res, tuple) and ok(res[0], res[1][0]): return res[0], res[1][0], f'{k} gates, {q} rectangles'
    res = search(N, incols, R, [target], bar, 'andor', 3 * secs, 0)
    if isinstance(res, tuple) and ok(res[0], res[1][0]): return res[0], res[1][0], f'{bar} gates'
    return None

if __name__ == '__main__':
    step, sf, out = sys.argv[1:4]; secs = float(sys.argv[4]) if len(sys.argv) > 4 else 20
    stmt = open(sf).read().strip()
    m = re.fullmatch(r'PEqualNP\.Represents\.RepSizeAtMost \(fun \(u : Fin (\d+)\) \(v : Fin (\d+)\) => \((\d+) : ℕ\)\.testBit \((\d+) \* u\.val \+ v\.val\)\) (\d+)', ' '.join(stmt.split()))
    if not m or m.group(2) != m.group(4): print('not a row of this family'); sys.exit(3)
    n, mm, mask, bar = int(m.group(1)), int(m.group(2)), int(m.group(3)), int(m.group(5))
    r = find(n, mm, mask, bar, secs)
    if not r: print(f'no circuit of at most {bar} gates found in the time'); sys.exit(3)
    open(out, 'w').write(A.witness_lean(step, stmt, [(op, [a, b]) for op, a, b in r[0]], r[1]))
    print(r[2], 'for the bar', bar); sys.exit(0)
