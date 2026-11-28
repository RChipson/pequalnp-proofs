#!/usr/bin/env python3
"""Rows "The two-lit function of the graph H on n points with mask M on shared wires has an AND/OR(/NOT) circuit of
fan-in two with at most k gates": a search aimed at the bar, with the usual shapes first.

Inputs have one or two points lit.  The circuits that exist are mostly covers by rectangles (ORs of points, then
ANDs of those, then ORs joining the ANDs), either for the function itself or, when NOT gates are allowed, for its
complement with one NOT gate at the end.  This program looks for such a circuit with exactly k gates (then k - 1).

  python3 twolit2.py <step id> <statement file> <out.lean> [seconds per search, default 12]
exit 0: witness written; 3: none found in the time (the row is NOT thereby shown false)"""
import os, re, sys
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, os.path.join(HERE, '..', 'encoder')); sys.path.insert(0, os.path.join(HERE, '..', 'respond'))
from msynth import search
import auto_respond as A
PAT = re.compile(r'∃ C : PEqualNP\.CircuitLowerBounds\.Circuit, PEqualNP\.MetaComplexity\.(FanInTwo|Monotone2) C ∧ C\.size ≤ (\d+) ∧ ∀ i j : Fin (\d+), C\.eval \(List\.ofFn fun k : Fin (\d+) => decide \(k = i ∨ k = j\)\) = \((\d+) : ℕ\)\.testBit \((\d+) \* min i\.val j\.val \+ max i\.val j\.val\)')

def shaped(n, rows, target, k, secs):
    """a circuit of exactly k gates: p ORs of inputs, q ANDs of those (or of inputs), q - 1 ORs joining; or None"""
    R = len(rows); incols = [sum(1 << r for r, x in enumerate(rows) if x >> i & 1) for i in range(n)]
    for q in range(1, k // 2 + 2):
        pp = k - 2 * q + 1
        if pp < 0: break
        def extra(L, pp=pp, q=q):
            cl = []; op, sa, sb = L['op'], L['sa'], L['sb']
            for g in range(k):
                isand = pp <= g < pp + q
                cl.append([op[g]] if isand else [-op[g]])
                for j in range(n + g):
                    if isand and j >= n + pp: cl += [[-sa[g][j]], [-sb[g][j]]]
                    if g >= pp + q and j < n + pp: cl += [[-sa[g][j]], [-sb[g][j]]]
            return cl
        res = search(n, incols, R, [target], k, 'andor', secs, 0, extra)
        if isinstance(res, tuple): return res[0], res[1][0]
    return None

def find(n, mask, bar, nots, secs=12):
    rows = [(1 << i) | (1 << j) for i in range(n) for j in range(i, n)]
    val = [mask >> (n * i + j) & 1 for i in range(n) for j in range(i, n)]
    target = sum(1 << r for r, v in enumerate(val) if v); full = (1 << len(rows)) - 1
    def ok(gates, outw):
        for x, want in zip(rows, val):
            w = [bool(x >> i & 1) for i in range(n)]
            for op, ins in gates: w.append((w[ins[0]] and w[ins[1]]) if op == 'and' else (w[ins[0]] or w[ins[1]]) if op == 'or' else (not w[ins[0]]))
            if w[outw] != bool(want): return False
        return True
    for k in (bar, bar - 1):
        r = shaped(n, rows, target, k, secs)
        if r:
            g = [(op, [a, b]) for op, a, b in r[0]]
            if ok(g, r[1]): return g, r[1], f'{k} gates'
        if nots and k - 1 >= 1:
            r = shaped(n, rows, target ^ full, k - 1, secs)
            if r:
                g = [(op, [a, b]) for op, a, b in r[0]] + [('not', [r[1]])]
                if ok(g, n + len(g) - 1): return g, n + len(g) - 1, f'{k} gates (the complement and one NOT)'
    return None

if __name__ == '__main__':
    step, sf, out = sys.argv[1:4]; secs = float(sys.argv[4]) if len(sys.argv) > 4 else 12
    stmt = open(sf).read().strip()
    m = PAT.fullmatch(' '.join(stmt.split()))
    if not m or len({m.group(3), m.group(4), m.group(6)}) != 1: print('not a row of this family'); sys.exit(3)
    n, mask, bar, nots = int(m.group(3)), int(m.group(5)), int(m.group(2)), m.group(1) == 'FanInTwo'
    r = find(n, mask, bar, nots, secs)
    if not r: print(f'no circuit of at most {bar} gates found in the time'); sys.exit(3)
    open(out, 'w').write(A.witness_lean(step, stmt, r[0], r[1]))
    print(r[2], 'for the bar', bar); sys.exit(0)
