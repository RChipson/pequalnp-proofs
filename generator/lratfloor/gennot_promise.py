#!/usr/bin/env python3
"""CNF of the library formula  LinkN.enc2 (n + m) s (Promise.gMask n m M) (Promise.repRows n m):
"some AND/OR/NOT circuit of fan-in two with at most s gates represents the n by m graph with mask M on the
one-a-side promise".  This is the project's own notes/data/lrat-link/gennot.py with the function and the row
list replaced by the promise ones; clause order as in the Lean definition, so that a solver's certificate
for this file can be replayed against the Lean formula.
Usage: gennot_promise.py n m M s out.cnf"""
import sys
n0, m0, MASK, s = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
out = sys.argv[5]
n = n0 + m0
drop = {'lex'}
R = 1 << n
A = R + n + s + 2
def log2(x): return x.bit_length() - 1 if x > 0 else 0
def g(r): return (MASK >> (m0 * log2(r % (1 << n0)) + log2(r >> n0))) & 1 == 1
ROWS = [(1 << u) + (1 << (n0 + v)) for u in range(n0) for v in range(m0)]
print('rows', ROWS, file=sys.stderr)
def ix(kd, j, a): return (kd * (s + 1) + j) * A + a
def P(v): return v + 1
def Q(v): return -(v + 1)
def L(v, b): return P(v) if b else Q(v)
def bit(r, k): return (r >> k) & 1 == 1
F = []
# fOp
for j in range(s): F.append([P(ix(0, j, 0)), P(ix(0, j, 1)), P(ix(0, j, 2)), P(ix(0, j, 3))])
# fSrcAlo
for sd in (1, 2):
    for j in range(s): F.append([P(ix(sd, j, k)) for k in range(n + j + 1)])
# fSrcEq
for sd in (1, 2):
    for j in range(s):
        for r in ROWS:
            for k in range(n + j + 1):
                if k < n: F.append([Q(ix(sd, j, k)), L(ix(sd + 3, j, r), bit(r, k))])
                elif k < n + j:
                    F.append([Q(ix(sd, j, k)), Q(ix(sd + 3, j, r)), P(ix(3, k - n, r))])
                    F.append([Q(ix(sd, j, k)), P(ix(sd + 3, j, r)), Q(ix(3, k - n, r))])
                else: F.append([Q(ix(sd, j, k)), Q(ix(sd + 3, j, r))])
# fGate
for j in range(s):
    for r in ROWS:
        o0, o1, o2 = ix(0, j, 0), ix(0, j, 1), ix(0, j, 2)
        w, u1, u2 = ix(3, j, r), ix(4, j, r), ix(5, j, r)
        F += [[Q(o0), Q(w), P(u1)], [Q(o0), Q(w), P(u2)], [Q(o0), P(w), Q(u1), Q(u2)],
              [Q(o1), P(w), Q(u1)], [Q(o1), P(w), Q(u2)], [Q(o1), Q(w), P(u1), P(u2)],
              [Q(o2), P(w)], [Q(ix(0, j, 3)), P(w), P(u1)], [Q(ix(0, j, 3)), Q(w), Q(u1)]]
# fOutAlo
F.append([P(ix(6, 0, k)) for k in range(n + s + 1)])
# fOutEq
for r in ROWS:
    for k in range(n + s + 1):
        if k < n:
            if bit(r, k) != g(r): F.append([Q(ix(6, 0, k))])
        elif k < n + s: F.append([Q(ix(6, 0, k)), L(ix(3, k - n, r), g(r))])
        elif g(r): F.append([Q(ix(6, 0, k))])
# symmetry / normal form
pad = lambda j: ix(7, j, 0)
if 'out' not in drop:
    F.append([P(ix(6, 0, n + s - 1)), P(pad(s - 1))])
if 'pad' not in drop:
    for j in range(s):
        F += [[Q(pad(j)), P(ix(0, j, 2))], [Q(pad(j)), P(ix(1, j, n + j))], [Q(pad(j)), P(ix(2, j, n + j))],
              [P(pad(j)), Q(ix(0, j, 2))], [P(pad(j)), Q(ix(1, j, n + j))], [P(pad(j)), Q(ix(2, j, n + j))]]
if 'pre' not in drop:
    for j in range(s - 1): F.append([Q(pad(j + 1)), P(pad(j))])
if 'padrd' not in drop:
    for j in range(s):
        for i in range(j):
            F += [[Q(pad(i)), Q(ix(1, j, n + i))], [Q(pad(i)), Q(ix(2, j, n + i))]]
if 'ord' not in drop:
    for j in range(s):
        for k in range(n + j + 1):
            for l in range(k + 1):
                F.append([Q(ix(1, j, k)), Q(ix(2, j, l)), P(pad(j))] + ([P(ix(0, j, 3))] if l == k else []))
if 'used' not in drop:
    for j in range(s - 1):
        F.append([P(ix(1, i, n + j)) for i in range(j + 1, s)] + [P(ix(2, i, n + j)) for i in range(j + 1, s)] + [P(pad(j))])
for j in range(s):
    for k in range(n + j + 1): F.append([Q(ix(0, j, 3)), Q(ix(1, j, k)), P(ix(2, j, k))])
for j in range(s):
    for i in range(j): F.append([Q(ix(0, j, 3)), Q(ix(0, i, 3)), Q(ix(1, j, n + i))])
if 'inc' in drop:
    for j in range(s):
        for r in ROWS:
            d1, d2, u1, u2 = ix(8, j, r), ix(9, j, r), ix(4, j, r), ix(5, j, r)
            F += [[Q(d1), P(u1)], [Q(d1), Q(u2)], [Q(d2), Q(u1)], [Q(d2), P(u2)]]
        F.append([P(ix(8, j, r)) for r in ROWS] + [P(pad(j))])
        F.append([P(ix(9, j, r)) for r in ROWS] + [P(pad(j))])
if 'lex' in drop:
    for j in range(s - 1):
        base = [P(pad(j)), P(ix(1, j + 1, n + j)), P(ix(2, j + 1, n + j))]
        for a in range(n + j + 1):
            for b in range(a):
                F.append([Q(ix(1, j, a)), Q(ix(1, j + 1, b))] + base)
            for c in range(n + j + 1):
                for d in range(c):
                    F.append([Q(ix(1, j, a)), Q(ix(1, j + 1, a)), Q(ix(2, j, c)), Q(ix(2, j + 1, d))] + base)
                F.append([Q(ix(1, j, a)), Q(ix(1, j + 1, a)), Q(ix(2, j, c)), Q(ix(2, j + 1, c)), Q(ix(0, j, 1))] + base)
                F.append([Q(ix(1, j, a)), Q(ix(1, j + 1, a)), Q(ix(2, j, c)), Q(ix(2, j + 1, c)), Q(ix(0, j + 1, 0))] + base)
nv = 10 * (s + 1) * A
with open(out, 'w') as o:
    o.write(f'p cnf {nv} {len(F)}\n')
    for c in F: o.write(' '.join(map(str, c)) + ' 0\n')
print(f'vars={nv} clauses={len(F)}', file=sys.stderr)
