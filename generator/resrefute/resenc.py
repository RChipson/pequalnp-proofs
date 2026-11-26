#!/usr/bin/env python3
"""Short resolution refutations of the pigeonhole formula PHP(m, n), by SAT.

Lines are clauses; a line is an axiom of the formula or the exact resolvent of two earlier lines
(the project's IsDerivation: R = C minus (v, true) union D minus (v, false)).  All axioms are taken as
lines (the formula is minimally unsatisfiable, so each is needed) and the question is whether k
further resolvents suffice, the last being the empty clause.

  python3 resenc.py cnf <m> <n> <k> <out.cnf>       write the DIMACS file
  python3 resenc.py decode <m> <n> <k> <solver output> <out.json>   read a model, check it, save the refutation

Assumptions that lose nothing: every resolvent but the last is used later; no resolvent holds a
variable in both signs; two consecutive resolvents that do not depend on each other are ordered by
their larger premise."""
import itertools, json, sys

def axioms(m, n):
    var = lambda p, h: p * n + h
    ax = [frozenset(2 * var(p, h) for h in range(n)) for p in range(m)]
    for h in range(n):
        for p in range(m):
            for q in range(p + 1, m): ax.append(frozenset((2 * var(p, h) + 1, 2 * var(q, h) + 1)))
    return ax

class Enc:
    def __init__(self, m, n, k):
        self.m, self.n, self.k = m, n, k; self.ax = axioms(m, n); self.A = len(self.ax); self.NV = m * n; self.NL = 2 * self.NV
        self.nv = 0; self.cls = []
        new = self.new
        self.L = [[new() for _ in range(self.NL)] for _ in range(k)]
        self.s1 = [[new() for _ in range(self.A + r)] for r in range(k)]
        self.s2 = [[new() for _ in range(self.A + r)] for r in range(k)]
        self.pv = [[new() for _ in range(self.NV)] for _ in range(k)]
        self.Aa = [[new() for _ in range(self.NL)] for _ in range(k)]
        self.Bb = [[new() for _ in range(self.NL)] for _ in range(k)]
    def new(self):
        self.nv += 1; return self.nv
    def lit(self, i, l):
        return (l in self.ax[i]) if i < self.A else self.L[i - self.A][l]
    def build(self):
        A, k, NL, NV, c = self.A, self.k, self.NL, self.NV, self.cls
        for r in range(k):
            for sel in (self.s1[r], self.s2[r], self.pv[r]):
                c.append(list(sel))
                for a, b in itertools.combinations(sel, 2): c.append([-a, -b])
            for sel, X in ((self.s1[r], self.Aa[r]), (self.s2[r], self.Bb[r])):
                for i in range(A + r):
                    for l in range(NL):
                        w = self.lit(i, l)
                        if w is True: c.append([-sel[i], X[l]])
                        elif w is False: c.append([-sel[i], -X[l]])
                        else: c.append([-sel[i], -X[l], w]); c.append([-sel[i], X[l], -w])
            for v in range(NV):
                p = self.pv[r][v]; a0, a1, b0, b1 = self.Aa[r][2 * v], self.Aa[r][2 * v + 1], self.Bb[r][2 * v], self.Bb[r][2 * v + 1]
                l0, l1 = self.L[r][2 * v], self.L[r][2 * v + 1]
                c.append([-p, a0]); c.append([-p, b1])
                # l0 <-> (a0 and not p) or b0
                c.append([-l0, a0, b0]); c.append([-l0, -p, b0]); c.append([l0, -a0, p]); c.append([l0, -b0])
                # l1 <-> a1 or (b1 and not p)
                c.append([-l1, a1, b1]); c.append([-l1, a1, -p]); c.append([l1, -a1]); c.append([l1, -b1, p])
                c.append([-l0, -l1])                    # no variable in both signs
        for l in range(NL): c.append([-self.L[k - 1][l]])
        for r in range(k - 1):                          # used later
            w = A + r
            c.append([self.s1[q][w] for q in range(r + 1, k)] + [self.s2[q][w] for q in range(r + 1, k)])
        # order: if resolvent r+1 does not read resolvent r, its larger premise is not smaller
        for r in range(k - 1):
            uses = [self.s1[r + 1][A + r], self.s2[r + 1][A + r]]
            M0 = [self.new() for _ in range(A + r)]; M1 = [self.new() for _ in range(A + r)]
            for i in range(A + r):
                # M0[i] <- some premise of r is >= i   (only this direction is needed)
                for j in range(i, A + r): c.append([-self.s1[r][j], M0[i]]); c.append([-self.s2[r][j], M0[i]])
                # M1[i] -> some premise of r+1 is >= i
                c.append([-M1[i]] + [self.s1[r + 1][j] for j in range(i, A + r + 1)] + [self.s2[r + 1][j] for j in range(i, A + r + 1)])
                c.append([-M0[i], M1[i]] + uses)
        return c

def main():
    cmd, m, n, k = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    e = Enc(m, n, k)
    if cmd == 'cnf':
        c = e.build()
        with open(sys.argv[5], 'w') as f:
            f.write(f'p cnf {e.nv} {len(c)}\n'); f.write('\n'.join(' '.join(map(str, x)) + ' 0' for x in c) + '\n')
        print('variables', e.nv, 'clauses', len(c))
    elif cmd == 'decode':
        mod = set()
        for line in open(sys.argv[5]):
            if line.startswith('v '): mod |= {int(x) for x in line.split()[1:] if int(x) > 0}
        lines = [sorted(a) for a in e.ax]; hints = [None] * e.A
        for r in range(k):
            i = next(x for x in range(e.A + r) if e.s1[r][x] in mod); j = next(x for x in range(e.A + r) if e.s2[r][x] in mod)
            v = next(x for x in range(e.NV) if e.pv[r][x] in mod)
            R = (set(lines[i]) - {2 * v}) | (set(lines[j]) - {2 * v + 1})
            assert 2 * v in lines[i] and 2 * v + 1 in lines[j]
            assert R == {l for l in range(e.NL) if e.L[r][l] in mod}
            lines.append(sorted(R)); hints.append((i, j, v))
        assert lines[-1] == []
        json.dump(dict(m=m, n=n, lines=lines, hints=hints), open(sys.argv[6], 'w'))
        print('refutation with', len(lines), 'lines checked and saved')

if __name__ == '__main__':
    main()
