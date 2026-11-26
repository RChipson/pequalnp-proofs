#!/usr/bin/env python3
"""Exact search (SAT) for circuits of AND, OR (fan-in two) and NOT gates, every gate counted.

  python3 synth_not.py mux <address bits> <gates> [seconds]
The function is the multiplexer of the project's row: inputs x0..x(a-1) are the address (x0 the
least significant bit), then 2^a data bits; the output is the addressed data bit.
For many inputs the rows are added on demand: a circuit is found for a subset of the inputs,
checked on all of them, and a failing input is added (so an answer "circuit" is always checked
on every input; an answer "none" means no circuit exists for the rows used, hence none at all)."""
import itertools, random, sys, time
from pysat.solvers import Cadical153

def mux_fn(a):
    n = a + (1 << a)
    def f(x):
        idx = sum(((x >> i) & 1) << i for i in range(a))
        return bool(x >> (a + idx) & 1)
    return n, f

class Synth:
    def __init__(self, n, k, order=False):
        self.n, self.k = n, k; self.nv = 0; self.s = Cadical153()
        self.typ = []; self.sa = []; self.sb = []
        for g in range(k):
            t = [self.new() for _ in range(3)]            # and, or, not
            self.s.add_clause(t)
            for x, y in itertools.combinations(t, 2): self.s.add_clause([-x, -y])
            a = [self.new() for _ in range(n + g)]; b = [self.new() for _ in range(n + g)]
            for sel in (a, b):
                self.s.add_clause(sel)
                for x, y in itertools.combinations(sel, 2): self.s.add_clause([-x, -y])
            # symmetry: for AND/OR the first operand is the smaller wire; for NOT the second equals the first
            for i in range(n + g):
                for j in range(n + g):
                    if i >= j: self.s.add_clause([t[2], -a[i], -b[j]])
                    if i != j: self.s.add_clause([-t[2], -a[i], -b[j]])
            self.typ.append(t); self.sa.append(a); self.sb.append(b)
        # order: two neighbouring gates where the later does not read the earlier could be swapped, so ask the
        # earlier one to have the smaller pair (second operand, first operand).  Any circuit can be sorted so.
        if order:
            for g in range(k - 1):
                W = n + g
                u = [self.sa[g + 1][W], self.sb[g + 1][W]]
                for i in range(W):
                    for j in range(i):
                        self.s.add_clause(u + [-self.sb[g][i], -self.sb[g + 1][j]])
                    for p_ in range(W):
                        for q in range(p_):
                            self.s.add_clause(u + [-self.sb[g][i], -self.sb[g + 1][i], -self.sa[g][p_], -self.sa[g + 1][q]])
        # every gate except the last is used by a later gate
        for g in range(k - 1):
            w = n + g
            self.s.add_clause([self.sa[h][w] for h in range(g + 1, k)] + [self.sb[h][w] for h in range(g + 1, k)])
    def new(self):
        self.nv += 1; return self.nv
    def add_row(self, x, out):
        n, k = self.n, self.k
        val = [bool(x >> i & 1) for i in range(n)]
        for g in range(k):
            A = self.new(); B = self.new(); v = self.new()
            for i in range(n + g):
                for sel, X in ((self.sa[g][i], A), (self.sb[g][i], B)):
                    w = val[i]
                    if w is True: self.s.add_clause([-sel, X])
                    elif w is False: self.s.add_clause([-sel, -X])
                    else: self.s.add_clause([-sel, -X, w]); self.s.add_clause([-sel, X, -w])
            ta, to, tn = self.typ[g]
            for cl in ([-ta, -v, A], [-ta, -v, B], [-ta, v, -A, -B], [-to, v, -A], [-to, v, -B], [-to, -v, A, B], [-tn, v, A], [-tn, -v, -A]):
                self.s.add_clause(cl)
            val.append(v)
        self.s.add_clause([val[-1] if out else -val[-1]])
    def solve(self):
        if not self.s.solve(): return None
        mod = set(l for l in self.s.get_model() if l > 0)
        gates = []
        for g in range(self.k):
            t = ['and', 'or', 'not'][next(i for i in range(3) if self.typ[g][i] in mod)]
            a = next(i for i, v in enumerate(self.sa[g]) if v in mod); b = next(i for i, v in enumerate(self.sb[g]) if v in mod)
            gates.append((t, a, b))
        return gates

def evalc(n, gates, x):
    w = [bool(x >> i & 1) for i in range(n)]
    for t, a, b in gates: w.append((w[a] and w[b]) if t == 'and' else (w[a] or w[b]) if t == 'or' else (not w[a]))
    return w[-1]

def search(n, f, k, seconds, seed=1):
    rnd = random.Random(seed); S = Synth(n, k); t0 = time.time()
    rows = set()
    for x in rnd.sample(range(1 << n), min(1 << n, 48)): S.add_row(x, f(x)); rows.add(x)
    while time.time() - t0 < seconds:
        g = S.solve()
        if g is None: return 'none', len(rows)
        bad = [x for x in range(1 << n) if evalc(n, g, x) != f(x)]
        if not bad: return 'circuit', g
        for x in rnd.sample(bad, min(len(bad), 12)): S.add_row(x, f(x)); rows.add(x)
    return 'timeout', len(rows)

if __name__ == '__main__':
    a, k = int(sys.argv[2]), int(sys.argv[3]); secs = int(sys.argv[4]) if len(sys.argv) > 4 else 600
    n, f = mux_fn(a)
    t0 = time.time(); r = search(n, f, k, secs); print(r, '%.1f s' % (time.time() - t0))
