#!/usr/bin/env python3
"""L-meta-1342, range 1 (three or more junk AND gates): exhaustive search, by SAT, for a top-form
fan-in-two AND/OR circuit with at most 21 gates computing the edge function of the 11-vertex graph.

WHAT IS SEARCHED.  Circuits in the model of the project's TopForm definitions: every gate is AND
or OR, reads exactly two earlier wires (repetitions allowed).  F is the edge function.  A gate is
BELOW F when it is true only where F is true.  A JUNK gate is an AND gate not below F.  TOP FORM:
no AND gate below F lies strictly inside the cone of an AND gate.

TESTS.  All wires are monotone functions, so a wire is below F exactly when it is false on every
maximal independent set, and a circuit computes F exactly when it is true on every edge (both
ends true, the rest false) and false on every maximal independent set.  So every wire is replaced
by its values on the 16 edges and the 24 maximal independent sets.

NORMAL FORM (proved in the comments of normal_form() below).  If a top-form circuit with at most
21 gates and at least three junk gates computes F, then for some t >= 1 and m >= 0 with
m + 2t - 1 <= 21 there are
  * a BOTTOM of m gates (AND/OR over the inputs and earlier bottom gates), every bottom AND gate
    junk, every bottom gate read by a later bottom gate or by a top, the test vectors of all
    bottom wires and inputs pairwise different, the gates in co-lexicographic order;
  * t TOPS, each the AND of two different bottom wires or inputs, each false on every maximal
    independent set, together true on every edge;
  * at least max(0, m + 2t - 19) AND gates in the bottom.
This program decides, for every such (t, m), whether such an object exists.  All answers "no"
means the range holds no circuit.  A "yes" prints the object, from which the circuit is read off.

STATUS (25 Nov 2026): correct on the self-tests (a five-cycle: seven gates found, six refused), but
far too slow on the real graph: of the 121 cases only (t, m) = (9, 4) was settled (no) in the time
tried; (8, 6) and the 22-gate sanity case (7, 9) did not finish in nine minutes.  The range was
NOT exhausted and nothing was reported as exhausted.  The step was handed back as out_of_time.

  python3 topform_sat.py list                 print the cases (t, m, least number of bottom ANDs)
  python3 topform_sat.py one <t> <m> [minand] decide one case (minand overrides, for self-tests)
"""
import itertools, sys, time
from pysat.solvers import Cadical153
from pysat.card import CardEnc, EncType

import os
N = 11
EDGES = [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
B_PROJECT = [15, 29, 43, 57, 71, 85, 99, 113, 135, 149, 163, 177, 269, 325, 389, 526, 540, 582, 596, 1066, 1186, 1288, 1408, 1546]
TOTAL = 21
SELFTEST = os.environ.get('SELFTEST')      # self-tests on a small graph: n:u-v,u-v,...
if SELFTEST:
    N = int(SELFTEST.split(':')[0]); EDGES = [tuple(map(int, e.split('-'))) for e in SELFTEST.split(':')[1].split(',')]
EXTRA_COLUMNS = os.environ.get('EXTRA', '1') == '1'

def maximal_independent_sets():
    adj = [0] * N
    for u, v in EDGES: adj[u] |= 1 << v; adj[v] |= 1 << u
    ind = [s for s in range(1 << N) if all(not (adj[i] & s) for i in range(N) if s >> i & 1)]
    return sorted(s for s in ind if all((s >> i & 1) or (adj[i] & s) for i in range(N)))

MIS = maximal_independent_sets()
assert SELFTEST or MIS == sorted(B_PROJECT), 'the maximal independent sets differ from the list in the checked reduction'
# test k < NE: edge k; then the maximal independent sets (these are the BASE columns, NB of them);
# then, only to help the solver, every other non-empty independent set: a real circuit has a value
# there too, an AND/OR gate acts on it in the same way, and a top is false there as well.
OTHER = sorted(s for s in range(1, 1 << N) if s not in MIS and any((s & M) == s for M in MIS)) if EXTRA_COLUMNS else []
TESTS = [(1 << u) | (1 << v) for u, v in EDGES] + MIS + OTHER
NE, NB, NT = len(EDGES), len(EDGES) + len(MIS), len(TESTS)
INVEC = [[bool(TESTS[k] >> i & 1) for k in range(NT)] for i in range(N)]

def cases():
    out = []
    for t in range(1, 12):
        for m in range(0, TOTAL + 2 - 2 * t):
            out.append((t, m, max(0, m + 2 * t - 19)))
    return out

def normal_form(t, m, minand):
    """CNF for one case.  Why the normal form loses nothing:
    1. A wire that is not below F stays not below F through OR gates, and an AND gate that reads
       a wire with a below-F AND gate in its cone breaks top form.  The output is below F.  So the
       gates the output depends on split into: below-F AND gates (tops), OR gates above them (all
       below F, reading only tops and such ORs), and the gates under the tops (the bottom), none
       of which is below F (inputs are not, and the bottom holds no below-F AND gate).  So every
       bottom AND gate is junk, and the operands of a top are bottom wires or inputs.
    2. With t tops reached from the output, at least t - 1 OR gates lie above them.
    3. Gates the output does not depend on: a junk one counts towards the three; the others are
       dropped.  A circuit of the range therefore gives: bottom gates all used (m of them, with j
       ANDs), t tops, and 3 - j further junk gates if j < 3, in at most 21 gates:
       m + max(0, 3 - j) + 2t - 1 <= 21, that is j >= m + 2t - 19.
    4. If two bottom wires (or a bottom wire and an input) have the same test vector, every reader
       of the later one can read the earlier one; all test vectors stay the same, the later gate
       becomes unused and is dropped: a smaller object of the same kind (if the dropped gate was
       an AND, j and m both fall by one and j >= m + 2t - 19 still holds).  So vectors may be
       taken pairwise different; in particular no gate reads the same wire twice.
    5. Order of the bottom gates: while some gate g+1 does not read gate g and its pair of inputs
       (larger first) is smaller than that of gate g, swap the two; the sequence of pairs falls
       lexicographically, so this ends, with: gate g+1 reads gate g, or pair(g) <= pair(g+1).
    6. Tops are a set: taken in strictly increasing order of their pairs of operands."""
    nv = [0]
    def new():
        nv[0] += 1; return nv[0]
    cls = []
    W = N + m                                     # bottom wires: inputs 0..N-1, gates N..N+m-1
    val = [[None] * NT for _ in range(W)]         # literal or bool
    isand = [new() for _ in range(m)]
    sa = [[new() for _ in range(N + g)] for g in range(m)]   # smaller operand
    sb = [[new() for _ in range(N + g)] for g in range(m)]   # larger operand
    for i in range(N):
        for k in range(NT): val[i][k] = INVEC[i][k]
    def lit_imp_eq(sel, x, src):
        # sel -> (x <-> src), src a literal or a bool
        if src is True: cls.append([-sel, x])
        elif src is False: cls.append([-sel, -x])
        else: cls.append([-sel, -x, src]); cls.append([-sel, x, -src])
    for g in range(m):
        cand = N + g
        for s in (sa[g], sb[g]):
            cls.append(list(s))
            for i, j in itertools.combinations(range(cand), 2): cls.append([-s[i], -s[j]])
        # smaller operand strictly below the larger one
        for i in range(cand):
            for j in range(cand):
                if i >= j: cls.append([-sa[g][i], -sb[g][j]])
        A = [new() for _ in range(NT)]; Bv = [new() for _ in range(NT)]
        for k in range(NT):
            v = new(); val[N + g][k] = v
            for i in range(cand):
                lit_imp_eq(sa[g][i], A[k], val[i][k]); lit_imp_eq(sb[g][i], Bv[k], val[i][k])
            a, b, c = A[k], Bv[k], isand[g]
            cls += [[-c, -v, a], [-c, -v, b], [-c, v, -a, -b], [c, v, -a], [c, v, -b], [c, -v, a, b]]
        # a bottom AND gate is junk: true on some maximal independent set
        cls.append([-isand[g]] + [val[N + g][k] for k in range(NE, NB)])
    # pairwise different vectors (bottom gates against all earlier wires)
    for g in range(m):
        for h in range(N + g):
            ds = []
            for k in range(NB):                    # different on the base columns
                x, y = val[N + g][k], val[h][k]
                d = new(); ds.append(d)
                if y is True: cls.append([-d, -x])
                elif y is False: cls.append([-d, x])
                else: cls += [[-d, x, y], [-d, -x, -y]]
            cls.append(ds)
    # co-lexicographic order of consecutive bottom gates
    for g in range(m - 1):
        last = N + g                               # the wire of gate g, readable by gate g+1
        for i in range(N + g):
            for j in range(i):
                cls.append([-sb[g][i], -sb[g + 1][j]])           # larger operands: b_g <= b_{g+1} (b_{g+1} = last is the reading case)
            for i1 in range(i):
                for j1 in range(i1):
                    cls.append([-sb[g][i], -sb[g + 1][i], -sa[g][i1], -sa[g + 1][j1]])
    # tops
    ta = [[new() for _ in range(W)] for _ in range(t)]
    tb = [[new() for _ in range(W)] for _ in range(t)]
    tv = [[new() for _ in range(NE)] for _ in range(t)]
    for T in range(t):
        for s in (ta[T], tb[T]):
            cls.append(list(s))
            for i, j in itertools.combinations(range(W), 2): cls.append([-s[i], -s[j]])
        for i in range(W):
            for j in range(W):
                if i >= j: cls.append([-ta[T][i], -tb[T][j]])
        A = [new() for _ in range(NT)]; Bv = [new() for _ in range(NT)]
        for k in range(NT):
            for i in range(W):
                lit_imp_eq(ta[T][i], A[k], val[i][k]); lit_imp_eq(tb[T][i], Bv[k], val[i][k])
            if k < NE: cls += [[-tv[T][k], A[k]], [-tv[T][k], Bv[k]], [tv[T][k], -A[k], -Bv[k]]]
            else: cls.append([-A[k], -Bv[k]])           # below F
    for k in range(NE): cls.append([tv[T][k] for T in range(t)])   # every edge is covered
    # tops in strictly increasing order of (larger operand, smaller operand)
    for T in range(t - 1):
        for i in range(W):
            for j in range(i): cls.append([-tb[T][i], -tb[T + 1][j]])
            for i1 in range(i):
                for j1 in range(i1 + 1):
                    cls.append([-tb[T][i], -tb[T + 1][i], -ta[T][i1], -ta[T + 1][j1]])
    # every bottom gate is read
    for g in range(m):
        w = N + g
        cls.append([sa[h][w] for h in range(g + 1, m)] + [sb[h][w] for h in range(g + 1, m)] +
                   [ta[T][w] for T in range(t)] + [tb[T][w] for T in range(t)])
    # at least minand AND gates in the bottom
    if minand > m: cls.append([])
    elif minand > 0:
        enc = CardEnc.atleast(lits=isand, bound=minand, top_id=nv[0], encoding=EncType.seqcounter)
        cls += enc.clauses; nv[0] = max(nv[0], enc.nv)
    return cls, dict(isand=isand, sa=sa, sb=sb, ta=ta, tb=tb)

def solve(t, m, minand):
    cls, names = normal_form(t, m, minand)
    if any(len(c) == 0 for c in cls): return False, None, 0.0
    t0 = time.time()
    with Cadical153(bootstrap_with=cls) as s:
        ok = s.solve()
        if not ok: return False, None, time.time() - t0
        mod = set(l for l in s.get_model() if l > 0)
    pick = lambda row: next(i for i, v in enumerate(row) if v in mod)
    gates = [('and' if names['isand'][g] in mod else 'or', pick(names['sa'][g]), pick(names['sb'][g])) for g in range(m)]
    tops = [(pick(names['ta'][T]), pick(names['tb'][T])) for T in range(t)]
    return True, (gates, tops), time.time() - t0

def circuit_of(gates, tops):
    """The full circuit as a gate list (wire N + position), with an independent check on all 2^11 inputs."""
    full = list(gates); m = len(gates); tw = []
    for a, b in tops: tw.append(N + len(full)); full.append(('and', a, b))
    acc = tw[0]
    for w in tw[1:]:
        full.append(('or', acc, w)); acc = N + len(full) - 1
    for x in range(1 << N):
        w = [bool(x >> i & 1) for i in range(N)]
        for op, a, b in full: w.append((w[a] and w[b]) if op == 'and' else (w[a] or w[b]))
        assert w[acc] == any(x >> u & 1 and x >> v & 1 for u, v in EDGES)
    return full

def brute(total):
    # self-test only: is there ANY AND/OR fan-in-two circuit (a < b) with exactly `total` gates for F?  Plain search over test vectors.
    target = sum(1 << k for k in range(NE))
    base = [sum(1 << k for k in range(NB) if TESTS[k] >> i & 1) for i in range(N)]
    def rec(ws, left):
        if left == 0: return ws[-1] == target
        for a in range(len(ws)):
            for b in range(a + 1, len(ws)):
                for v in (ws[a] & ws[b], ws[a] | ws[b]):
                    if v in ws: continue
                    if rec(ws + [v], left - 1): return True
        return False
    return rec(base, total)

if __name__ == '__main__':
    if sys.argv[1] == 'list':
        for c in cases(): print(*c)
    elif sys.argv[1] == 'brute':
        print('BRUTE', sys.argv[2], brute(int(sys.argv[2])))
    elif sys.argv[1] == 'one':
        t, m = int(sys.argv[2]), int(sys.argv[3])
        minand = int(sys.argv[4]) if len(sys.argv) > 4 else max(0, m + 2 * t - 19)
        ok, obj, secs = solve(t, m, minand)
        if ok:
            full = circuit_of(*obj)
            print('YES', t, m, minand, 'gates', len(full), 'seconds %.1f' % secs, full)
        else:
            print('NO', t, m, minand, 'seconds %.1f' % secs)
