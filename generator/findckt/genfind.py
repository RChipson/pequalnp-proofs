#!/usr/bin/env python3
"""Rows "... has an AND/OR/NOT circuit of fan-in at most two with at most k gates" whose function is
written as an OR of AND terms of inputs, possibly under one outer negation (3-colourability of small
graphs, Hamiltonian cycle on small graphs, and the like).

Method: the inner function is monotone, so an AND/OR circuit computes it exactly when it is true on
every minimal true input and false on every maximal false input.  A SAT solver looks for an AND/OR
circuit with k gates (k - 1 and a final NOT when the function is negated); the result is checked on
all inputs here and then by the kernel in the proof.

  python3 genfind.py <step id> <statement file> <out.lean> [seconds]
Exit 0: file written.  Exit 1: no circuit found in the time given (this proves nothing)."""
import itertools, os, re, subprocess, sys, time
from pysat.solvers import Cadical153

def parse(stmt):
    m = re.fullmatch(r'PEqualNP\.MetaComplexity\.HasCircuitSize (\d+) \(fun x : Fin (\d+) → Bool => (!?)\(?(.*?)\)?\) (\d+)', stmt.strip(), re.S)
    if not m: return None
    n, neg, body, k = int(m.group(1)), m.group(3) == '!', m.group(4), int(m.group(5))
    terms = []
    for t in body.split(' || '):
        t = t.strip()
        if not re.fullmatch(r'\(?x \d+( && x \d+)*\)?', t): return None
        terms.append(sum(1 << int(v) for v in re.findall(r'x (\d+)', t)))
    return n, neg, terms, k

def rows_of(n, terms):
    F = [any((x & t) == t for t in terms) for x in range(1 << n)]
    mins = [x for x in range(1 << n) if F[x] and all(not F[x & ~(1 << i)] for i in range(n) if x >> i & 1)]
    maxs = [x for x in range(1 << n) if not F[x] and all(F[x | (1 << i)] for i in range(n) if not x >> i & 1)]
    return F, [(x, True) for x in mins] + [(x, False) for x in maxs]

def find(n, k, rows):
    nv = [0]
    def new():
        nv[0] += 1; return nv[0]
    R = len(rows); cls = []; val = [[bool(rows[r][0] >> i & 1) for r in range(R)] for i in range(n)]; typ = []; sel = []
    for g in range(k):
        c = new(); typ.append(c)
        pairs = list(itertools.combinations(range(n + g), 2)); ps = [new() for _ in pairs]; sel.append((pairs, ps))
        cls.append(list(ps))
        for a, b in itertools.combinations(ps, 2): cls.append([-a, -b])
        row = [new() for _ in range(R)]
        for (i, j), p in zip(pairs, ps):
            for r in range(R):
                x, y, v = val[i][r], val[j][r], row[r]
                for cv in (True, False):
                    for xv in ((True, False) if not isinstance(x, bool) else (x,)):
                        for yv in ((True, False) if not isinstance(y, bool) else (y,)):
                            o = (xv and yv) if cv else (xv or yv)
                            cl = [-p, -c if cv else c]
                            if not isinstance(x, bool): cl.append(-x if xv else x)
                            if not isinstance(y, bool): cl.append(-y if yv else y)
                            cl.append(v if o else -v); cls.append(cl)
        val.append(row)
    for g in range(k - 1):      # every gate but the last is read later (loses nothing: unused gates can be dropped)
        w = n + g; cls.append([p for h in range(g + 1, k) for (i, j), p in zip(*sel[h]) if w in (i, j)])
    for r in range(R): cls.append([val[-1][r] if rows[r][1] else -val[-1][r]])
    with Cadical153(bootstrap_with=cls) as s:
        if not s.solve(): return None
        mod = set(l for l in s.get_model() if l > 0)
    gates = []
    for g in range(k):
        pairs, ps = sel[g]
        i, j = next(pr for pr, p in zip(pairs, ps) if p in mod)
        gates.append(('and' if typ[g] in mod else 'or', i, j))
    return gates

def lean(step, stmt, n, gates):
    ns = 'PEqualNP.Outside.' + step.replace('-', '_'); P = 'PEqualNP.CircuitLowerBounds'
    g = ', '.join(f'⟨{P}.GateOp.not, [{a}]⟩' if t == 'not' else f'⟨{P}.GateOp.{t}, [{a}, {b}]⟩' for t, a, b in gates)
    rfls = ' | '.join(['rfl'] * len(gates))
    return f'''import Mathlib
import PEqualNP.Defs

namespace {ns}

-- The circuit, found by a SAT search on the minimal true and maximal false inputs of the monotone
-- inner function; the kernel checks it on every input.
def wit : {P}.Circuit := ⟨[{g}], {n + len(gates) - 1}⟩

end {ns}

set_option maxRecDepth 100000 in
theorem {ns} : {stmt} := by
  refine ⟨{ns}.wit, ?_, ?_, ?_⟩
  · intro g hg
    simp only [{ns}.wit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with {rfls} <;> simp
  · decide
  · decide +kernel
'''

def main():
    if sys.argv[1] == 'find':
        import json
        n, k = int(sys.argv[2]), int(sys.argv[3]); rows = json.load(open(sys.argv[4]))
        print('GATES' + repr(find(n, k, [tuple(r) for r in rows]))); return 0
    step, sf, outp = sys.argv[1:4]; secs = int(sys.argv[4]) if len(sys.argv) > 4 else 780
    stmt = open(sf).read().strip(); p = parse(stmt)
    if not p: print('not a row of this shape'); return 2
    n, neg, terms, k = p
    if n > 12: print('too many inputs for this tool'); return 1
    F, rows = rows_of(n, terms)
    import json
    rf = outp + '.rows.json'; json.dump(rows, open(rf, 'w'))
    kk = k - 1 if neg else k
    t0 = time.time(); procs = {}
    for q in sorted({kk, kk - 1, kk - 2} - {0, -1}):   # the size allowed and one or two fewer, side by side
        procs[q] = subprocess.Popen([sys.executable, os.path.abspath(__file__), 'find', str(n), str(q), rf], stdout=subprocess.PIPE, text=True)
    gates = None
    while procs and time.time() - t0 < secs and not gates:
        for q, pr in list(procs.items()):
            if pr.poll() is not None:
                o = pr.stdout.read(); del procs[q]
                if o.startswith('GATES['): gates = eval(o[5:])
        time.sleep(0.5)
    for pr in procs.values(): pr.kill()
    if not gates: print(f'no circuit with at most {k} gates found in {int(time.time() - t0)} s'); return 1
    if neg: gates = gates + [('not', n + len(gates) - 1, 0)]
    for x in range(1 << n):
        w = [bool(x >> i & 1) for i in range(n)]
        for t, a, b in gates: w.append((w[a] and w[b]) if t == 'and' else (w[a] or w[b]) if t == 'or' else (not w[a]))
        assert w[-1] == (F[x] != neg)
    assert len(gates) <= k
    open(outp, 'w').write(lean(step, stmt, n, gates))
    print(f'wrote {outp}: {len(gates)} gates in {int(time.time() - t0)} s'); return 0

if __name__ == '__main__':
    sys.exit(main())
