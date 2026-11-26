#!/usr/bin/env python3
"""Rows "Monotone function on n inputs, table T: at most k AND, OR, NOT gates, none dead, a NOT on a
gate": find the circuit by SAT and write the proof (the circuit, checked by evaluation).

Conditions of the statement: every gate AND/OR/NOT with at most two inputs, reading earlier wires;
at most k gates; the circuit computes the table on every input; every gate is the output or is read
by a later gate; no NOT reads a NOT; some NOT reads a gate (not an input).

  python3 gennot.py <step id> <statement file> <out.lean> [seconds]
Exit 0: file written.  Exit 1: no circuit found in the time given (this proves nothing)."""
import itertools, os, re, subprocess, sys, time
from pysat.solvers import Cadical153

def parse(stmt):
    if stmt.startswith('¬'): return None
    m = re.search(r'ReadsBack (\d+) C ∧ C\.size ≤ (\d+) ∧ \(∀ x : Fin \d+ → Bool, C\.eval \(List\.ofFn x\) = PEqualNP\.MetaComplexity\.tableFun \d+ \(\(\[([01, ]+)\] : List ℕ\)\.map \(fun b => b == 1\)\) x\)', stmt)
    if not m or 'g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ ' not in stmt: return None
    return int(m.group(1)), int(m.group(2)), [int(b) for b in m.group(3).split(',')]

def find(n, k, table):
    nv = [0]
    def new():
        nv[0] += 1; return nv[0]
    s = Cadical153(); typ = []; sa = []; sb = []
    for g in range(k):
        t = [new() for _ in range(3)]; s.add_clause(t)
        for x, y in itertools.combinations(t, 2): s.add_clause([-x, -y])
        a = [new() for _ in range(n + g)]; b = [new() for _ in range(n + g)]
        for sel in (a, b):
            s.add_clause(sel)
            for x, y in itertools.combinations(sel, 2): s.add_clause([-x, -y])
        for i in range(n + g):
            for j in range(n + g):
                if i >= j: s.add_clause([t[2], -a[i], -b[j]])      # AND/OR: first operand below the second
                if i != j: s.add_clause([-t[2], -a[i], -b[j]])     # NOT: one operand (b repeats it)
        typ.append(t); sa.append(a); sb.append(b)
    for g in range(k - 1):                                         # none dead: read by a later gate (the output is the last gate)
        w = n + g
        s.add_clause([sa[h][w] for h in range(g + 1, k)] + [sb[h][w] for h in range(g + 1, k)])
    some = []
    for h in range(k):
        for g in range(h):
            s.add_clause([-typ[h][2], -sa[h][n + g], -typ[g][2]])  # no NOT reads a NOT
            z = new(); some.append(z); s.add_clause([-z, typ[h][2]]); s.add_clause([-z, sa[h][n + g]])
    s.add_clause(some)                                             # some NOT reads a gate
    for x in range(1 << n):
        val = [bool(x >> i & 1) for i in range(n)]
        for g in range(k):
            A = new(); B = new(); v = new()
            for i in range(n + g):
                for sel, X in ((sa[g][i], A), (sb[g][i], B)):
                    w = val[i]
                    if w is True: s.add_clause([-sel, X])
                    elif w is False: s.add_clause([-sel, -X])
                    else: s.add_clause([-sel, -X, w]); s.add_clause([-sel, X, -w])
            ta, to, tn = typ[g]
            for cl in ([-ta, -v, A], [-ta, -v, B], [-ta, v, -A, -B], [-to, v, -A], [-to, v, -B], [-to, -v, A, B], [-tn, v, A], [-tn, -v, -A]):
                s.add_clause(cl)
            val.append(v)
        out = bool(table[x]) if x < len(table) else False
        s.add_clause([val[-1] if out else -val[-1]])
    if not s.solve(): return None
    mod = set(l for l in s.get_model() if l > 0); gates = []
    for g in range(k):
        t = ['and', 'or', 'not'][next(i for i in range(3) if typ[g][i] in mod)]
        a = next(i for i, v in enumerate(sa[g]) if v in mod); b = next(i for i, v in enumerate(sb[g]) if v in mod)
        gates.append((t, a, b))
    return gates

def check(n, k, table, gates):
    assert len(gates) <= k
    for x in range(1 << n):
        w = [bool(x >> i & 1) for i in range(n)]
        for t, a, b in gates: w.append((w[a] and w[b]) if t == 'and' else (w[a] or w[b]) if t == 'or' else (not w[a]))
        assert w[-1] == bool(table[x])
    for j, (t, a, b) in enumerate(gates):
        assert a < n + j and b < n + j
        assert j == len(gates) - 1 or any((n + j) in ((a2, b2) if t2 != 'not' else (a2,)) for t2, a2, b2 in gates[j + 1:])
        if t == 'not' and a >= n: assert gates[a - n][0] != 'not'
    assert any(t == 'not' and a >= n for t, a, b in gates)

def lean(step, stmt, n, gates):
    ns = 'PEqualNP.Outside.' + step.replace('-', '_'); P = 'PEqualNP.CircuitLowerBounds'
    g = ', '.join(f'⟨{P}.GateOp.{t}, [{a}]⟩' if t == 'not' else f'⟨{P}.GateOp.{t}, [{a}, {b}]⟩' for t, a, b in gates)
    out = n + len(gates) - 1
    na = next(a for t, a, b in gates if t == 'not' and a >= n)      # a NOT that reads a gate
    rfls = ' | '.join(['rfl'] * len(gates))
    return f'''import Mathlib
import PEqualNP.Defs

namespace {ns}

-- The circuit, found by a SAT search; every condition of the statement is checked by evaluation.
def wit : {P}.Circuit := ⟨[{g}], {out}⟩

end {ns}

theorem {ns} : {stmt} := by
  refine ⟨{ns}.wit, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [{ns}.wit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with {rfls} <;> simp
  · decide
  · decide
  · decide +kernel
  · decide
  · intro g hg
    simp only [{ns}.wit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with {rfls} <;> simp [{ns}.wit]
  · exact ⟨⟨{P}.GateOp.not, [{na}]⟩, by simp [{ns}.wit], rfl, by simp⟩
'''

def main():
    if sys.argv[1] == 'find':
        n, k = int(sys.argv[2]), int(sys.argv[3]); table = [int(c) for c in sys.argv[4]]
        print('GATES' + repr(find(n, k, table))); return 0
    step, sf, outp = sys.argv[1:4]; secs = int(sys.argv[4]) if len(sys.argv) > 4 else 900
    stmt = open(sf).read().strip(); p = parse(stmt)
    if not p: print('not a row of this family'); return 2
    n, k, table = p
    t0 = time.time(); procs = {}
    for kk in (k, k - 1):      # exactly k gates, and one fewer, side by side
        procs[kk] = subprocess.Popen([sys.executable, os.path.abspath(__file__), 'find', str(n), str(kk), ''.join(map(str, table))], stdout=subprocess.PIPE, text=True)
    gates = None
    while procs and time.time() - t0 < secs and not gates:
        for kk, pr in list(procs.items()):
            if pr.poll() is not None:
                o = pr.stdout.read(); del procs[kk]
                if o.startswith('GATES['): gates = eval(o[5:])
        time.sleep(0.5)
    for pr in procs.values(): pr.kill()
    if not gates: print(f'no circuit with at most {k} gates found in {int(time.time() - t0)} s'); return 1
    check(n, k, table, gates)
    open(outp, 'w').write(lean(step, stmt, n, gates))
    print(f'wrote {outp}: {len(gates)} gates in {int(time.time() - t0)} s'); return 0

if __name__ == '__main__':
    sys.exit(main())
