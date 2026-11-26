#!/usr/bin/env python3
"""Rows "Six-input monotone f, table A * 2^32 + B: a fan-in-two circuit of at most k gates with a
one-input NOT gate computes f".  The circuit is found by SAT (AND/OR on two wires, NOT on one, at
least one NOT, every gate counted) and the proof is the circuit, checked by evaluation.

  python3 gen1n.py <step id> <statement file> <out.lean> [seconds]"""
import os, re, sys, time, subprocess
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, os.path.join(HERE, '..', 'mux'))
import synth_not
PAT = re.compile(r'∃ C : PEqualNP\.CircuitLowerBounds\.Circuit, PEqualNP\.MetaComplexity\.FanInTwo C ∧ \(∃ g ∈ C\.gates, g\.op = PEqualNP\.CircuitLowerBounds\.GateOp\.not ∧ g\.inputs\.length = 1\) ∧ C\.size ≤ (\d+) ∧ ∀ x : Fin (\d+) → Bool, C\.eval \(List\.ofFn x\) = Nat\.testBit \((\d+) \* 2 \^ 32 \+ (\d+)\) \(∑ i : Fin \d+, if x i then 2 \^ \(i : ℕ\) else 0\)')

def find(n, T, k):
    S = synth_not.Synth(n, k, True)
    S.s.add_clause([S.typ[g][2] for g in range(k)])          # at least one NOT
    for x in range(1 << n): S.add_row(x, bool(T >> x & 1))
    return S.solve()

def lean(step, stmt, n, gates):
    ns = 'PEqualNP.Outside.' + step.replace('-', '_'); P = 'PEqualNP.CircuitLowerBounds'
    g = ', '.join(f'⟨{P}.GateOp.not, [{a}]⟩' if t == 'not' else f'⟨{P}.GateOp.{t}, [{a}, {b}]⟩' for t, a, b in gates)
    rfls = ' | '.join(['rfl'] * len(gates)); na = next(a for t, a, b in gates if t == 'not')
    return f'''import Mathlib
import PEqualNP.Defs

namespace {ns}

-- The circuit, found by a SAT search; the kernel checks it on every input.
def wit : {P}.Circuit := ⟨[{g}], {n + len(gates) - 1}⟩

end {ns}

theorem {ns} : {stmt} := by
  refine ⟨{ns}.wit, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [{ns}.wit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with {rfls} <;> simp
  · exact ⟨⟨{P}.GateOp.not, [{na}]⟩, by simp [{ns}.wit], rfl, rfl⟩
  · decide
  · decide +kernel
'''

def main():
    if sys.argv[1] == 'find':
        print('GATES' + repr(find(int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])))); return 0
    step, sf, outp = sys.argv[1:4]; secs = int(sys.argv[4]) if len(sys.argv) > 4 else 780
    stmt = open(sf).read().strip(); m = PAT.fullmatch(stmt)
    if not m: print('not a row of this family'); return 2
    k, n, T = int(m.group(1)), int(m.group(2)), int(m.group(3)) * 2 ** 32 + int(m.group(4))
    t0 = time.time(); procs = {q: subprocess.Popen([sys.executable, os.path.abspath(__file__), 'find', str(n), str(T), str(q)], stdout=subprocess.PIPE, text=True) for q in (k, k - 1)}
    gates = None
    while procs and time.time() - t0 < secs and not gates:
        for q, pr in list(procs.items()):
            if pr.poll() is not None:
                o = pr.stdout.read(); del procs[q]
                if o.startswith('GATES['): gates = eval(o[5:])
        time.sleep(0.5)
    for pr in procs.values(): pr.kill()
    if not gates:
        # both searches ended (exactly k and exactly k - 1 gates, which cover every smaller size by a doubled NOT): none exists
        if not procs: print(f'no circuit with at most {k} gates and a NOT exists (exhaustive search, {int(time.time() - t0)} s)'); return 1
        print(f'undecided: the search did not end in {secs} s'); return 3
    for x in range(1 << n): assert synth_not.evalc(n, gates, x) == bool(T >> x & 1)
    assert len(gates) <= k and any(t == 'not' for t, a, b in gates)
    open(outp, 'w').write(lean(step, stmt, n, gates)); print(f'wrote {outp}: {len(gates)} gates in {int(time.time() - t0)} s'); return 0

if __name__ == '__main__':
    sys.exit(main())
