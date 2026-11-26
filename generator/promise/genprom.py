#!/usr/bin/env python3
"""Rows "The n by n bipartite graph with mask M is represented on the one-a-side promise by an
AND/OR/NOT circuit of fan-in two with at most k gates".

Only the n*n inputs with exactly one left and one right vertex on matter.  For each mask the least
number of gates is found by SAT (gates AND, OR on two earlier wires, NOT on one; every gate counted);
a row is provable when its bar is at least that number, and the proof is the circuit, checked by
evaluation.

  python3 genprom.py survey <gaps.json> <out.json>         least sizes for every open row of the family
  python3 genprom.py lean <step id> <statement file> <out.lean>   write the proof (finds the circuit again)"""
import json, os, re, sys, time
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, os.path.join(HERE, '..', 'mux'))
import synth_not

PAT = re.compile(r'∃ C : PEqualNP\.CircuitLowerBounds\.Circuit, PEqualNP\.MetaComplexity\.FanInTwo C ∧ C\.size ≤ (\d+) ∧ PEqualNP\.Represents\.Represents \(fun u v : Fin (\d+) => \((\d+) : ℕ\)\.testBit \((\d+) \* u\.val \+ v\.val\)\) C')

def parse(stmt):
    m = PAT.fullmatch(stmt.strip())
    if not m or m.group(2) != m.group(4): return None
    return int(m.group(2)), int(m.group(3)), int(m.group(1))        # side, mask, bar

def rows_of(n, mask):
    return [((1 << u) | (1 << (n + v)), bool(mask >> (n * u + v) & 1)) for u in range(n) for v in range(n)]

def circuit(n, mask, k):
    """A circuit with exactly k gates, or None."""
    rows = rows_of(n, mask)
    if k == 0: return None
    S = synth_not.Synth(2 * n, k, True)
    for x, o in rows: S.add_row(x, o)
    return S.solve()

def least(n, mask, kmax):
    rows = rows_of(n, mask)
    # zero gates: the output is an input wire; not expressible in the statement's circuits unless a wire equals the function, skipped
    for k in range(1, kmax + 1):
        g = circuit(n, mask, k)
        if g:
            for x, o in rows: assert synth_not.evalc(2 * n, g, x) == o
            return k, g
    return None, None

def lean(step, stmt, n, gates):
    ns = 'PEqualNP.Outside.' + step.replace('-', '_'); P = 'PEqualNP.CircuitLowerBounds'
    g = ', '.join(f'⟨{P}.GateOp.not, [{a}]⟩' if t == 'not' else f'⟨{P}.GateOp.{t}, [{a}, {b}]⟩' for t, a, b in gates)
    rfls = ' | '.join(['rfl'] * len(gates))
    return f'''import Mathlib
import PEqualNP.Defs

namespace {ns}

-- The circuit, found by a SAT search over the promise inputs; the kernel checks it on each of them.
def wit : {P}.Circuit := ⟨[{g}], {2 * n + len(gates) - 1}⟩

end {ns}

theorem {ns} : {stmt} := by
  refine ⟨{ns}.wit, ?_, ?_, ?_⟩
  · intro g hg
    simp only [{ns}.wit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with {rfls} <;> simp
  · decide
  · decide +kernel
'''

def main():
    if sys.argv[1] == 'survey':
        gaps = json.load(open(sys.argv[2]))['gaps']; out = {}; memo = {}
        for g in gaps:
            p = parse(g.get('statement', ''))
            if not p: continue
            n, mask, bar = p
            if (n, mask) not in memo:
                t0 = time.time(); memo[(n, mask)] = least(n, mask, 10)
                print(n, mask, 'least', memo[(n, mask)][0], '%.1fs' % (time.time() - t0), flush=True)
            k, gates = memo[(n, mask)]
            out[g['id']] = dict(n=n, mask=mask, bar=bar, least=k, gates=gates, pr_open=g.get('pr_open'), ok=bool(k and k <= bar))
        json.dump(out, open(sys.argv[3], 'w'))
        print('rows', len(out), 'provable', sum(1 for v in out.values() if v['ok']), 'of which no PR', sum(1 for v in out.values() if v['ok'] and str(v['pr_open']) in ('0', 'None')))
        return 0
    step, sf, outp = sys.argv[2:5]
    stmt = open(sf).read().strip(); p = parse(stmt)
    if not p: print('not a row of this family'); return 2
    n, mask, bar = p
    k, gates = least(n, mask, bar)
    if not k: print(f'no circuit with at most {bar} gates'); return 1
    open(outp, 'w').write(lean(step, stmt, n, gates)); print(f'wrote {outp}: {k} gates for the bar {bar}'); return 0

if __name__ == '__main__':
    sys.exit(main())
