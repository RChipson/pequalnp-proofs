#!/usr/bin/env python3
"""Rows "Three ordered outputs a, b, c fit N gates with at most two NOTs".

Inputs are the four thresholds (i < t) on the five points t = 0..4, then the constants false and true.  A wire is
its 5-bit pattern.  A short search over sets of patterns finds a circuit of at most N gates with at most two NOT
gates that has the three patterns among its wires; the Lean file gives that circuit and the three wires, and Lean
checks every clause of the statement by evaluation.

  python3 genfit.py <step id> <statement file> <out.lean>
Exit 0: file written.  Exit 1: no such circuit exists (then the row is false and its twin "exceed" is the true one).
Exit 3: not a row of this family."""
import itertools, re, sys
INP = [sum(1 << t for t in range(5) if i < t) for i in range(4)] + [0, 31]

def least(targets, maxn, nots=2):
    targets = [x & 31 for x in targets]
    def dfs(have, order, k, used):
        need = [x for x in targets if x not in have]
        if not need: return list(order)
        if k == 0 or len(set(need)) > k: return None
        key = (have, k, used)
        if key in seen: return None
        seen.add(key)
        hv = sorted(have); cands = {}
        for a, b in itertools.combinations(hv, 2):
            for op, v in (('and', a & b), ('or', a | b)):
                if v not in have and v not in cands: cands[v] = (op, a, b)
        if used < nots:
            for a in hv:
                v = a ^ 31
                if v not in have and v not in cands: cands[v] = ('not', a, a)
        for v in sorted(cands, key=lambda v: (v not in need, v)):
            op, a, b = cands[v]
            r = dfs(have | {v}, order + [(op, a, b, v)], k - 1, used + (op == 'not'))
            if r is not None: return r
        return None
    for n in range(0, maxn + 1):
        seen = set()
        r = dfs(frozenset(INP), [], n, 0)
        if r is not None: return n, r
    return None, None

PAT = re.compile(r'^∃ \(D : PEqualNP\.CircuitLowerBounds\.Circuit\) \(p q r : Fin \(6\+D\.size\)\),\s+PEqualNP\.MetaComplexity\.FanInTwo D ∧ PEqualNP\.MetaComplexity\.NestedCover\.ReadsBack 6 D ∧\s+'
                 r'PEqualNP\.NotBracket\.notCount D ≤ 2 ∧ D\.size ≤ (\d+) ∧\s+∀ t : Fin 5,\s+let xs := \(List\.ofFn \(fun i : Fin 4 => decide \(i\.val < t\.val\)\)\) \+\+ \[false,true\]\s+let w := D\.wires xs\s+'
                 r'w\.getD p\.val false = \((\d+) : Nat\)\.testBit t\.val ∧\s+w\.getD q\.val false = \((\d+) : Nat\)\.testBit t\.val ∧\s+w\.getD r\.val false = \((\d+) : Nat\)\.testBit t\.val$')

def build(step, stmt):
    m = PAT.match(stmt)
    if not m: return 3, None
    N, a, b, c = map(int, m.groups())
    if max(a, b, c) > 31: return 3, None
    n, circ = least([a, b, c], N)
    if circ is None: return 1, None
    wire = {p: i for i, p in enumerate(INP)}; gates = []
    for j, (op, x, y, v) in enumerate(circ):
        gates.append(f'⟨.not, [{wire[x]}]⟩' if op == 'not' else f'⟨.{op}, [{wire[x]}, {wire[y]}]⟩'); wire[v] = 6 + j
    p, q, r = wire[a & 31], wire[b & 31], wire[c & 31]
    ns = step.replace('-', '_')
    txt = f'''import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.{ns} : {stmt} := by
  refine ⟨⟨[{', '.join(gates)}], 0⟩, ⟨{p}, by decide⟩, ⟨{q}, by decide⟩, ⟨{r}, by decide⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with {' | '.join(['rfl'] * len(gates))} <;> simp
  · intro j hj i hi
    have hj' : j < {len(gates)} := hj
    interval_cases j <;> simp [PEqualNP.MetaComplexity.NestedCover.gateAt] at hi <;> omega
  · decide
  · decide
  · decide
'''
    return 0, txt

if __name__ == '__main__':
    step, sf, out = sys.argv[1:4]
    rc, txt = build(step, open(sf).read().strip())
    if rc == 0: open(out, 'w').write(txt); print('written')
    else: print('no circuit of that size exists: the row is false' if rc == 1 else 'not a row of this family')
    sys.exit(rc)
