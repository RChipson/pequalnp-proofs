"""Write the Lean proof file for an 'exists a monotone circuit' step from a gate list.
Usage: python3 emit_monotone.py <step id like L-meta-3515> <n> <size bound> <statement file> '<gates as python list>'
The gates are (op, a, b) with op 'and' or 'or'; the output is the last gate.
"""
import sys, ast
step, n, bound, stf, gates = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), sys.argv[4], ast.literal_eval(sys.argv[5])
mod = step.replace('-', '_')
st = open(stf).read().strip()
edges = st[st.index('∈ [') + 2: st.index(']', st.index('∈ [')) + 1]
gl = ', '.join('⟨.%s, [%d, %d]⟩' % g for g in gates)
bs = ' '.join('b%d' % i for i in range(n))
vec = '![' + ', '.join('b%d' % i for i in range(n)) + ']'
xs = '![' + ', '.join('x %d' % i for i in range(n)) + ']'
out = f'''import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.{mod}

open PEqualNP.CircuitLowerBounds

-- An explicit circuit, found by a search over circuits of this size. Its value is compared
-- with the edge function on every input by direct evaluation.
def circ : Circuit := ⟨[{gl}], {n + len(gates) - 1}⟩

lemma expand (x : Fin {n} → Bool) : x = {xs} := by
  funext i
  fin_cases i <;> rfl

set_option maxRecDepth 100000 in
lemma all_rows : ∀ {bs} : Bool,
    (circ.eval (List.ofFn {vec}) = true ↔
      ∃ (p : Fin {n}) (q : Fin {n}), ((p : ℕ), (q : ℕ)) ∈ ({edges} : List (ℕ × ℕ)) ∧
        {vec} p = true ∧ {vec} q = true) := by
  decide +kernel

lemma shape : PEqualNP.TopForm.IsAO2 {n} circ := by decide

lemma distinct : ∀ g ∈ circ.gates, g.inputs.Nodup := by decide

lemma small : circ.size ≤ {bound} := by decide

lemma correct (x : Fin {n} → Bool) :
    circ.eval (List.ofFn x) = true ↔
      ∃ (p : Fin {n}) (q : Fin {n}), ((p : ℕ), (q : ℕ)) ∈ ({edges} : List (ℕ × ℕ)) ∧
        x p = true ∧ x q = true := by
  have h := all_rows {' '.join('(x %d)' % i for i in range(n))}
  rw [← expand x] at h
  exact h

end PEqualNP.Outside.{mod}

theorem PEqualNP.Outside.{mod} : {st} :=
  ⟨PEqualNP.Outside.{mod}.circ, PEqualNP.Outside.{mod}.shape, PEqualNP.Outside.{mod}.distinct,
    PEqualNP.Outside.{mod}.small, PEqualNP.Outside.{mod}.correct⟩
'''
sys.stdout.write(out)
