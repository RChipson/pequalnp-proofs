import Mathlib
import PEqualNP.Defs

-- Run the first circuit, then the second on all of its wires, then one OR gate of the
-- two outputs: 44 + 18 + 1 gates.
namespace PEqualNP.Outside.L_meta_4091
open PEqualNP.CircuitLowerBounds

def W (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma W_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    W (gs ++ [g]) x = W gs x ++ [g.op.eval (g.inputs.map fun i => (W gs x).getD i false)] := by
  simp [W, List.foldl_append]

lemma W_length (gs : List Gate) (x : List Bool) : (W gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [W]
  | append_singleton gs g ih => rw [W_snoc]; simp [ih]; omega

lemma getD_snoc (l : List Bool) (v : Bool) (i : Nat) :
    (l ++ [v]).getD i false =
      if i < l.length then l.getD i false else if i = l.length then v else false := by
  split_ifs with h1 h2
  · exact List.getD_append _ _ _ _ h1
  · subst h2
    rw [List.getD_append_right _ _ _ _ (le_refl _)]
    simp
  · rw [List.getD_eq_default]
    simp
    omega

lemma W_input (gs : List Gate) (x : List Bool) (i : Nat) (hi : i < x.length) :
    (W gs x).getD i false = x.getD i false := by
  induction gs using List.reverseRecOn with
  | nil => simp [W]
  | append_singleton gs g ih =>
    rw [W_snoc, getD_snoc, W_length, if_pos (by omega)]
    exact ih

end PEqualNP.Outside.L_meta_4091

open PEqualNP.Outside.L_meta_4091 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_4091 : ∀ (x1 x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → x1.size = (44 : ℕ) → x1.output < (70 : ℕ) → PEqualNP.MetaComplexity.Monotone2 x2 → x2.size ≤ (18 : ℕ) → ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x8 ∧ x8.size ≤ (63 : ℕ) ∧ ∀ (x9 : List Bool), x9.length = (26 : ℕ) → x8.eval x9 = (x1.eval x9 || x2.eval (x1.wires x9)) := by
  intro C1 C2 h1 hs1 ho1 h2 hs2
  have l1 : C1.gates.length = 44 := hs1
  have l2 : C2.gates.length ≤ 18 := hs2
  refine ⟨⟨C1.gates ++ C2.gates ++ [(⟨GateOp.or, [C1.output, C2.output]⟩ : Gate)],
    70 + C2.gates.length⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with (hg | hg) | rfl
    · exact h1 g hg
    · exact h2 g hg
    · exact ⟨by simp, by simp⟩
  · show (C1.gates ++ C2.gates ++ [(⟨GateOp.or, [C1.output, C2.output]⟩ : Gate)]).length ≤ 63
    simp only [List.length_append, List.length_singleton]
    omega
  · intro x hx
    have e : W (C1.gates ++ C2.gates ++ [(⟨GateOp.or, [C1.output, C2.output]⟩ : Gate)]) x =
        W C2.gates (W C1.gates x) ++ [GateOp.or.eval
          [(W C2.gates (W C1.gates x)).getD C1.output false,
            (W C2.gates (W C1.gates x)).getD C2.output false]] := by
      rw [W_snoc]
      have : W (C1.gates ++ C2.gates) x = W C2.gates (W C1.gates x) := by
        unfold W
        rw [List.foldl_append]
      rw [this]
      rfl
    show (W (C1.gates ++ C2.gates ++ [(⟨GateOp.or, [C1.output, C2.output]⟩ : Gate)]) x).getD
      (70 + C2.gates.length) false = _
    rw [e, getD_snoc, W_length, W_length, hx, l1, if_neg (by omega), if_pos (by omega)]
    have p : (W C2.gates (W C1.gates x)).getD C1.output false =
        (W C1.gates x).getD C1.output false :=
      W_input _ _ _ (by rw [W_length, hx, l1]; omega)
    rw [p]
    show GateOp.or.eval [C1.eval x, C2.eval (C1.wires x)] = _
    cases C1.eval x <;> cases C2.eval (C1.wires x) <;> rfl
