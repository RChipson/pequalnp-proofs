import Mathlib
import PEqualNP.Defs

-- Clamp every wire index, and the output index, to 24. While the wire list has at most
-- 24 entries, index 24 and every larger index read the default value, so nothing changes.
namespace PEqualNP.Outside.L_meta_2677
open PEqualNP.CircuitLowerBounds

def clampG (g : Gate) : Gate := ⟨g.op, g.inputs.map (fun i => min i 24)⟩

def clamp (C : Circuit) : Circuit := ⟨C.gates.map clampG, min C.output 24⟩

lemma getD_clamp (w : List Bool) (h : w.length ≤ 24) (i : ℕ) :
    w.getD (min i 24) false = w.getD i false := by
  by_cases hi : i ≤ 24
  · rw [min_eq_left hi]
  · have h1 : w.length ≤ i := by omega
    have h2 : w.length ≤ min i 24 := by
      rw [min_eq_right (by omega)]
      exact h
    rw [List.getD_eq_default _ _ h1, List.getD_eq_default _ _ h2]

lemma fold_clamp (gs : List Gate) : ∀ (w : List Bool), w.length + gs.length ≤ 24 →
    (gs.map clampG).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w ∧
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length =
      w.length + gs.length := by
  induction gs with
  | nil => intro w _; simp
  | cons g gs ih =>
    intro w h
    simp only [List.length_cons] at h
    have hw : w.length ≤ 24 := by omega
    have hv : (clampG g).op.eval ((clampG g).inputs.map fun i => w.getD i false) =
        g.op.eval (g.inputs.map fun i => w.getD i false) := by
      simp only [clampG, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact getD_clamp w hw i
    have ih' := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (by
      simp only [List.length_append, List.length_singleton]; omega)
    simp only [List.map_cons, List.foldl_cons, List.length_cons]
    rw [hv]
    refine ⟨ih'.1, ?_⟩
    rw [ih'.2]
    simp only [List.length_append, List.length_singleton]
    omega

end PEqualNP.Outside.L_meta_2677

theorem PEqualNP.Outside.L_meta_2677 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), ∃ (x2 : PEqualNP.CircuitLowerBounds.Circuit), x2.size = x1.size ∧ (PEqualNP.MetaComplexity.Monotone2 x1 → PEqualNP.MetaComplexity.Monotone2 x2) ∧ (PEqualNP.MetaComplexity.FanInTwo x1 → PEqualNP.MetaComplexity.FanInTwo x2) ∧ x2.output ≤ (24 : ℕ) ∧ (∀ x3 ∈ x2.gates, ∀ x5 ∈ x3.inputs, x5 ≤ (24 : ℕ)) ∧ ∀ (x3 : List Bool), x3.length + x1.size ≤ (24 : ℕ) → x2.wires x3 = x1.wires x3 ∧ x2.eval x3 = x1.eval x3 ∧ (x1.wires x3).length = x3.length + x1.size := by
  intro C
  refine ⟨PEqualNP.Outside.L_meta_2677.clamp C, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [PEqualNP.Outside.L_meta_2677.clamp, PEqualNP.CircuitLowerBounds.Circuit.size]
  · intro h g hg
    simp only [PEqualNP.Outside.L_meta_2677.clamp, List.mem_map] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    have := h g0 hg0
    simpa [PEqualNP.Outside.L_meta_2677.clampG] using this
  · intro h g hg
    simp only [PEqualNP.Outside.L_meta_2677.clamp, List.mem_map] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    have := h g0 hg0
    simpa [PEqualNP.Outside.L_meta_2677.clampG] using this
  · exact min_le_right _ _
  · intro g hg i hi
    simp only [PEqualNP.Outside.L_meta_2677.clamp, List.mem_map] at hg
    obtain ⟨g0, _, rfl⟩ := hg
    simp only [PEqualNP.Outside.L_meta_2677.clampG, List.mem_map] at hi
    obtain ⟨i0, _, rfl⟩ := hi
    exact min_le_right _ _
  · intro x hx
    have key := PEqualNP.Outside.L_meta_2677.fold_clamp C.gates x hx
    have hw : (PEqualNP.Outside.L_meta_2677.clamp C).wires x = C.wires x := key.1
    have hl : (C.wires x).length = x.length + C.size := key.2
    refine ⟨hw, ?_, hl⟩
    show ((PEqualNP.Outside.L_meta_2677.clamp C).wires x).getD (min C.output 24) false =
      (C.wires x).getD C.output false
    rw [hw]
    exact PEqualNP.Outside.L_meta_2677.getD_clamp _ (by rw [hl]; exact hx) _
