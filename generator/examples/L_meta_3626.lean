import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3626

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

-- In a circuit of NOT gates only, every wire is a function of one input.
lemma not_only {m : ℕ} (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.not) :
    ∀ (W : (Fin m → Bool) → List Bool) (len : ℕ) (c0 : Fin m), (∀ x, (W x).length = len) →
      (∀ w, ∃ (c : Fin m) (f : Bool → Bool), ∀ x, (W x).getD w false = f (x c)) →
      ∀ w, ∃ (c : Fin m) (f : Bool → Bool), ∀ x, (gs.foldl step (W x)).getD w false = f (x c) := by
  induction gs with
  | nil => intro W len c0 _ h w; exact h w
  | cons g gs ih =>
    intro W len c0 hlen h w
    have hop := hgs g List.mem_cons_self
    simp only [List.foldl_cons]
    apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')) (fun x => step (W x) g) (len + 1) c0
    · intro x
      simp [step, hlen x]
    · intro j
      rcases Nat.lt_trichotomy j len with hj | hj | hj
      · obtain ⟨c, f, hf⟩ := h j
        refine ⟨c, f, fun x => ?_⟩
        simp only [step]
        rw [List.getD_append _ _ _ _ (by rw [hlen x]; exact hj)]
        exact hf x
      · subst hj
        obtain ⟨op, inputs⟩ := g
        simp only at hop
        subst hop
        cases inputs with
        | nil =>
          refine ⟨c0, fun _ => true, fun x => ?_⟩
          simp only [step]
          rw [List.getD_append_right _ _ _ _ (by rw [hlen x]), hlen x, Nat.sub_self,
            List.getD_cons_zero]
          rfl
        | cons a l =>
          obtain ⟨c, f, hf⟩ := h a
          refine ⟨c, fun b => !(f b), fun x => ?_⟩
          simp only [step]
          rw [List.getD_append_right _ _ _ _ (by rw [hlen x]), hlen x, Nat.sub_self,
            List.getD_cons_zero]
          change (!((W x).getD a false)) = !(f (x c))
          rw [hf x]
      · refine ⟨c0, fun _ => false, fun x => ?_⟩
        rw [List.getD_eq_default _ _ (by simp [step, hlen x]; omega)]

lemma main (n : ℕ) (i : Fin (n + 1)) (C : Circuit) (L : List (Fin (n + 1)))
    (h1 : ∃ x : Fin (n + 1) → Bool,
      C.eval (L.map (Function.update x i true)) ≠ C.eval (L.map (Function.update x i false)))
    (h2 : ∃ (y y' : Fin n → Bool),
      C.eval (L.map (i.insertNth false y)) ≠ C.eval (L.map (i.insertNth false y'))) :
    ∃ g ∈ C.gates, g.op ≠ GateOp.not := by
  by_contra hno
  push Not at hno
  have key := not_only C.gates hno (fun x => L.map x) L.length i (fun x => by simp) (by
    intro w
    by_cases hw : w < L.length
    · refine ⟨L[w], id, fun x => ?_⟩
      simp [List.getD_eq_getElem?_getD, hw]
    · refine ⟨i, fun _ => false, fun x => ?_⟩
      rw [List.getD_eq_default _ _ (by simp; omega)]) C.output
  obtain ⟨c, f, hf⟩ := key
  have hE : ∀ x : Fin (n + 1) → Bool, C.eval (L.map x) = f (x c) := hf
  obtain ⟨x, hx⟩ := h1
  rw [hE, hE] at hx
  by_cases hc : c = i
  · subst hc
    obtain ⟨y, y', hy⟩ := h2
    rw [hE, hE] at hy
    simp at hy
  · simp [Function.update, hc] at hx

end PEqualNP.Outside.L_meta_3626

theorem PEqualNP.Outside.L_meta_3626 : have x1 : List PEqualNP.CircuitLowerBounds.Gate → ℕ := fun (x1 : List PEqualNP.CircuitLowerBounds.Gate) => List.countP (fun (x2 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.true Bool.true Bool.false (fun (x3 : ℕ) => Bool.true) Bool.true x2.op) x1; ∀ (x2 : ℕ) (x3 : Fin (x2 + (1 : ℕ))) (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : List (Fin (x2 + (1 : ℕ)))),   PEqualNP.MetaComplexity.FanInTwo x4 →     have x7 : (Fin (x2 + (1 : ℕ)) → Bool) → Bool := fun (x7 : Fin (x2 + (1 : ℕ)) → Bool) => x4.eval (List.map x7 x5);     (∃ (x8 : Fin (x2 + (1 : ℕ)) → Bool), x7 (Function.update x8 x3 Bool.true) ≠ x7 (Function.update x8 x3 Bool.false)) → (∃ (x9 : Fin x2 → Bool) (x10 : Fin x2 → Bool), x7 (x3.insertNth Bool.false x9) ≠ x7 (x3.insertNth Bool.false x10)) → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x10 ∧ x1 x10.gates + (1 : ℕ) ≤ x1 x4.gates := by
  intro cnt n i C L hf f h1 h2
  obtain ⟨g, hg, hop⟩ := PEqualNP.Outside.L_meta_3626.main n i C L h1 h2
  refine ⟨⟨[], 0⟩, fun g hg => absurd hg List.not_mem_nil, ?_⟩
  have hpos : 0 < List.countP (fun x2 : PEqualNP.CircuitLowerBounds.Gate =>
      PEqualNP.CircuitLowerBounds.GateOp.rec Bool.true Bool.true Bool.false
        (fun _ => Bool.true) Bool.true x2.op) C.gates := by
    apply List.countP_pos_iff.mpr
    refine ⟨g, hg, ?_⟩
    cases h : g.op <;> simp_all
  exact hpos
