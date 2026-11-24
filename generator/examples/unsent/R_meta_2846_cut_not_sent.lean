import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2846_1
    (flat : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit),
      let g := PEqualNP.MetaComplexity.NestedCover.gateAt C
      let B : ℕ → Prop := fun w => ∀ z : Fin n → Bool,
        (C.wires (List.ofFn z)).getD w false = true →
          PEqualNP.MetaComplexity.circuitFun n C z = true
      PEqualNP.TopForm.IsAO2 n C →
      (∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 n D →
        PEqualNP.MetaComplexity.circuitFun n D = PEqualNP.MetaComplexity.circuitFun n C →
          C.size ≤ D.size) →
      (∃ T : Finset ℕ,
        (∀ i ∈ T, i < C.gates.length ∧ (g i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
          (n + i = C.output ∨ ∃ k ∈ T, ∀ k' < C.gates.length,
            (n + i ∈ (g k').inputs ↔ k' = k))) ∧
        ∀ w : ℕ, B w →
          (∃ k < C.gates.length, (g k).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
            w ∈ (g k).inputs) →
          ∀ k < C.gates.length, w ∈ (g k).inputs → k ∈ T) →
      ∀ i < C.gates.length, (g i).op = PEqualNP.CircuitLowerBounds.GateOp.and →
        ∀ w ∈ (g i).inputs, ¬ B w)
    (rest : ∀ (Np Nl : ℕ) (I : Fin Np → Fin Nl → Prop) [DecidableRel I]
        (C : PEqualNP.CircuitLowerBounds.Circuit),
      let n := Np + Nl
      let g := PEqualNP.MetaComplexity.NestedCover.gateAt C
      (∀ p p' : Fin Np, ∀ l l' : Fin Nl, p ≠ p' → l ≠ l' →
        ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) →
      PEqualNP.TopForm.IsAO2 n C →
      (∀ z : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n C z =
        decide (∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ z (Fin.castAdd Nl p) = true ∧
          z (Fin.natAdd Np l) = true)) →
      (∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 n D →
        PEqualNP.MetaComplexity.circuitFun n D = PEqualNP.MetaComplexity.circuitFun n C →
          C.size ≤ D.size) →
      (∃ T : Finset ℕ,
        (∀ i ∈ T, i < C.gates.length ∧ (g i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
          (n + i = C.output ∨ ∃ k ∈ T, ∀ k' < C.gates.length,
            (n + i ∈ (g k').inputs ↔ k' = k))) ∧
        ∀ w : ℕ, (∀ z : Fin n → Bool, (C.wires (List.ofFn z)).getD w false = true →
            PEqualNP.MetaComplexity.circuitFun n C z = true) →
          ∀ k < C.gates.length, w ∈ (g k).inputs → k ∈ T) →
      ∃ S : Bool → Finset ℕ,
        (∀ t w, w ∈ S t → (w < n ∧ decide (Np ≤ w) = t) ∨ ∃ i < C.gates.length,
          w = n + i ∧ (g i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
            ∀ u ∈ (g i).inputs, u ∈ S t) ∧
        ∀ i < C.gates.length, (g i).op = PEqualNP.CircuitLowerBounds.GateOp.and →
          ∃ a b t, (g i).inputs = [a, b] ∧ a ∈ S t ∧ b ∈ S (!t)) :
    ∀ (Np Nl : ℕ) (I : Fin Np → Fin Nl → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ p p' : Fin Np, ∀ l l' : Fin Nl, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.TopForm.IsAO2 (Np + Nl) C → (∀ z : Fin (Np + Nl) → Bool, PEqualNP.MetaComplexity.circuitFun (Np + Nl) C z = decide (∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true)) → (∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 (Np + Nl) D → (∀ z : Fin (Np + Nl) → Bool, PEqualNP.MetaComplexity.circuitFun (Np + Nl) D z = decide (∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true)) → C.size ≤ D.size) → (∃ T : Finset ℕ, (∀ i ∈ T, i < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (Np + Nl + i = C.output ∨ ∃ k ∈ T, ∀ k' < C.gates.length, (Np + Nl + i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k').inputs ↔ k' = k))) ∧ ∀ w : ℕ, (∀ z : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z)).getD w false = true → ∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true) → (∃ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs) → ∀ k < C.gates.length, w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs → k ∈ T) → (∃ P L : Finset ℕ, (∀ w ∈ P, w < Np ∨ ∃ i < C.gates.length, w = Np + Nl + i ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).inputs, u ∈ P) ∧ (∀ w ∈ L, (Np ≤ w ∧ w < Np + Nl) ∨ ∃ i < C.gates.length, w = Np + Nl + i ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).inputs, u ∈ L) ∧ ∀ i < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ a b : ℕ, (PEqualNP.MetaComplexity.NestedCover.gateAt C i).inputs = [a, b] ∧ ((a ∈ P ∧ b ∈ L) ∨ (a ∈ L ∧ b ∈ P))) := by
  intro Np Nl I _ C no4 ao hex least stuck
  have conv : ∀ z : Fin (Np + Nl) → Bool,
      PEqualNP.MetaComplexity.circuitFun (Np + Nl) C z = true →
        ∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ z (Fin.castAdd Nl p) = true ∧
          z (Fin.natAdd Np l) = true := by
    intro z hz
    rw [hex z] at hz
    exact of_decide_eq_true hz
  have least' : ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.TopForm.IsAO2 (Np + Nl) D →
      PEqualNP.MetaComplexity.circuitFun (Np + Nl) D =
        PEqualNP.MetaComplexity.circuitFun (Np + Nl) C → C.size ≤ D.size := by
    intro D hD e
    refine least D hD (fun z => ?_)
    rw [e]
    exact hex z
  obtain ⟨T, hT1, hT2⟩ := stuck
  have hT2' : ∀ w : ℕ, (∀ z : Fin (Np + Nl) → Bool,
      (C.wires (List.ofFn z)).getD w false = true →
        PEqualNP.MetaComplexity.circuitFun (Np + Nl) C z = true) →
      (∃ k < C.gates.length,
        (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op =
          PEqualNP.CircuitLowerBounds.GateOp.or ∧
        w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs) →
      ∀ k < C.gates.length,
        w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs → k ∈ T :=
    fun w hw => hT2 w (fun z hz => conv z (hw z hz))
  have fl := flat (Np + Nl) C ao least' ⟨T, hT1, hT2'⟩
  have gmem : ∀ k < C.gates.length,
      PEqualNP.MetaComplexity.NestedCover.gateAt C k ∈ C.gates := by
    intro k hk
    unfold PEqualNP.MetaComplexity.NestedCover.gateAt
    rw [List.getD_eq_getElem _ _ hk]
    exact List.getElem_mem hk
  have strong : ∀ w : ℕ, (∀ z : Fin (Np + Nl) → Bool,
      (C.wires (List.ofFn z)).getD w false = true →
        PEqualNP.MetaComplexity.circuitFun (Np + Nl) C z = true) →
      ∀ k < C.gates.length,
        w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs → k ∈ T := by
    intro w hw k hk hmem
    rcases ao.1 _ (gmem k hk) with hand | hor
    · exact absurd hw (fl k hk hand w hmem)
    · exact hT2' w hw ⟨k, hk, hor, hmem⟩ k hk hmem
  obtain ⟨S, closed, ands⟩ := rest Np Nl I C no4 ao hex least' ⟨T, hT1, strong⟩
  refine ⟨S false, S true, ?_, ?_, ?_⟩
  · intro w hw
    rcases closed false w hw with ⟨_, side⟩ | gate
    · exact Or.inl (by simpa using side)
    · exact Or.inr gate
  · intro w hw
    rcases closed true w hw with ⟨bound, side⟩ | gate
    · exact Or.inl ⟨by simpa using side, bound⟩
    · exact Or.inr gate
  · intro i hi hand
    obtain ⟨a, b, t, inputs, ha, hb⟩ := ands i hi hand
    refine ⟨a, b, inputs, ?_⟩
    cases t with
    | false => exact Or.inl ⟨ha, hb⟩
    | true => exact Or.inr ⟨ha, hb⟩
