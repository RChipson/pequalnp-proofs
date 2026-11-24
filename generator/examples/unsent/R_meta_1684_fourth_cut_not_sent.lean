import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_1684_1
    (hB : ∀ (n : ℕ) (marked : Finset ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.CircuitLowerBounds.HasLineDegree n marked C 1 → ∀ x : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n C x = true → (∀ y : Fin n → Bool, (∀ k : Fin n, k.val ∉ marked → x k = true → y k = true) → PEqualNP.MetaComplexity.circuitFun n C y = true) ∨ (∃ i : Fin n, i.val ∈ marked ∧ x i = true ∧ ∀ y : Fin n → Bool, (∀ k : Fin n, (k.val ∉ marked ∨ k = i) → x k = true → y k = true) → PEqualNP.MetaComplexity.circuitFun n C y = true))
    (hL : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; ¬∃ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 ∧ x2.size ≤ (63 : ℕ) ∧ PEqualNP.CircuitLowerBounds.HasLineDegree ((13 : ℕ) + (13 : ℕ)) (Finset.Ico (13 : ℕ) ((13 : ℕ) + (13 : ℕ))) x2 (1 : ℕ) ∧ (∀ (x3 x4 : Fin (13 : ℕ)), (∃ x5 ∈ x1, x3 = x4 + x5) → (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x2 fun (x6 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide (x6 = Fin.castAdd (13 : ℕ) x3 ∨ x6 = Fin.natAdd (13 : ℕ) x4)) = Bool.true) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), (∀ x4 ∉ x3, ∃ (x6 : Fin (13 : ℕ)), (∀ x7 ∈ x3, ¬∃ x9 ∈ x1, x7 = x6 + x9) ∧ ∃ x7 ∈ x1, x4 = x6 + x7) → ((¬∃ (x5 : Fin (13 : ℕ)), ∀ x6 ∈ x3, ∃ x8 ∈ x1, x6 = x5 + x8) ∧ ¬∃ (x5 : Fin (13 : ℕ)), ∀ (x6 : Fin (13 : ℕ)), (∀ x7 ∈ x3, ¬∃ x9 ∈ x1, x7 = x6 + x9) → ∃ x8 ∈ x1, x5 = x6 + x8) → (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x2 fun (x6 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide ((∃ x7 ∈ x3, x6 = Fin.castAdd (13 : ℕ) x7) ∨ ∃ (x7 : Fin (13 : ℕ)), x6 = Fin.natAdd (13 : ℕ) x7 ∧ ∀ x8 ∈ x3, ¬∃ x10 ∈ x1, x8 = x7 + x10)) = Bool.false)
    (hP : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; ¬∃ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 ∧ x2.size ≤ (63 : ℕ) ∧ PEqualNP.CircuitLowerBounds.HasLineDegree ((13 : ℕ) + (13 : ℕ)) (Finset.range (13 : ℕ)) x2 (1 : ℕ) ∧ (∀ (x3 x4 : Fin (13 : ℕ)), (∃ x5 ∈ x1, x3 = x4 + x5) → (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x2 fun (x6 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide (x6 = Fin.castAdd (13 : ℕ) x3 ∨ x6 = Fin.natAdd (13 : ℕ) x4)) = Bool.true) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), (∀ x4 ∉ x3, ∃ (x6 : Fin (13 : ℕ)), (∀ x7 ∈ x3, ¬∃ x9 ∈ x1, x7 = x6 + x9) ∧ ∃ x7 ∈ x1, x4 = x6 + x7) → ((¬∃ (x5 : Fin (13 : ℕ)), ∀ x6 ∈ x3, ∃ x8 ∈ x1, x6 = x5 + x8) ∧ ¬∃ (x5 : Fin (13 : ℕ)), ∀ (x6 : Fin (13 : ℕ)), (∀ x7 ∈ x3, ¬∃ x9 ∈ x1, x7 = x6 + x9) → ∃ x8 ∈ x1, x5 = x6 + x8) → (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x2 fun (x6 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide ((∃ x7 ∈ x3, x6 = Fin.castAdd (13 : ℕ) x7) ∨ ∃ (x7 : Fin (13 : ℕ)), x6 = Fin.natAdd (13 : ℕ) x7 ∧ ∀ x8 ∈ x3, ¬∃ x10 ∈ x1, x8 = x7 + x10)) = Bool.false)
    (hHard : have D : Finset (Fin 13) := {0, 1, 3, 9}; ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 63 ∧ ¬ PEqualNP.CircuitLowerBounds.HasLineDegree (13 + 13) (Finset.Ico 13 (13 + 13)) C 1 ∧ ¬ PEqualNP.CircuitLowerBounds.HasLineDegree (13 + 13) (Finset.range 13) C 1 ∧ (∀ p w : Fin 13, (∃ dd ∈ D, p = w + dd) → PEqualNP.MetaComplexity.circuitFun (13 + 13) C (fun k => decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 w)) = true) ∧ (∀ P : Finset (Fin 13), (∀ v : Fin 13, v ∉ P → ∃ w2 : Fin 13, (∀ pp ∈ P, ¬ (∃ dd ∈ D, pp = w2 + dd)) ∧ (∃ dd ∈ D, v = w2 + dd)) → ((∃ w3 : Fin 13, ∀ p3 ∈ P, (∃ dd ∈ D, p3 = w3 + dd)) ∨ (∃ v4 : Fin 13, ∀ w4 : Fin 13, (∀ pp ∈ P, ¬ (∃ dd ∈ D, pp = w4 + dd)) → (∃ dd ∈ D, v4 = w4 + dd))) → PEqualNP.MetaComplexity.circuitFun (13 + 13) C (fun kk : Fin (13 + 13) => decide ((∃ pp ∈ P, kk = Fin.castAdd 13 pp) ∨ (∃ ww : Fin 13, kk = Fin.natAdd 13 ww ∧ (∀ pp ∈ P, ¬ (∃ dd ∈ D, pp = ww + dd))))) = false))) :
    ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 63 ∧ (∀ p w : Fin 13, (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = w + dd) → PEqualNP.MetaComplexity.circuitFun (13 + 13) C (fun k => decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 w)) = true) ∧ (∀ P : Finset (Fin 13), (∀ v : Fin 13, v ∉ P → ∃ w2 : Fin 13, (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w2 + dd)) ∧ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), v = w2 + dd)) → ((∃ w3 : Fin 13, ∀ p3 ∈ P, (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p3 = w3 + dd)) ∨ (∃ v4 : Fin 13, ∀ w4 : Fin 13, (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w4 + dd)) → (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), v4 = w4 + dd))) → PEqualNP.MetaComplexity.circuitFun (13 + 13) C (fun kk : Fin (13 + 13) => decide ((∃ pp ∈ P, kk = Fin.castAdd 13 pp) ∨ (∃ ww : Fin 13, kk = Fin.natAdd 13 ww ∧ (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = ww + dd))))) = false)) := by
  have bt : ∀ b : Bool, ¬ b = false → b = true := by
    intro b
    cases b <;> simp
  have g1 : ∀ w w4 : Fin 13, (∀ pp : Fin 13, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w + dd) → ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w4 + dd)) → ∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), w = w4 + dd := by
    decide +kernel
  have g2 : ∀ pp v : Fin 13, v ≠ pp → ∃ w2 : Fin 13, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w2 + dd) ∧ ∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), v = w2 + dd := by
    decide +kernel
  rintro ⟨C, hM, hsz, hacc, hrej⟩
  by_cases hdL : PEqualNP.CircuitLowerBounds.HasLineDegree (13 + 13) (Finset.Ico 13 (13 + 13)) C 1
  · -- line-degree one over the lines: the circuit rejects every input of the stated shape
    refine hL ⟨C, hM, hsz, hdL, hacc, fun P _ _ => ?_⟩
    by_contra hne
    have ht := bt _ hne
    rcases hB (13 + 13) (Finset.Ico 13 (13 + 13)) C hM hdL _ ht with hy | ⟨i, hi, hxi, hy⟩
    · have hU := hrej Finset.univ (fun v hv => absurd (Finset.mem_univ v) hv)
        (Or.inr ⟨0, fun w4 h => (h w4 (Finset.mem_univ _) ⟨0, by simp, by simp⟩).elim⟩)
      refine Bool.false_ne_true (hU.symm.trans (hy _ ?_))
      intro k hk _
      have hk2 := k.isLt
      have hk' : k.val < 13 := by
        simp only [Finset.mem_Ico, not_and, not_lt] at hk
        omega
      simp only [decide_eq_true_eq]
      exact Or.inl ⟨⟨k.val, hk'⟩, Finset.mem_univ _, Fin.ext rfl⟩
    · have hi' : 13 ≤ i.val := by
        simp only [Finset.mem_Ico] at hi
        omega
      simp only [decide_eq_true_eq] at hxi
      rcases hxi with ⟨pp, _, hpp⟩ | ⟨w, hw, hmiss⟩
      · exfalso
        have h1 := congrArg Fin.val hpp
        have h2 := pp.isLt
        simp at h1
        omega
      · obtain ⟨P', hP'⟩ : ∃ P' : Finset (Fin 13), ∀ p : Fin 13, p ∈ P' ↔ ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = w + dd) :=
          ⟨Finset.univ.filter (fun p : Fin 13 => ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = w + dd)), by intro p; simp⟩
        have hcl : ∀ v : Fin 13, v ∉ P' → ∃ w2 : Fin 13, (∀ pp ∈ P', ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w2 + dd)) ∧ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), v = w2 + dd) := by
          intro v hv
          refine ⟨w, fun pp hpp => (hP' pp).mp hpp, ?_⟩
          by_contra hc
          exact hv ((hP' v).mpr hc)
        have hF := hrej P' hcl
          (Or.inr ⟨w, fun w4 h => g1 w w4 (fun pp hpp => h pp ((hP' pp).mpr hpp))⟩)
        refine Bool.false_ne_true (hF.symm.trans (hy _ ?_))
        intro k hk hxk
        simp only [decide_eq_true_eq] at hxk ⊢
        rcases hk with hk | hk
        · have hk2 := k.isLt
          have hk' : k.val < 13 := by
            simp only [Finset.mem_Ico, not_and, not_lt] at hk
            omega
          rcases hxk with ⟨pp, hppP, hkpp⟩ | ⟨ww, hkw, _⟩
          · exact Or.inl ⟨pp, (hP' pp).mpr (hmiss pp hppP), hkpp⟩
          · exfalso
            have h1 := congrArg Fin.val hkw
            simp at h1
            omega
        · rw [hk]
          exact Or.inr ⟨w, hw, fun pp hpp => (hP' pp).mp hpp⟩
  · by_cases hdP : PEqualNP.CircuitLowerBounds.HasLineDegree (13 + 13) (Finset.range 13) C 1
    · -- line-degree one over the points: the dual argument
      refine hP ⟨C, hM, hsz, hdP, hacc, fun P _ _ => ?_⟩
      by_contra hne
      have ht := bt _ hne
      rcases hB (13 + 13) (Finset.range 13) C hM hdP _ ht with hy | ⟨i, hi, hxi, hy⟩
      · have hE := hrej ∅ (fun v _ => ⟨v, fun pp hpp => by simp at hpp, ⟨0, by simp, by simp⟩⟩)
          (Or.inl ⟨0, fun p3 hp3 => by simp at hp3⟩)
        refine Bool.false_ne_true (hE.symm.trans (hy _ ?_))
        intro k hk _
        have hk2 := k.isLt
        have hk' : 13 ≤ k.val := by
          simp only [Finset.mem_range, not_lt] at hk
          exact hk
        simp only [decide_eq_true_eq]
        refine Or.inr ⟨⟨k.val - 13, by omega⟩, Fin.ext ?_, fun pp hpp => by simp at hpp⟩
        show k.val = 13 + (k.val - 13)
        omega
      · have hi' : i.val < 13 := by
          simp only [Finset.mem_range] at hi
          exact hi
        simp only [decide_eq_true_eq] at hxi
        rcases hxi with ⟨pp, hppP, hipp⟩ | ⟨w, hw, _⟩
        · have hcl : ∀ v : Fin 13, v ∉ ({pp} : Finset (Fin 13)) → ∃ w2 : Fin 13, (∀ q ∈ ({pp} : Finset (Fin 13)), ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), q = w2 + dd)) ∧ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), v = w2 + dd) := by
            intro v hv
            have hvne : v ≠ pp := by
              intro e
              exact hv (by rw [e]; exact Finset.mem_singleton_self pp)
            obtain ⟨w2, h1, h2⟩ := g2 pp v hvne
            refine ⟨w2, fun q hq => ?_, h2⟩
            rw [Finset.mem_singleton.mp hq]
            exact h1
          have hS := hrej {pp} hcl
            (Or.inl ⟨pp, fun p3 hp3 => ⟨0, by simp, by rw [Finset.mem_singleton.mp hp3]; simp⟩⟩)
          refine Bool.false_ne_true (hS.symm.trans (hy _ ?_))
          intro k hk hxk
          simp only [decide_eq_true_eq] at hxk ⊢
          rcases hk with hk | hk
          · have hk' : 13 ≤ k.val := by
              simp only [Finset.mem_range, not_lt] at hk
              exact hk
            rcases hxk with ⟨q, _, hkq⟩ | ⟨ww, hkw, hmiss⟩
            · exfalso
              have h1 := congrArg Fin.val hkq
              have h2 := q.isLt
              simp at h1
              omega
            · refine Or.inr ⟨ww, hkw, fun q hq => ?_⟩
              rw [Finset.mem_singleton.mp hq]
              exact hmiss pp hppP
          · rw [hk]
            exact Or.inl ⟨pp, Finset.mem_singleton_self pp, hipp⟩
        · exfalso
          have h1 := congrArg Fin.val hw
          simp at h1
          omega
    · exact hHard ⟨C, hM, hsz, hdL, hdP, hacc, hrej⟩
