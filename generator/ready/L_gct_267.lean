import Mathlib
import PEqualNP.Defs

-- Proof pattern adapted from the accepted proof L-gct-271: an odd and an even polynomial with
-- all roots real, and sign changes of the product plus one at quarter-integer points.

open Polynomial

namespace PEqualNP.Outside.L_gct_267

noncomputable def F : Polynomial ℝ :=
  X ^ 5 - C 5 * X ^ 3 + C 4 * X

noncomputable def G : Polynomial ℝ :=
  C 16 * X ^ 4 - C 40 * X ^ 2 + C 9

noncomputable def H : Polynomial ℝ := F * G + 1

noncomputable def T (k : ℕ) : ℝ := (2 * (k : ℝ) - 9) / 4

lemma F_support_card : F.support.card ≤ 3 := by
  have hsub : F.support ⊆ {1, 3, 5} := by
    intro n hn
    rw [mem_support_iff] at hn
    by_contra hmem
    apply hn
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hmem
    obtain ⟨h1, h3, h5⟩ := hmem
    simp [F, coeff_X_pow, coeff_C_mul, coeff_X, h1, h3, h5, Ne.symm h1, Ne.symm h3,
      Ne.symm h5]
  calc F.support.card ≤ ({1, 3, 5} : Finset ℕ).card := Finset.card_le_card hsub
    _ ≤ 3 := by decide

lemma G_support_card : G.support.card ≤ 3 := by
  have hsub : G.support ⊆ {0, 2, 4} := by
    intro n hn
    rw [mem_support_iff] at hn
    by_contra hmem
    apply hn
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hmem
    obtain ⟨h0, h2, h4⟩ := hmem
    simp [G, coeff_X_pow, coeff_C_mul, coeff_C, h0, h2, h4, Ne.symm h0, Ne.symm h2,
      Ne.symm h4]
  calc G.support.card ≤ ({0, 2, 4} : Finset ℕ).card := Finset.card_le_card hsub
    _ ≤ 3 := by decide

lemma root_between (p : Polynomial ℝ) (a b : ℝ) (hab : a ≤ b)
    (h : p.eval a * p.eval b < 0) : ∃ r ∈ Set.Ioo a b, p.eval r = 0 := by
  have hc : ContinuousOn (fun x => p.eval x) (Set.Icc a b) := p.continuous.continuousOn
  rcases lt_or_gt_of_ne (show p.eval a ≠ 0 by intro h0; simp [h0] at h) with ha | ha
  · have hb : 0 < p.eval b := by
      by_contra hb
      push Not at hb
      nlinarith
    have := intermediate_value_Ioo hab hc
    obtain ⟨r, hr, hr0⟩ := this ⟨ha, hb⟩
    exact ⟨r, hr, by simpa using hr0⟩
  · have hb : p.eval b < 0 := by
      by_contra hb
      push Not at hb
      nlinarith
    have := intermediate_value_Ioo' hab hc
    obtain ⟨r, hr, hr0⟩ := this ⟨hb, ha⟩
    exact ⟨r, hr, by simpa using hr0⟩

set_option maxHeartbeats 4000000 in
lemma H_sign (k : Fin 9) : H.eval (T k) * H.eval (T ((k : ℕ) + 1)) < 0 := by
  fin_cases k <;>
    simp [H, F, G, T, eval_add, eval_mul, eval_sub, eval_pow, eval_X, eval_C, eval_one] <;>
    norm_num

lemma H_ne_zero : H ≠ 0 := by
  intro h
  have := H_sign 0
  simp [h] at this

lemma exists_roots : ∃ s : Finset ℝ, s.card = 9 ∧ ∀ x ∈ s, x ∈ H.roots.toFinset := by
  have hr : ∀ k : Fin 9, ∃ r ∈ Set.Ioo (T k) (T ((k : ℕ) + 1)), H.eval r = 0 := by
    intro k
    apply root_between
    · unfold T
      push_cast
      linarith
    · exact H_sign k
  choose r hr hr0 using hr
  have hmono : StrictMono r := by
    intro i j hij
    have h1 : r i < T ((i : ℕ) + 1) := (hr i).2
    have h2 : T (j : ℕ) < r j := (hr j).1
    have h3 : T ((i : ℕ) + 1) ≤ T (j : ℕ) := by
      unfold T
      have h4 : (i : ℕ) + 1 ≤ (j : ℕ) := hij
      have h5 : ((i : ℕ) : ℝ) + 1 ≤ ((j : ℕ) : ℝ) := by exact_mod_cast h4
      push_cast
      linarith
    linarith
  refine ⟨Finset.univ.image r, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hmono.injective]
    simp
  · intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    rw [Multiset.mem_toFinset, mem_roots H_ne_zero]
    exact hr0 i

end PEqualNP.Outside.L_gct_267

theorem PEqualNP.Outside.L_gct_267 : ¬ (∀ f g : Polynomial ℝ, (f.support.card ≤ 3 ∧ g.support.card ≤ 3) → ((f * g + 1).roots.toFinset).card ≤ 7) := by
  intro hall
  have hb := hall PEqualNP.Outside.L_gct_267.F PEqualNP.Outside.L_gct_267.G
    ⟨PEqualNP.Outside.L_gct_267.F_support_card, PEqualNP.Outside.L_gct_267.G_support_card⟩
  obtain ⟨s, hs, hsub⟩ := PEqualNP.Outside.L_gct_267.exists_roots
  have hle : s.card ≤ (PEqualNP.Outside.L_gct_267.H.roots.toFinset).card :=
    Finset.card_le_card (fun x hx => hsub x hx)
  have hb' : (PEqualNP.Outside.L_gct_267.H.roots.toFinset).card ≤ 7 := hb
  omega
