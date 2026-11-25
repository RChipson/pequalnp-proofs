import Mathlib
import PEqualNP.Defs

open Polynomial

namespace PEqualNP.Outside.L_gct_265

noncomputable def F : Polynomial ℝ :=
  C 2116 * X ^ 4 - C 8556 * X ^ 3 + C 12973 * X ^ 2 - C 8742 * X + C 2209

noncomputable def G : Polynomial ℝ :=
  - C (13 / 21160) - C (25 / 529) * X ^ 3 - C (2750 / 529) * X ^ 14 - C (207500 / 529) * X ^ 50 - C (9500000 / 529) * X ^ 170

noncomputable def H : Polynomial ℝ := F * G + 1

noncomputable def T (k : ℕ) : ℝ :=
  if k = 0 then 0 else if k = 1 then (1 / 5) else if k = 2 then (1 / 3) else if k = 3 then (3 / 5) else
  if k = 4 then (3 / 4) else if k = 5 then (6 / 7) else if k = 6 then (10 / 11) else if k = 7 then (20 / 21) else
  if k = 8 then (40 / 41) else if k = 9 then 1 else if k = 10 then (53 / 52) else if k = 11 then (47 / 46) else
  (8 / 7)

lemma F_support_card : F.support.card ≤ 5 := by
  have hsub : F.support ⊆ {0, 1, 2, 3, 4} := by
    intro n hn
    rw [mem_support_iff] at hn
    by_contra hmem
    apply hn
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hmem
    obtain ⟨h0, h1, h2, h3, h4⟩ := hmem
    simp [F, coeff_X_pow, coeff_C_mul, coeff_X, coeff_C, h0, h1, h2, h3, h4, Ne.symm h0, Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4]
  calc F.support.card ≤ ({0, 1, 2, 3, 4} : Finset ℕ).card := Finset.card_le_card hsub
    _ ≤ 5 := by decide

lemma G_support_card : G.support.card ≤ 5 := by
  have hsub : G.support ⊆ {0, 3, 14, 50, 170} := by
    intro n hn
    rw [mem_support_iff] at hn
    by_contra hmem
    apply hn
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hmem
    obtain ⟨h0, h3, h14, h50, h170⟩ := hmem
    simp [G, coeff_X_pow, coeff_C_mul, coeff_X, coeff_C, h0, h3, h14, h50, h170, Ne.symm h0, Ne.symm h3, Ne.symm h14, Ne.symm h50, Ne.symm h170]
  calc G.support.card ≤ ({0, 3, 14, 50, 170} : Finset ℕ).card := Finset.card_le_card hsub
    _ ≤ 5 := by decide

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
lemma H_sign : ∀ k : ℕ, k < 12 → H.eval (T k) * H.eval (T (k + 1)) < 0 := by
  intro k hk
  interval_cases k <;>
    simp [H, F, G, T, eval_add, eval_mul, eval_sub, eval_neg, eval_pow, eval_X, eval_C, eval_one] <;>
    norm_num

lemma T_lt : ∀ k : ℕ, k < 12 → T k < T (k + 1) := by
  intro k hk
  interval_cases k <;> simp [T] <;> norm_num

lemma T_nonneg : ∀ k : ℕ, k < 12 → 0 ≤ T k := by
  intro k hk
  interval_cases k <;> simp [T] <;> norm_num

lemma H_ne_zero : H ≠ 0 := by
  intro h
  have := H_sign 0 (by norm_num)
  simp [h] at this

lemma exists_roots : ∃ s : Finset ℝ, s.card = 12 ∧ ∀ x ∈ s, x ∈ H.roots.toFinset ∧ 0 < x := by
  have hr : ∀ k : Fin 12, ∃ r ∈ Set.Ioo (T k) (T ((k : ℕ) + 1)), H.eval r = 0 := by
    intro k
    exact root_between H _ _ (le_of_lt (T_lt k k.isLt)) (H_sign k k.isLt)
  choose r hr hr0 using hr
  have hmono : StrictMono r := by
    apply Fin.strictMono_iff_lt_succ.2
    intro i
    have h1 : r i.castSucc < T ((i.castSucc : ℕ) + 1) := (hr i.castSucc).2
    have h2 : T (i.succ : ℕ) < r i.succ := (hr i.succ).1
    have h3 : ((i.castSucc : Fin 12) : ℕ) + 1 = (i.succ : ℕ) := by simp
    rw [h3] at h1
    exact lt_trans h1 h2
  refine ⟨Finset.univ.image r, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hmono.injective]
    simp
  · intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    refine ⟨?_, lt_of_le_of_lt (T_nonneg i i.isLt) (hr i).1⟩
    rw [Multiset.mem_toFinset, mem_roots H_ne_zero]
    exact hr0 i

end PEqualNP.Outside.L_gct_265

theorem PEqualNP.Outside.L_gct_265 : ¬ (∀ f g : Polynomial ℝ, (f.support.card ≤ 5 ∧ g.support.card ≤ 5) → ((f * g + 1).roots.toFinset.filter (fun x : ℝ => 0 < x)).card ≤ 11) := by
  intro hall
  have hb := hall PEqualNP.Outside.L_gct_265.F PEqualNP.Outside.L_gct_265.G
    ⟨PEqualNP.Outside.L_gct_265.F_support_card, PEqualNP.Outside.L_gct_265.G_support_card⟩
  obtain ⟨s, hs, hsub⟩ := PEqualNP.Outside.L_gct_265.exists_roots
  have hle : s.card ≤ ((PEqualNP.Outside.L_gct_265.H.roots.toFinset).filter (fun x : ℝ => 0 < x)).card :=
    Finset.card_le_card (fun x hx => Finset.mem_filter.mpr (hsub x hx))
  have hb' : ((PEqualNP.Outside.L_gct_265.H.roots.toFinset).filter (fun x : ℝ => 0 < x)).card ≤ 11 := hb
  omega
