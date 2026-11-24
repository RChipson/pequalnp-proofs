import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3574

-- The positions of the list whose set has at least two members, lies inside x and does not
-- lie inside c.
def inside {n : ℕ} (L : List (Finset (Fin n))) (x c : Finset (Fin n)) : Finset (Fin L.length) :=
  Finset.univ.filter fun i => 1 < (L.get i).card ∧ L.get i ⊆ x ∧ ¬ L.get i ⊆ c

def del {n : ℕ} (x c : Finset (Fin n)) : ℕ := if Disjoint x c then 1 else 0

-- The bound that is carried through the list: outside any set c, a set has at most as many
-- members as there are counted positions, plus one when it does not meet c.
def Part {n : ℕ} (L : List (Finset (Fin n))) (x : Finset (Fin n)) : Prop :=
  ∀ c : Finset (Fin n), (x \ c).card ≤ (inside L x c).card + del x c

lemma part_small {n : ℕ} (L : List (Finset (Fin n))) (x : Finset (Fin n)) (hx : x.card ≤ 1) :
    Part L x := by
  intro c
  unfold del
  by_cases hd : Disjoint x c
  · rw [if_pos hd]
    have := Finset.card_le_card (Finset.sdiff_subset (s := x) (t := c))
    omega
  · rw [if_neg hd]
    obtain ⟨e, hex, hec⟩ := Finset.not_disjoint_iff.mp hd
    have hempty : x \ c = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro y hy
      obtain ⟨hyx, hyc⟩ := Finset.mem_sdiff.mp hy
      have := Finset.card_le_one.mp hx y hyx e hex
      exact hyc (this ▸ hec)
    rw [hempty]
    simp

lemma part_union {n : ℕ} (L : List (Finset (Fin n))) (k : ℕ) (hk : k < L.length)
    (a b : Finset (Fin n)) (hs : L[k] = a ∪ b) (pa : Part L a) (pb : Part L b) :
    Part L L[k] := by
  intro c
  by_cases hsc : L[k] ⊆ c
  · rw [Finset.sdiff_eq_empty_iff_subset.mpr hsc]
    simp
  by_cases hcard : (L[k]).card ≤ 1
  · exact part_small L _ hcard c
  have hcard' : 1 < (L[k]).card := by omega
  have has : a ⊆ L[k] := hs ▸ Finset.subset_union_left
  have hbs : b ⊆ L[k] := hs ▸ Finset.subset_union_right
  by_cases hsa : L[k] ⊆ a
  · have e : a = L[k] := Finset.Subset.antisymm has hsa
    have := pa c
    rwa [e] at this
  by_cases hsb : L[k] ⊆ b
  · have e : b = L[k] := Finset.Subset.antisymm hbs hsb
    have := pb c
    rwa [e] at this
  have hkmem : (⟨k, hk⟩ : Fin L.length) ∈ inside L L[k] c := by
    simp only [inside, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hcard', Finset.Subset.refl _, hsc⟩
  have hA : inside L a c ⊆ inside L L[k] c := by
    intro i hi
    simp only [inside, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact ⟨hi.1, hi.2.1.trans has, hi.2.2⟩
  have hB : inside L b (c ∪ a) ⊆ inside L L[k] c := by
    intro i hi
    simp only [inside, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact ⟨hi.1, hi.2.1.trans hbs, fun h => hi.2.2 (h.trans Finset.subset_union_left)⟩
  have hdisj : Disjoint (inside L a c) (inside L b (c ∪ a)) := by
    rw [Finset.disjoint_left]
    intro i hi hj
    simp only [inside, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
    exact hj.2.2 (hi.2.1.trans Finset.subset_union_right)
  have hkA : (⟨k, hk⟩ : Fin L.length) ∉ inside L a c := by
    intro h
    simp only [inside, Finset.mem_filter, Finset.mem_univ, true_and] at h
    exact hsa h.2.1
  have hkB : (⟨k, hk⟩ : Fin L.length) ∉ inside L b (c ∪ a) := by
    intro h
    simp only [inside, Finset.mem_filter, Finset.mem_univ, true_and] at h
    exact hsb h.2.1
  have hcount : (inside L a c).card + (inside L b (c ∪ a)).card + 1 ≤ (inside L L[k] c).card := by
    have hsub : insert (⟨k, hk⟩ : Fin L.length) (inside L a c ∪ inside L b (c ∪ a)) ⊆ inside L L[k] c := by
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact hkmem
      · rcases Finset.mem_union.mp hi with hi | hi
        · exact hA hi
        · exact hB hi
    have hnot : (⟨k, hk⟩ : Fin L.length) ∉ inside L a c ∪ inside L b (c ∪ a) := by
      intro h
      rcases Finset.mem_union.mp h with h | h
      · exact hkA h
      · exact hkB h
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hnot, Finset.card_union_of_disjoint hdisj] at h1
    exact h1
  have hsplit : L[k] \ c ⊆ (a \ c) ∪ (b \ (c ∪ a)) := by
    intro e he
    obtain ⟨hes, hec⟩ := Finset.mem_sdiff.mp he
    rw [hs] at hes
    by_cases hea : e ∈ a
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hea, hec⟩)
    · have heb : e ∈ b := (Finset.mem_union.mp hes).resolve_left hea
      refine Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨heb, fun h => ?_⟩)
      rcases Finset.mem_union.mp h with h | h
      · exact hec h
      · exact hea h
  have hle : (L[k] \ c).card ≤ (a \ c).card + (b \ (c ∪ a)).card :=
    (Finset.card_le_card hsplit).trans (Finset.card_union_le _ _)
  have hdel : del a c + del b (c ∪ a) ≤ 1 + del L[k] c := by
    unfold del
    by_cases h1 : Disjoint a c
    · by_cases h2 : Disjoint b (c ∪ a)
      · have h3 : Disjoint L[k] c := by
          rw [hs]
          exact Finset.disjoint_union_left.mpr ⟨h1, h2.mono_right Finset.subset_union_left⟩
        rw [if_pos h1, if_pos h2, if_pos h3]
      · rw [if_pos h1, if_neg h2]
        split <;> omega
    · rw [if_neg h1]
      split <;> split <;> omega
  have h1 := pa c
  have h2 := pb (c ∪ a)
  omega

lemma all_parts {n : ℕ} (L : List (Finset (Fin n)))
    (H : ∀ (k : ℕ) (s : Finset (Fin n)), L[k]? = some s →
      ∃ a b : Finset (Fin n), s = a ∪ b ∧ (a.card ≤ 1 ∨ a ∈ List.take k L) ∧
        (b.card ≤ 1 ∨ b ∈ List.take k L)) :
    ∀ (k : ℕ) (hk : k < L.length), Part L L[k] := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    obtain ⟨a, b, hs, ha, hb⟩ := H k L[k] (by simp)
    have earlier : ∀ x : Finset (Fin n), (x.card ≤ 1 ∨ x ∈ List.take k L) → Part L x := by
      intro x hx
      rcases hx with hx | hx
      · exact part_small L x hx
      · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
        have hi' : i < k ∧ i < L.length := by
          simp only [List.length_take] at hi
          omega
        rw [List.getElem_take]
        exact ih i hi'.1 hi'.2
    exact part_union L k hk a b hs (earlier a ha) (earlier b hb)

lemma main {n : ℕ} (L : List (Finset (Fin n)))
    (H : ∀ (k : ℕ) (s : Finset (Fin n)), L[k]? = some s →
      ∃ a b : Finset (Fin n), s = a ∪ b ∧ (a.card ≤ 1 ∨ a ∈ List.take k L) ∧
        (b.card ≤ 1 ∨ b ∈ List.take k L)) :
    ∀ s ∈ L, s.card ≤
      Fintype.card { i : Fin L.length // 1 < (L.get i).card ∧ L.get i ⊆ s } + 1 := by
  intro s hs
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hs
  have h := all_parts L H k hk ∅
  have hd : del L[k] ∅ ≤ 1 := by
    unfold del
    split <;> omega
  have hsub : inside L L[k] ∅ ⊆
      Finset.univ.filter (fun i : Fin L.length => 1 < (L.get i).card ∧ L.get i ⊆ L[k]) := by
    intro i hi
    simp only [inside, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact ⟨hi.1, hi.2.1⟩
  have hc := Finset.card_le_card hsub
  rw [Fintype.card_subtype]
  simp only [Finset.sdiff_empty] at h
  omega

end PEqualNP.Outside.L_meta_3574

theorem PEqualNP.Outside.L_meta_3574 : ∀ (x1 : ℕ) (x2 : List (Finset (Fin x1))), (∀ (x3 : ℕ) (x4 : Finset (Fin x1)), x2[x3]? = Option.some x4 → ∃ (x6 : Finset (Fin x1)) (x7 : Finset (Fin x1)), x4 = x6 ∪ x7 ∧ (x6.card ≤ (1 : ℕ) ∨ x6 ∈ List.take x3 x2) ∧ (x7.card ≤ (1 : ℕ) ∨ x7 ∈ List.take x3 x2)) → ∀ x4 ∈ x2, x4.card ≤ Fintype.card { x6 : Fin x2.length // (1 : ℕ) < (x2.get x6).card ∧ x2.get x6 ⊆ x4 } + (1 : ℕ) :=
  fun n L H => PEqualNP.Outside.L_meta_3574.main L H
