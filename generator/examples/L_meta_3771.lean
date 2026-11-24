import Mathlib
import PEqualNP.Defs

-- Four distinct points forbid all but at most three partners: the four translates of
-- the difference set cover at least ten of the thirteen residues. Each point's forbidden
-- partners are packed into one number, and every choice of four points is checked by the
-- kernel on plain numbers, in increasing order only.
namespace PEqualNP.Outside.L_meta_3771

def masks : List Nat := [523, 4357, 6274, 3137, 5664, 2832, 1416, 708, 354, 177, 4184, 2092, 1046]

lemma mask_ok : ∀ a b : Fin 13, (masks.getD a.val 0).testBit b.val =
    decide (a + b ∈ ({0, 1, 3, 9} : Finset (Fin 13))) := by decide +kernel

def union4 (a1 a2 a3 a4 : Nat) : Nat :=
  Nat.lor (Nat.lor (masks.getD a1 0) (masks.getD a2 0)) (Nat.lor (masks.getD a3 0) (masks.getD a4 0))

def freeN (a1 a2 a3 a4 : Nat) : List Nat :=
  (List.range 13).filter fun b => !(union4 a1 a2 a3 a4).testBit b

def chk : Bool :=
  (List.range 13).all fun a1 => (List.range 13).all fun a2 => Nat.ble a2 a1 ||
    (List.range 13).all fun a3 => Nat.ble a3 a2 ||
      (List.range 13).all fun a4 => Nat.ble a4 a3 || Nat.ble (freeN a1 a2 a3 a4).length 3

lemma chk_ok : chk = true := by decide +kernel

lemma four (a1 a2 a3 a4 : Fin 13) (h12 : a1 < a2) (h23 : a2 < a3) (h34 : a3 < a4) :
    (freeN a1.val a2.val a3.val a4.val).length ≤ 3 := by
  have v12 : a1.val < a2.val := h12
  have v23 : a2.val < a3.val := h23
  have v34 : a3.val < a4.val := h34
  have h := chk_ok
  unfold chk at h
  have h1 := List.all_eq_true.mp h a1.val (List.mem_range.mpr a1.isLt)
  have h2 := List.all_eq_true.mp h1 a2.val (List.mem_range.mpr a2.isLt)
  rw [Bool.or_eq_true] at h2
  rcases h2 with h2 | h2
  · have := Nat.le_of_ble_eq_true h2
    omega
  have h3 := List.all_eq_true.mp h2 a3.val (List.mem_range.mpr a3.isLt)
  rw [Bool.or_eq_true] at h3
  rcases h3 with h3 | h3
  · have := Nat.le_of_ble_eq_true h3
    omega
  have h4 := List.all_eq_true.mp h3 a4.val (List.mem_range.mpr a4.isLt)
  rw [Bool.or_eq_true] at h4
  rcases h4 with h4 | h4
  · have := Nat.le_of_ble_eq_true h4
    omega
  exact Nat.le_of_ble_eq_true h4

lemma first_four (A : Finset (Fin 13)) (hA : 4 ≤ A.card) :
    ∃ a1 a2 a3 a4 : Fin 13, a1 ∈ A ∧ a2 ∈ A ∧ a3 ∈ A ∧ a4 ∈ A ∧ a1 < a2 ∧ a2 < a3 ∧ a3 < a4 := by
  have ne1 : A.Nonempty := Finset.card_pos.mp (by omega)
  have m1 : A.min' ne1 ∈ A := Finset.min'_mem A ne1
  have c1 : (A.erase (A.min' ne1)).card = A.card - 1 := Finset.card_erase_of_mem m1
  have ne2 : (A.erase (A.min' ne1)).Nonempty := Finset.card_pos.mp (by omega)
  have m2 := Finset.min'_mem _ ne2
  have k2 := Finset.mem_erase.mp m2
  have c2 : ((A.erase (A.min' ne1)).erase ((A.erase (A.min' ne1)).min' ne2)).card =
      (A.erase (A.min' ne1)).card - 1 := Finset.card_erase_of_mem m2
  have ne3 : ((A.erase (A.min' ne1)).erase ((A.erase (A.min' ne1)).min' ne2)).Nonempty :=
    Finset.card_pos.mp (by omega)
  have m3 := Finset.min'_mem _ ne3
  have k3 := Finset.mem_erase.mp m3
  have k3b := Finset.mem_erase.mp k3.2
  have c3 := Finset.card_erase_of_mem m3
  have ne4 : (((A.erase (A.min' ne1)).erase ((A.erase (A.min' ne1)).min' ne2)).erase
      (((A.erase (A.min' ne1)).erase ((A.erase (A.min' ne1)).min' ne2)).min' ne3)).Nonempty :=
    Finset.card_pos.mp (by omega)
  have m4 := Finset.min'_mem _ ne4
  have k4 := Finset.mem_erase.mp m4
  have k4b := Finset.mem_erase.mp k4.2
  have k4c := Finset.mem_erase.mp k4b.2
  refine ⟨_, _, _, _, m1, k2.2, k3b.2, k4c.2, ?_, ?_, ?_⟩
  · exact lt_of_le_of_ne (Finset.min'_le A _ k2.2) (Ne.symm k2.1)
  · exact lt_of_le_of_ne (Finset.min'_le _ _ k3.2) (Ne.symm k3.1)
  · exact lt_of_le_of_ne (Finset.min'_le _ _ k4.2) (Ne.symm k4.1)

end PEqualNP.Outside.L_meta_3771

open PEqualNP.Outside.L_meta_3771 in
theorem PEqualNP.Outside.L_meta_3771 : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; ∀ (x2 x3 : Finset (Fin (13 : ℕ))), (∀ x4 ∈ x2, ∀ x6 ∈ x3, x4 + x6 ∉ x1) → x2.card ≤ (3 : ℕ) ∨ x3.card ≤ (3 : ℕ) := by
  intro D A B h
  by_contra hcon
  push Not at hcon
  obtain ⟨hA, hB⟩ := hcon
  obtain ⟨a1, a2, a3, a4, h1, h2, h3, h4, l12, l23, l34⟩ := first_four A (by omega)
  have nb : ∀ a ∈ A, ∀ b ∈ B, (masks.getD a.val 0).testBit b.val = false := by
    intro a ha b hb
    rw [mask_ok]
    exact decide_eq_false (h a ha b hb)
  have hsub : B.image (fun b : Fin 13 => b.val) ⊆ (freeN a1.val a2.val a3.val a4.val).toFinset := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hx
    rw [List.mem_toFinset]
    unfold freeN
    rw [List.mem_filter]
    refine ⟨List.mem_range.mpr b.isLt, ?_⟩
    have hu : (union4 a1.val a2.val a3.val a4.val).testBit b.val = false := by
      show ((masks.getD a1.val 0 ||| masks.getD a2.val 0) |||
        (masks.getD a3.val 0 ||| masks.getD a4.val 0)).testBit b.val = false
      rw [Nat.testBit_or, Nat.testBit_or, Nat.testBit_or, nb a1 h1 b hb, nb a2 h2 b hb,
        nb a3 h3 b hb, nb a4 h4 b hb]
      rfl
    rw [hu]
    rfl
  have hcard : (B.image (fun b : Fin 13 => b.val)).card = B.card :=
    Finset.card_image_of_injective _ Fin.val_injective
  have hle := ((Finset.card_le_card hsub).trans (List.toFinset_card_le _)).trans
    (four a1 a2 a3 a4 l12 l23 l34)
  omega
