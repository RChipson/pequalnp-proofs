import Cert

-- GLUE-BEGIN
-- New for this step: the two given wires are put back as the first two gates of a
-- circuit on the nine inputs. The constant wire is never read by a derivation. If the
-- OR wire is read, one more gate rebuilds it from its two inputs (or it is an input
-- itself), so in every case the checked frontier certificate for fourteen gates
-- excludes it.
namespace PEqualNP.Outside.L_meta_3116
namespace Glue
open PEqualNP.CircuitLowerBounds Main1672

def gF : Gate := ⟨.or, []⟩
def gO (a b : Nat) : Gate := ⟨.or, [a, b]⟩
def R (a : Fin 9) : Sig := raw.getD a.val zero
def sO (a b : Fin 9) : Sig := gv (raw ++ [zero]) (gO a.val b.val)

lemma sF_zero : gv raw gF = zero := by decide +kernel
lemma sO_eq : ∀ a b : Fin 9, sO a b = bin true (R a) (R b) := by decide +kernel
lemma R_mem : ∀ a : Fin 9, R a ∈ raw := by decide +kernel
lemma R_inj : ∀ a b : Fin 9, a ≠ b → R a ≠ R b := by decide +kernel
lemma R_ne : ∀ a : Fin 9, R a ≠ zero ∧ R a ≠ one := by decide +kernel
lemma fresh : ∀ a b : Fin 9, a ≠ b →
    bin true (R a) (R b) ≠ R a ∧ bin true (R a) (R b) ≠ R b := by decide +kernel
lemma idem : ∀ a : Fin 9, bin true (R a) (R a) = R a := by decide +kernel

lemma R_proper (a : Fin 9) : proper (R a) :=
  ⟨raw_valid (R a) (R_mem a), (R_ne a).1, (R_ne a).2⟩

def extend (a b : Nat) (C : Circuit) : Circuit := ⟨gF :: gO a b :: C.gates, C.output⟩

lemma extend_fan (a b : Nat) (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C) :
    PEqualNP.MetaComplexity.FanInTwo (extend a b C) := by
  intro g hg
  simp only [extend, List.mem_cons] at hg
  rcases hg with rfl | rfl | hg
  · exact ⟨by simp [gF], by simp [gF]⟩
  · exact ⟨by simp [gO], by simp [gO]⟩
  · exact h g hg

lemma extend_eval (a b : Nat) (C : Circuit) (x : Fin 9 → Bool) :
    (extend a b C).eval (List.ofFn x) =
      C.eval (List.ofFn x ++ [false] ++
        [GateOp.or.eval [(List.ofFn x ++ [false]).getD a false,
          (List.ofFn x ++ [false]).getD b false]]) := rfl

lemma target_mem (a b : Fin 9) (C : Circuit) (hf : PEqualNP.MetaComplexity.FanInTwo C)
    (he : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [false] ++
        [GateOp.or.eval [(List.ofFn x ++ [false]).getD a.val false,
          (List.ofFn x ++ [false]).getD b.val false]]) = edgeF x) :
    target ∈ execute C.gates (raw ++ [zero] ++ [sO a b]) := by
  have h := circuit_target (extend a.val b.val C) (extend_fan a.val b.val C hf)
    (fun x => (extend_eval a.val b.val C x).trans (he x))
  change target ∈ execute C.gates ((raw ++ [gv raw gF]) ++
    [gv (raw ++ [gv raw gF]) (gO a.val b.val)]) at h
  rw [sF_zero] at h
  exact h

lemma core (a b : Fin 9) (C : Circuit) (hf : PEqualNP.MetaComplexity.FanInTwo C)
    (hle : C.gates.length ≤ 13)
    (htgt : target ∈ execute C.gates (raw ++ [zero] ++ [sO a b])) : False := by
  have hvO : Valid (sO a b) := by
    rw [sO_eq]
    exact valid_bin (raw_valid _ (R_mem a)) (raw_valid _ (R_mem b))
  have hvW : ∀ s ∈ raw ++ [zero] ++ [sO a b], Valid s := by
    intro s hs
    simp only [List.mem_append, List.mem_singleton] at hs
    rcases hs with (hs | rfl) | rfl
    · exact raw_valid s hs
    · exact valid_zero
    · exact hvO
  obtain ⟨k, t, S, hk, hlive, hsub⟩ :=
    extract C.gates (raw ++ [zero] ++ [sO a b]) hvW (fun g hg => hf g hg) htgt
  have hk13 : k ≤ 13 := hk.trans hle
  have hmem : ∀ s ∈ S, s ∈ raw ∨ s = sO a b := by
    intro s hs
    have hp := live_proper hlive s hs
    have h := hsub s hs
    simp only [List.mem_append, List.mem_singleton] at h
    rcases h with (h | h) | h
    · exact Or.inl h
    · exact (hp.2.1 h).elim
    · exact Or.inr h
  have finish : ∀ {k' t' : Nat} {S' : Finset Sig}, Live k' t' S' → k' ≤ 14 →
      (∀ s ∈ S', s ∈ raw) → False := by
    intro k' t' S' hl hk' hs
    have heq := necessary hl hs
    subst S'
    have sz := live_size hl
    rw [List.toFinset_card_of_nodup raw_nd] at sz
    have hlenRaw : raw.length = 9 := rfl
    exact rootImpossible t' (by omega) k' hk' raw.toFinset rootTag rootWires_rep
      (restrict_live hl (rootTag_ok hk'))
  by_cases hab : a = b
  · subst hab
    refine finish hlive (by omega) ?_
    intro s hs
    rcases hmem s hs with h | h
    · exact h
    · rw [h, sO_eq, idem]
      exact R_mem a
  by_cases ho : sO a b ∈ S
  · have hS : insert (bin true (R a) (R b)) (S.erase (sO a b)) = S := by
      rw [← sO_eq]
      exact Finset.insert_erase ho
    have hfresh : bin true (R a) (R b) ∉ insert (R a) (insert (R b) (S.erase (sO a b))) := by
      intro hx
      rcases Finset.mem_insert.mp hx with hx | hx
      · exact (fresh a b hab).1 hx
      · rcases Finset.mem_insert.mp hx with hx | hx
        · exact (fresh a b hab).2 hx
        · exact (Finset.mem_erase.mp hx).1 (sO_eq a b).symm
    have hl2 : Live (k + 1) t (insert (R a) (insert (R b) (S.erase (sO a b)))) :=
      Live.binary (R_proper a) (R_proper b) (R_inj a b hab) hfresh (hS.symm ▸ hlive)
    refine finish hl2 (by omega) ?_
    intro s hs
    rcases Finset.mem_insert.mp hs with rfl | hs
    · exact R_mem a
    · rcases Finset.mem_insert.mp hs with rfl | hs
      · exact R_mem b
      · obtain ⟨hne, hsS⟩ := Finset.mem_erase.mp hs
        exact (hmem s hsS).resolve_right hne
  · refine finish hlive (by omega) ?_
    intro s hs
    rcases hmem s hs with h | rfl
    · exact h
    · exact (ho hs).elim

end Glue
end PEqualNP.Outside.L_meta_3116

open PEqualNP.Outside.L_meta_3116 in
theorem PEqualNP.Outside.L_meta_3116 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (13 : ℕ) → ∀ (x4 x5 : Fin (9 : ℕ)), ∃ (x6 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x6 ++ [Bool.false, x6 x4 || x6 x5]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  intro C hf hsize a b
  by_contra hne
  refine Glue.core a b C hf hsize (Glue.target_mem a b C hf (fun x => ?_))
  have h : C.eval (List.ofFn x ++ [false, x a || x b]) =
      (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
      x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 ||
      x 8 && x 5) := Classical.not_not.mp (fun hh => hne ⟨x, hh⟩)
  have h1 : ∀ c : Fin 9, (List.ofFn x ++ [false]).getD c.val false = x c := by
    intro c
    fin_cases c <;> rfl
  have hv : PEqualNP.CircuitLowerBounds.GateOp.or.eval [(List.ofFn x ++ [false]).getD a.val false,
      (List.ofFn x ++ [false]).getD b.val false] = (x a || x b) := by
    rw [h1 a, h1 b]
    cases x a <;> cases x b <;> rfl
  rw [hv, List.append_assoc]
  exact h
