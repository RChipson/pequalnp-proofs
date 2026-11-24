import Cert

-- GLUE-BEGIN
-- New for this step: the two given wires are put back as the first two gates of a
-- circuit on the nine inputs. The second wire repeats an input, repeats the negated
-- input 0, or is constant, so a derivation reads only inputs and the negation of
-- input 0. If it reads that negation and input 0, pinning input 0 to false loses two
-- gates, against the checked bound for the graph without vertex 0. If it reads the
-- negation and not input 0, one more gate rebuilds the negation from input 0. Either
-- way the checked frontier certificate for fourteen gates excludes it.
namespace PEqualNP.Outside.L_meta_3116
namespace Glue
open PEqualNP.CircuitLowerBounds Main1672

def gN : Gate := ⟨.not, [0]⟩
def gC (a b : Nat) : Gate := ⟨.or, [a, b]⟩
def sN : Sig := neg raw0
def sC (a b : Nat) : Sig := gv (raw ++ [sN]) (gC a b)
def okPair (a b : Fin 11) : Prop := a = b ∨ b = 10 ∨ a = 0 ∧ b = 9

instance (a b : Fin 11) : Decidable (okPair a b) := by unfold okPair; infer_instance

lemma gvN : gv raw gN = sN := by decide +kernel
lemma raw0_ne_sN : raw0 ≠ sN := by decide +kernel
lemma raw0_proper : proper raw0 :=
  ⟨raw_valid raw0 (by simp [raw]), by decide +kernel, by decide +kernel⟩
lemma sC_kind : ∀ a b : Fin 11, okPair a b →
    sC a b = zero ∨ sC a b = one ∨ sC a b ∈ raw ∨ sC a b = sN := by
  decide +kernel

lemma valid_raw0 : Valid raw0 := raw_valid raw0 (by simp [raw])
lemma valid_sN : Valid sN := valid_neg valid_raw0

def extend (a b : Nat) (C : Circuit) : Circuit := ⟨gN :: gC a b :: C.gates, C.output⟩

lemma extend_fan (a b : Nat) (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C) :
    PEqualNP.MetaComplexity.FanInTwo (extend a b C) := by
  intro g hg
  simp only [extend, List.mem_cons] at hg
  rcases hg with rfl | rfl | hg
  · exact ⟨by simp [gN], by simp [gN]⟩
  · exact ⟨by simp [gC], by simp [gC]⟩
  · exact h g hg

lemma extend_eval (a b : Nat) (C : Circuit) (x : Fin 9 → Bool) :
    (extend a b C).eval (List.ofFn x) =
      C.eval (List.ofFn x ++ [!x 0] ++
        [(gC a b).op.eval ((gC a b).inputs.map fun i => (List.ofFn x ++ [!x 0]).getD i false)]) := by
  have h1 : gN.op.eval (gN.inputs.map fun i => (List.ofFn x).getD i false) = !x 0 := by
    simp [gN, GateOp.eval, List.getD_eq_getElem?_getD]
  change ((C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    ((List.ofFn x ++ [gN.op.eval (gN.inputs.map fun i => (List.ofFn x).getD i false)]) ++
      [(gC a b).op.eval ((gC a b).inputs.map fun i =>
        (List.ofFn x ++ [gN.op.eval (gN.inputs.map fun i => (List.ofFn x).getD i false)]).getD
          i false)])).getD C.output false) = _
  rw [h1]
  rfl

def wiresW (a b : Nat) : List Sig := raw ++ [sN] ++ [sC a b]

lemma target_mem (a b : Nat) (C : Circuit) (hf : PEqualNP.MetaComplexity.FanInTwo C)
    (he : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [!x 0] ++
        [(gC a b).op.eval ((gC a b).inputs.map fun i => (List.ofFn x ++ [!x 0]).getD i false)])
      = edgeF x) :
    target ∈ execute C.gates (wiresW a b) := by
  have h := circuit_target (extend a b C) (extend_fan a b C hf)
    (fun x => (extend_eval a b C x).trans (he x))
  change target ∈ execute C.gates ((raw ++ [gv raw gN]) ++ [gv (raw ++ [gv raw gN]) (gC a b)]) at h
  rw [gvN] at h
  exact h

lemma proj_raw0 : (homProject 0).fn raw0 = zero := project_raw_zero 0
lemma proj_sN : (homProject 0).fn sN = one := by
  change (homProject 0).fn (neg raw0) = one
  rw [(homProject 0).hneg valid_raw0, proj_raw0]
  exact neg_laws.1

lemma core (a b : Fin 11) (ha : okPair a b) (C : Circuit)
    (hf : PEqualNP.MetaComplexity.FanInTwo C) (hle : C.gates.length ≤ 13)
    (htgt : target ∈ execute C.gates (wiresW a b)) : False := by
  have hvW : ∀ s ∈ wiresW a b, Valid s := by
    intro s hs
    simp only [wiresW, List.mem_append, List.mem_singleton] at hs
    rcases hs with (hs | rfl) | rfl
    · exact raw_valid s hs
    · exact valid_sN
    · exact gv_valid (fun s hs => by
        rcases List.mem_append.mp hs with hs | hs
        · exact raw_valid s hs
        · simp only [List.mem_singleton] at hs; subst s; exact valid_sN) (gC a b)
  obtain ⟨k, t, S, hk, hlive, hsub⟩ :=
    extract C.gates (wiresW a b) hvW (fun g hg => hf g hg) htgt
  have hk13 : k ≤ 13 := hk.trans hle
  have hmem : ∀ s ∈ S, s ∈ raw ∨ s = sN := by
    intro s hs
    have hp := live_proper hlive s hs
    have h := hsub s hs
    simp only [wiresW, List.mem_append, List.mem_singleton] at h
    rcases h with (h | h) | h
    · exact Or.inl h
    · exact Or.inr h
    · rcases sC_kind a b ha with h0 | h1 | hr | hn
      · exact (hp.2.1 (h.trans h0)).elim
      · exact (hp.2.2 (h.trans h1)).elim
      · exact Or.inl (h ▸ hr)
      · exact Or.inr (h.trans hn)
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
  by_cases hn : sN ∈ S
  · by_cases h0 : raw0 ∈ S
    · obtain ⟨q, hq, m, hm, t2, T, hl, hs⟩ := feasible_two_consts hlive (homProject 0) raw0 sN h0 hn
        raw0_ne_sN (fun hp => hp.2.1 proj_raw0) (fun hp => hp.2.2 proj_sN)
      refine root_project_deg3 0 (by decide) ⟨m, by omega, t2, T, hl, ?_⟩
      intro x hx
      obtain ⟨s, hsS, rfl⟩ := Finset.mem_image.mp (hs hx)
      have hp := live_proper hl _ hx
      rcases hmem s hsS with h | rfl
      · exact Finset.mem_image_of_mem _ (List.mem_toFinset.mpr h)
      · exact (hp.2.2 proj_sN).elim
    · have hS : insert (neg raw0) (S.erase sN) = S := Finset.insert_erase hn
      have hfresh : neg raw0 ∉ insert raw0 (S.erase sN) := by
        intro hx
        rcases Finset.mem_insert.mp hx with hx | hx
        · exact raw0_ne_sN hx.symm
        · exact (Finset.mem_erase.mp hx).1 rfl
      have hl2 : Live (k + 1) (t + 1) (insert raw0 (S.erase sN)) :=
        Live.unary raw0_proper hfresh (hS.symm ▸ hlive)
      refine finish hl2 (by omega) ?_
      intro s hs
      rcases Finset.mem_insert.mp hs with rfl | hs
      · simp [raw]
      · obtain ⟨hne, hsS⟩ := Finset.mem_erase.mp hs
        exact (hmem s hsS).resolve_right hne
  · refine finish hlive (by omega) ?_
    intro s hs
    rcases hmem s hs with h | rfl
    · exact h
    · exact (hn hs).elim

lemma bits (x : Fin 9 → Bool) :
    (fun i : Fin 9 => (BitVec.ofNat 9 (Nat.ofBits x)).getLsbD ↑i) = x := by
  funext i
  rw [BitVec.getLsbD_ofNat, Nat.testBit_ofBits_lt _ _ i.2]
  simp

lemma anyEq : (fun x9 : Fin 9 → Bool =>
    [((0 : Fin 9), (1 : Fin 9)), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8),
      (5, 7), (6, 8), (8, 5)].any fun e => x9 e.1 && x9 e.2) = edgeF := by
  decide +kernel

end Glue
end PEqualNP.Outside.L_meta_3116

open PEqualNP.Outside.L_meta_3116 in
theorem PEqualNP.Outside.L_meta_3116 : ∀ (x1 x2 : Fin (11 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit),   x1 = x2 ∨ x2 = (10 : Fin (11 : ℕ)) ∨ x1 = (0 : Fin (11 : ℕ)) ∧ x2 = (9 : Fin (11 : ℕ)) →     x1 ≤ x2 →       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           ∃ (x8 : BitVec (9 : ℕ)),             have x9 : Fin (9 : ℕ) → Bool := fun (x9 : Fin (9 : ℕ)) => x8.getLsbD ↑x9;             have x10 : List Bool := List.ofFn x9 ++ [!x9 (0 : Fin (9 : ℕ))];             x3.eval (x10 ++ [x10.getD (↑x1) Bool.false || x10.getD (↑x2) Bool.false]) ≠ [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x11 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x9 x11.1 && x9 x11.2 := by
  intro a b C hab _ hf hsize
  by_contra hne
  push Not at hne
  refine Glue.core a b hab C hf hsize (Glue.target_mem a b C hf (fun x => ?_))
  have h : ∀ g : Fin 9 → Bool,
      g = (fun i : Fin 9 => (BitVec.ofNat 9 (Nat.ofBits x)).getLsbD ↑i) →
      C.eval ((List.ofFn g ++ [!g 0]) ++ [(List.ofFn g ++ [!g 0]).getD (↑a) false ||
        (List.ofFn g ++ [!g 0]).getD (↑b) false]) =
      [((0 : Fin 9), (1 : Fin 9)), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8),
        (5, 7), (6, 8), (8, 5)].any fun e => g e.1 && g e.2 := by
    intro g hg
    subst hg
    exact Classical.not_not.mp (hne _)
  have h2 := h x (Glue.bits x).symm
  rw [← Glue.anyEq]
  simpa [Glue.gC, PEqualNP.CircuitLowerBounds.GateOp.eval] using h2
