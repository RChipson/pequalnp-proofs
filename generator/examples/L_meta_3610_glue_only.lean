import Cert

-- GLUE-BEGIN
-- New for this step: the given wire is put back as the first gate of a circuit on the
-- nine inputs. A derivation that reads the wire is extended by one gate that rebuilds it
-- from inputs 0 and 6, so in both cases the checked frontier certificate for fourteen
-- gates excludes it.
namespace PEqualNP.Outside.L_meta_3116
namespace Glue
open PEqualNP.CircuitLowerBounds Main1672

def gO : Gate := ⟨.or, [0, 6]⟩
def sO : Sig := bin true raw0 raw6

lemma gvO : gv raw gO = sO := by decide +kernel
lemma raw0_ne_sO : raw0 ≠ sO := by decide +kernel
lemma raw6_ne_sO : raw6 ≠ sO := by decide +kernel
lemma raw0_ne_raw6 : raw0 ≠ raw6 := by decide +kernel
lemma valid_raw0 : Valid raw0 := raw_valid raw0 (by simp [raw])
lemma valid_raw6 : Valid raw6 := raw_valid raw6 (by simp [raw])
lemma raw0_proper : proper raw0 := ⟨valid_raw0, by decide +kernel, by decide +kernel⟩
lemma raw6_proper : proper raw6 := ⟨valid_raw6, by decide +kernel, by decide +kernel⟩
lemma valid_sO : Valid sO := valid_bin valid_raw0 valid_raw6

def extend (C : Circuit) : Circuit := ⟨gO :: C.gates, C.output⟩

lemma extend_fan (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C) :
    PEqualNP.MetaComplexity.FanInTwo (extend C) := by
  intro g hg
  simp only [extend, List.mem_cons] at hg
  rcases hg with rfl | hg
  · exact ⟨by simp [gO], by simp [gO]⟩
  · exact h g hg

lemma extend_eval (C : Circuit) (x : Fin 9 → Bool) :
    (extend C).eval (List.ofFn x) = C.eval (List.ofFn x ++ [x 0 || x 6]) := by
  have h1 : gO.op.eval (gO.inputs.map fun i => (List.ofFn x).getD i false) = (x 0 || x 6) := by
    simp [gO, GateOp.eval, List.getD_eq_getElem?_getD]
  change ((C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    (List.ofFn x ++ [gO.op.eval (gO.inputs.map fun i => (List.ofFn x).getD i false)])).getD
      C.output false) = _
  rw [h1]
  rfl

lemma target_mem (C : Circuit) (hf : PEqualNP.MetaComplexity.FanInTwo C)
    (he : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 || x 6]) = edgeF x) :
    target ∈ execute C.gates (raw ++ [sO]) := by
  have h := circuit_target (extend C) (extend_fan C hf)
    (fun x => (extend_eval C x).trans (he x))
  change target ∈ execute C.gates (raw ++ [gv raw gO]) at h
  rw [gvO] at h
  exact h

lemma core (C : Circuit) (hf : PEqualNP.MetaComplexity.FanInTwo C) (hle : C.gates.length ≤ 13)
    (htgt : target ∈ execute C.gates (raw ++ [sO])) : False := by
  have hvW : ∀ s ∈ raw ++ [sO], Valid s := by
    intro s hs
    rcases List.mem_append.mp hs with hs | hs
    · exact raw_valid s hs
    · simp only [List.mem_singleton] at hs
      subst s
      exact valid_sO
  obtain ⟨k, t, S, hk, hlive, hsub⟩ :=
    extract C.gates (raw ++ [sO]) hvW (fun g hg => hf g hg) htgt
  have hk13 : k ≤ 13 := hk.trans hle
  have hmem : ∀ s ∈ S, s ∈ raw ∨ s = sO := by
    intro s hs
    rcases List.mem_append.mp (hsub s hs) with h | h
    · exact Or.inl h
    · exact Or.inr (by simpa using h)
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
  by_cases ho : sO ∈ S
  · have hS : insert (bin true raw0 raw6) (S.erase sO) = S := Finset.insert_erase ho
    have hfresh : bin true raw0 raw6 ∉ insert raw0 (insert raw6 (S.erase sO)) := by
      intro hx
      rcases Finset.mem_insert.mp hx with hx | hx
      · exact raw0_ne_sO hx.symm
      · rcases Finset.mem_insert.mp hx with hx | hx
        · exact raw6_ne_sO hx.symm
        · exact (Finset.mem_erase.mp hx).1 rfl
    have hl2 : Live (k + 1) t (insert raw0 (insert raw6 (S.erase sO))) :=
      Live.binary raw0_proper raw6_proper raw0_ne_raw6 hfresh (hS.symm ▸ hlive)
    refine finish hl2 (by omega) ?_
    intro s hs
    rcases Finset.mem_insert.mp hs with rfl | hs
    · simp [raw]
    · rcases Finset.mem_insert.mp hs with rfl | hs
      · simp [raw]
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
theorem PEqualNP.Outside.L_meta_3116 : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); have x2 : (Fin (9 : ℕ) → Bool) → List Bool := fun (x2 : Fin (9 : ℕ) → Bool) => List.ofFn x2 ++ [x2 (0 : Fin (9 : ℕ)) || x2 (6 : Fin (9 : ℕ))]; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x3 → x3.size ≤ (13 : ℕ) → ∃ (x6 : Fin (9 : ℕ) → Bool), x3.eval (x2 x6) ≠ x1 x6 := by
  intro f w C hf hs
  by_contra hne
  push Not at hne
  have target_eq : f = Main1672.edgeF := by decide +kernel
  exact Glue.core C hf hs (Glue.target_mem C hf (fun x => (hne x).trans (congrFun target_eq x)))
