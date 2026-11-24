import Cert

-- GLUE-BEGIN
-- New for this step: the stated input change leaves every input as it was, so this is
-- a restatement. A circuit on the nine inputs gives a
-- derivation that reads only inputs, which the checked frontier certificate for fourteen
-- gates excludes.
namespace PEqualNP.Outside.L_meta_3116
namespace Glue
open PEqualNP.CircuitLowerBounds Main1672

lemma core (C : Circuit) (hf : PEqualNP.MetaComplexity.FanInTwo C) (hle : C.gates.length ≤ 14)
    (he : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = edgeF x) : False := by
  have htgt : target ∈ execute C.gates raw := circuit_target C hf he
  obtain ⟨k, t, S, hk, hlive, hsub⟩ :=
    extract C.gates raw raw_valid (fun g hg => hf g hg) htgt
  have heq := necessary hlive hsub
  subst S
  have sz := live_size hlive
  rw [List.toFinset_card_of_nodup raw_nd] at sz
  have hlenRaw : raw.length = 9 := rfl
  exact rootImpossible t (by omega) k (hk.trans hle) raw.toFinset rootTag rootWires_rep
    (restrict_live hlive (rootTag_ok (hk.trans hle)))

end Glue
end PEqualNP.Outside.L_meta_3116

theorem PEqualNP.Outside.L_meta_3116 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (14 : ℕ) → (List.filter (fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => x4.inputs.contains (0 : ℕ)) x1.gates).length = (1 : ℕ) → (¬∃ x5 ∈ x1.gates, (0 : ℕ) ∈ x5.inputs ∧ x5.op = PEqualNP.CircuitLowerBounds.GateOp.not) → ∃ (x6 : Fin (9 : ℕ) → Bool), (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 fun (x7 : Fin (9 : ℕ)) => if x7 = (0 : Fin (9 : ℕ)) then Bool.false != x6 (0 : Fin (9 : ℕ)) else x6 x7) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  intro C hf hs _ _
  by_contra hne
  refine PEqualNP.Outside.L_meta_3116.Glue.core C hf hs (fun x => ?_)
  have h : PEqualNP.MetaComplexity.circuitFun 9 C
      (fun i : Fin 9 => if i = 0 then (false != x 0) else x i) =
      (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
      x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 ||
      x 8 && x 5) := Classical.not_not.mp (fun hh => hne ⟨x, hh⟩)
  have hx : (fun i : Fin 9 => if i = 0 then (false != x 0) else x i) = x := by
    funext i
    split_ifs with hi
    · subst hi
      cases x 0 <;> rfl
    · rfl
  rw [hx] at h
  exact h
