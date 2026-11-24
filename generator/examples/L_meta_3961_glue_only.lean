import Cert

-- GLUE-BEGIN
-- New for this step: nothing but the restatement. A circuit on the nine inputs gives a
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

lemma anyEq : (fun x9 : Fin 9 → Bool =>
    [((0 : Fin 9), (1 : Fin 9)), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8),
      (5, 7), (6, 8), (8, 5)].any fun e => x9 e.1 && x9 e.2) = edgeF := by
  decide +kernel

end Glue
end PEqualNP.Outside.L_meta_3116

theorem PEqualNP.Outside.L_meta_3116 : ¬PEqualNP.MetaComplexity.HasCircuitSize (9 : ℕ) (fun (x1 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x2 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x1 x2.1 && x1 x2.2) (14 : ℕ) := by
  rintro ⟨C, hf, hs, he⟩
  refine PEqualNP.Outside.L_meta_3116.Glue.core C hf hs (fun x => ?_)
  exact (he x).trans (congrFun PEqualNP.Outside.L_meta_3116.Glue.anyEq x)
