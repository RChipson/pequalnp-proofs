import Cert

-- GLUE-BEGIN
-- New for this step: fewer than fifteen gates is at most fourteen, and the other
-- conditions are not needed. A circuit on the nine inputs gives a
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

theorem PEqualNP.Outside.L_meta_3116 : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → (∀ x4 ∈ x2.gates, x4.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) → (∀ (x5 : Fin (9 : ℕ) → Bool), (x2.wires (List.ofFn x5)).getD (9 : ℕ) Bool.false = (x5 (0 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)))) → x2.size < (15 : ℕ) → (∀ (x7 : Fin (3 : ℕ)), List.countP (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => x8.inputs.contains (![(4 : ℕ), (6 : ℕ), (7 : ℕ)] x7)) x2.gates ≤ (2 : ℕ)) → PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x2 ≠ x1 := by
  intro f C hf _ _ hs _ he
  have target_eq : f = PEqualNP.Outside.L_meta_3116.Main1672.edgeF := by decide +kernel
  have hs' : C.gates.length ≤ 14 := by
    have : C.gates.length < 15 := hs
    omega
  exact PEqualNP.Outside.L_meta_3116.Glue.core C hf hs'
    (fun x => (congrFun he x).trans (congrFun target_eq x))
