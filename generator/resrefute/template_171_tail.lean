set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem hc : chkR (axPHP 5 4) cert = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem hm : (∅ : Clause (Fin 5 × Fin 4)) ∈ cert.map Prod.fst := by decide +kernel

set_option maxRecDepth 100000 in
theorem hl : (cert.map Prod.fst).length ≤ 159 := by decide +kernel

end PEqualNP.Outside.L_pcx_171_aux

theorem PEqualNP.Outside.L_pcx_171 : ∃ π : List (PEqualNP.ProofComplexity.Clause (Fin 5 × Fin 4)), PEqualNP.ProofComplexity.IsRefutation (PEqualNP.ProofComplexity.PHP 5 4) π ∧ π.length ≤ 159 := by
  exact ⟨PEqualNP.Outside.L_pcx_171_aux.cert.map Prod.fst, ⟨PEqualNP.Outside.L_pcx_171_aux.chkR_sound _ (PEqualNP.Outside.L_pcx_171_aux.axPHP 5 4) (PEqualNP.Outside.L_pcx_171_aux.axPHP_sound 5 4) _ PEqualNP.Outside.L_pcx_171_aux.hc, PEqualNP.Outside.L_pcx_171_aux.hm⟩, PEqualNP.Outside.L_pcx_171_aux.hl⟩
