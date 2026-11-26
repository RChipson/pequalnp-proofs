import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20680_aux

-- The circuit; the kernel replays it on the inputs the statement asks about.
def wit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [15, 16]⟩], 17⟩

end PEqualNP.Outside.L_meta_20680_aux

theorem PEqualNP.Outside.L_meta_20680 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (11766784 : ℕ).testBit (5 * u.val + v.val)) 8 := by
  refine ⟨PEqualNP.Outside.L_meta_20680_aux.wit, ?_, ?_, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_20680_aux.wit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel
