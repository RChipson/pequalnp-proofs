import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20684_aux

-- The circuit; the kernel replays it on the inputs the statement asks about.
def wit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [13, 16]⟩], 17⟩

end PEqualNP.Outside.L_meta_20684_aux

theorem PEqualNP.Outside.L_meta_20684 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (13730816 : ℕ).testBit (5 * u.val + v.val)) 8 := by
  refine ⟨PEqualNP.Outside.L_meta_20684_aux.wit, ?_, ?_, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_20684_aux.wit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel
