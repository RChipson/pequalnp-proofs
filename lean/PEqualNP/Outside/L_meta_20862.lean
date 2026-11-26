import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20862_aux

-- The circuit; the kernel replays it on the inputs the statement asks about.
def wit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [10, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [17, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [18, 16]⟩], 19⟩

end PEqualNP.Outside.L_meta_20862_aux

theorem PEqualNP.Outside.L_meta_20862 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (29755425 : ℕ).testBit (5 * u.val + v.val)) 10 := by
  refine ⟨PEqualNP.Outside.L_meta_20862_aux.wit, ?_, ?_, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_20862_aux.wit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel
