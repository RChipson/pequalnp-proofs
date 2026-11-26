import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20372_aux

-- The circuit; the kernel replays it on the inputs the statement asks about.
def wit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [17, 20]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 18]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 24]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [19, 25]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [18, 27]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 19]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 32]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 33]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [21, 22]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [23, 26]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [35, 36]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [28, 29]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [37, 38]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [30, 31]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [39, 40]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [15, 34]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [41, 42]⟩], 43⟩

end PEqualNP.Outside.L_meta_20372_aux

theorem PEqualNP.Outside.L_meta_20372 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (11914988824647881820 : ℕ).testBit (8 * u.val + v.val)) 28 := by
  refine ⟨PEqualNP.Outside.L_meta_20372_aux.wit, ?_, ?_, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_20372_aux.wit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel
