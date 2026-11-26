import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20163_aux

-- The circuit; the kernel replays it on the inputs the statement asks about.
def wit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 18]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 20]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 20]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 19]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [25, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 19]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 21]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [17, 18]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 21]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 22]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 23]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [31, 32]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 24]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [33, 34]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 26]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [35, 36]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 27]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [37, 38]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 28]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [39, 40]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 29]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [41, 42]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 30]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [43, 44]⟩], 45⟩

end PEqualNP.Outside.L_meta_20163_aux

theorem PEqualNP.Outside.L_meta_20163 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (8164297279589376675 : ℕ).testBit (8 * u.val + v.val)) 30 := by
  refine ⟨PEqualNP.Outside.L_meta_20163_aux.wit, ?_, ?_, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_20163_aux.wit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel
