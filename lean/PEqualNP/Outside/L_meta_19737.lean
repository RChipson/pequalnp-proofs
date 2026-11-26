import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19737_aux

-- The circuit; the kernel replays it on the inputs the statement asks about.
def wit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [22, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [23, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 21]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [26, 17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 18]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [19, 20]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [17, 20]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [18, 19]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 21]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 24]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 25]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [33, 34]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 27]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [35, 36]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 28]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [37, 38]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 29]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [39, 40]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 30]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [41, 42]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 31]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [43, 44]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 32]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [45, 46]⟩], 47⟩

end PEqualNP.Outside.L_meta_19737_aux

theorem PEqualNP.Outside.L_meta_19737 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (5662696764710545965 : ℕ).testBit (8 * u.val + v.val)) 33 := by
  refine ⟨PEqualNP.Outside.L_meta_19737_aux.wit, ?_, ?_, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_19737_aux.wit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel
