import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20294_aux

-- The circuit; the kernel replays it on the inputs the statement asks about.
def wit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [17, 21]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [18, 20]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 20]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [17, 25]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 27]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [19, 28]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [18, 31]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [22, 23]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [24, 26]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [33, 34]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [29, 30]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [35, 36]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [19, 32]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [37, 38]⟩], 39⟩

end PEqualNP.Outside.L_meta_20294_aux

theorem PEqualNP.Outside.L_meta_20294 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (9972273704342751540 : ℕ).testBit (8 * u.val + v.val)) 24 := by
  refine ⟨PEqualNP.Outside.L_meta_20294_aux.wit, ?_, ?_, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_20294_aux.wit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel
