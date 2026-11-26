import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19714_aux

-- The circuit; the kernel replays it on the inputs the statement asks about.
def wit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 18]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [19, 21]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [20, 23]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [20, 25]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 28]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [19, 29]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 31]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [18, 32]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 35]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [22, 24]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [26, 27]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [37, 38]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [30, 33]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [39, 40]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [34, 36]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [41, 42]⟩], 43⟩

end PEqualNP.Outside.L_meta_19714_aux

theorem PEqualNP.Outside.L_meta_19714 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (17464622044026729945 : ℕ).testBit (8 * u.val + v.val)) 35 := by
  refine ⟨PEqualNP.Outside.L_meta_19714_aux.wit, ?_, ?_, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_19714_aux.wit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel
