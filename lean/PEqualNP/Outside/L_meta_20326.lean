import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20326_aux

-- The circuit; the kernel replays it on the inputs the statement asks about.
def wit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [20, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [22, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [24, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [26, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [30, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [32, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [34, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [17, 27]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [18, 28]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [36, 37]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [19, 29]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [38, 39]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [21, 31]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [40, 41]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [23, 33]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [42, 43]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [25, 35]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [44, 45]⟩], 46⟩

end PEqualNP.Outside.L_meta_20326_aux

theorem PEqualNP.Outside.L_meta_20326 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (11447215094344424295 : ℕ).testBit (8 * u.val + v.val)) 31 := by
  refine ⟨PEqualNP.Outside.L_meta_20326_aux.wit, ?_, ?_, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_20326_aux.wit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel
