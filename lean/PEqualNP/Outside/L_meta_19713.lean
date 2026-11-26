import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19713_aux

-- The circuit; the kernel replays it on the inputs the statement asks about.
def wit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [19, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [21, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [23, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [24, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 25]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 26]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [33, 34]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [16, 27]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [35, 36]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 28]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [37, 38]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [17, 29]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [39, 40]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [18, 30]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [41, 42]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [20, 31]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [43, 44]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [22, 32]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [45, 46]⟩], 47⟩

end PEqualNP.Outside.L_meta_19713_aux

theorem PEqualNP.Outside.L_meta_19713 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (5420442459739364580 : ℕ).testBit (8 * u.val + v.val)) 32 := by
  refine ⟨PEqualNP.Outside.L_meta_19713_aux.wit, ?_, ?_, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_19713_aux.wit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel
