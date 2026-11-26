import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19721_aux

-- The circuit; the kernel replays it on the inputs the statement asks about.
def wit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [19, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [21, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 25]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [25, 26]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [30, 27]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 26]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [35, 27]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [16, 28]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [17, 29]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [37, 38]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [18, 31]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [39, 40]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [20, 32]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [41, 42]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [22, 33]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [43, 44]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [23, 34]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [45, 46]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [24, 36]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [47, 48]⟩], 49⟩

end PEqualNP.Outside.L_meta_19721_aux

theorem PEqualNP.Outside.L_meta_19721 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (4319635817910669180 : ℕ).testBit (8 * u.val + v.val)) 34 := by
  refine ⟨PEqualNP.Outside.L_meta_19721_aux.wit, ?_, ?_, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_19721_aux.wit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel
