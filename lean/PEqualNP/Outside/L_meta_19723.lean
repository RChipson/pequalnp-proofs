import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19723_aux

-- The circuit; the kernel replays it on the inputs the statement asks about.
def wit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [19, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 18]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [26, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 18]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 20]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 21]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [29, 30]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 22]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [31, 32]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 23]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [33, 34]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 24]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [35, 36]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 25]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [37, 38]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 27]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [39, 40]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 28]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [41, 42]⟩], 43⟩

end PEqualNP.Outside.L_meta_19723_aux

theorem PEqualNP.Outside.L_meta_19723 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (6992850275190006930 : ℕ).testBit (8 * u.val + v.val)) 28 := by
  refine ⟨PEqualNP.Outside.L_meta_19723_aux.wit, ?_, ?_, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_19723_aux.wit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel
