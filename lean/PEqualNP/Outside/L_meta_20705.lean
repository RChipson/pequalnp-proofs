import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20705_aux

-- The circuit; the kernel replays it on the inputs the statement asks about.
def wit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [14, 16]⟩], 17⟩

end PEqualNP.Outside.L_meta_20705_aux

theorem PEqualNP.Outside.L_meta_20705 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (30475264 : ℕ).testBit (5 * u.val + v.val)) 8 := by
  refine ⟨PEqualNP.Outside.L_meta_20705_aux.wit, ?_, ?_, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_20705_aux.wit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel
