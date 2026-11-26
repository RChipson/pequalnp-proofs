import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20645_aux

-- The circuit; the kernel replays it on the inputs the statement asks about.
def wit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [11, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 14]⟩], 15⟩

end PEqualNP.Outside.L_meta_20645_aux

theorem PEqualNP.Outside.L_meta_20645 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (7570432 : ℕ).testBit (5 * u.val + v.val)) 6 := by
  refine ⟨PEqualNP.Outside.L_meta_20645_aux.wit, ?_, ?_, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_20645_aux.wit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel
