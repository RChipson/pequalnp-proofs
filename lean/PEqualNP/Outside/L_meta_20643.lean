import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20643_aux

-- The circuit; the kernel replays it on the inputs the statement asks about.
def wit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [13, 14]⟩], 15⟩

end PEqualNP.Outside.L_meta_20643_aux

theorem PEqualNP.Outside.L_meta_20643 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (7373824 : ℕ).testBit (5 * u.val + v.val)) 6 := by
  refine ⟨PEqualNP.Outside.L_meta_20643_aux.wit, ?_, ?_, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_20643_aux.wit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel
