import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20646_aux

-- The circuit; the kernel replays it on the inputs the statement asks about.
def wit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [12, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 14]⟩], 15⟩

end PEqualNP.Outside.L_meta_20646_aux

theorem PEqualNP.Outside.L_meta_20646 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (7572480 : ℕ).testBit (5 * u.val + v.val)) 6 := by
  refine ⟨PEqualNP.Outside.L_meta_20646_aux.wit, ?_, ?_, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_20646_aux.wit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel
