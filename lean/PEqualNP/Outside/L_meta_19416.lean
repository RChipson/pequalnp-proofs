import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19416_aux

-- The circuit of the sketch: OR 0 1, OR 10 5, OR 11 6, OR 2 3, AND 13 7, OR 12 14, output wire 15.
-- The kernel replays it on each of the 25 promise inputs.
def wit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [13, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 14]⟩], 15⟩

end PEqualNP.Outside.L_meta_19416_aux

theorem PEqualNP.Outside.L_meta_19416 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => decide ((v : ℕ) < ![5, 5, 3, 3, 2] u)) 6 := by
  refine ⟨PEqualNP.Outside.L_meta_19416_aux.wit, ?_, ?_, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_19416_aux.wit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel
