import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22178_aux

def wit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [8, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [14, 16]⟩], 17⟩

end PEqualNP.Outside.L_meta_22178_aux

theorem PEqualNP.Outside.L_meta_22178 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (16947 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_22178_aux.wit, ?_, ?_, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_22178_aux.wit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel
