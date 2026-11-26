import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23009_aux

def wit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 11]⟩], 12⟩

end PEqualNP.Outside.L_meta_23009_aux

theorem PEqualNP.Outside.L_meta_23009 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (99870 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_23009_aux.wit, ?_, ?_, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_23009_aux.wit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel
