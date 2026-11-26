import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21917_aux

def wit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [8, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 11]⟩], 12⟩

end PEqualNP.Outside.L_meta_21917_aux

theorem PEqualNP.Outside.L_meta_21917 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (34088 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_21917_aux.wit, ?_, ?_, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_21917_aux.wit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel
