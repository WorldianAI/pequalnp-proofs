import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23684

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def wit : Circuit :=
  ⟨[⟨GateOp.or, [2, 7]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.or, [3, 9]⟩, ⟨GateOp.or, [1, 6]⟩, ⟨GateOp.or, [0, 11]⟩, ⟨GateOp.or, [8, 10]⟩, ⟨GateOp.or, [12, 15]⟩, ⟨GateOp.and, [13, 15]⟩, ⟨GateOp.and, [14, 16]⟩, ⟨GateOp.or, [17, 18]⟩], 19⟩

theorem wit_mono : Monotone2 wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem main_aux : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (816696 : ℕ).testBit (6 * u.val + v.val)) 10 := by
  refine ⟨wit, wit_mono, by decide, ?_⟩
  decide

end PEqualNP.Outside.L_meta_23684

theorem PEqualNP.Outside.L_meta_23684 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (816696 : ℕ).testBit (6 * u.val + v.val)) 10 :=
  PEqualNP.Outside.L_meta_23684.main_aux
