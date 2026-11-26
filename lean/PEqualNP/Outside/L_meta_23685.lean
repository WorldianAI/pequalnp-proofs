import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23685

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def wit : Circuit :=
  ⟨[⟨GateOp.or, [1, 6]⟩, ⟨GateOp.or, [2, 7]⟩, ⟨GateOp.or, [8, 11]⟩, ⟨GateOp.and, [10, 12]⟩, ⟨GateOp.or, [4, 13]⟩, ⟨GateOp.or, [3, 11]⟩, ⟨GateOp.or, [9, 15]⟩, ⟨GateOp.or, [0, 5]⟩, ⟨GateOp.and, [16, 17]⟩, ⟨GateOp.or, [14, 18]⟩], 19⟩

theorem wit_mono : Monotone2 wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem main_aux : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (816745 : ℕ).testBit (6 * u.val + v.val)) 10 := by
  refine ⟨wit, wit_mono, by decide, ?_⟩
  decide

end PEqualNP.Outside.L_meta_23685

theorem PEqualNP.Outside.L_meta_23685 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (816745 : ℕ).testBit (6 * u.val + v.val)) 10 :=
  PEqualNP.Outside.L_meta_23685.main_aux
