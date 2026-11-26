import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23049

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def wit : Circuit :=
  ⟨[⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [3, 7]⟩, ⟨GateOp.or, [1, 4]⟩, ⟨GateOp.or, [6, 10]⟩, ⟨GateOp.or, [1, 9]⟩, ⟨GateOp.or, [5, 12]⟩, ⟨GateOp.or, [2, 15]⟩, ⟨GateOp.or, [5, 14]⟩, ⟨GateOp.or, [2, 7]⟩, ⟨GateOp.or, [8, 11]⟩, ⟨GateOp.or, [13, 16]⟩, ⟨GateOp.and, [19, 20]⟩, ⟨GateOp.and, [15, 18]⟩, ⟨GateOp.and, [13, 17]⟩, ⟨GateOp.or, [21, 22]⟩, ⟨GateOp.or, [23, 24]⟩], 25⟩

theorem wit_mono : Monotone2 wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem main_aux : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1947514 : ℕ).testBit (6 * u.val + v.val)) 16 := by
  refine ⟨wit, wit_mono, by decide, ?_⟩
  decide

end PEqualNP.Outside.L_meta_23049

theorem PEqualNP.Outside.L_meta_23049 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1947514 : ℕ).testBit (6 * u.val + v.val)) 16 :=
  PEqualNP.Outside.L_meta_23049.main_aux
