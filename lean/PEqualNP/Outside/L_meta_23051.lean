import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23051

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def wit : Circuit :=
  ⟨[⟨GateOp.or, [1, 5]⟩, ⟨GateOp.or, [4, 10]⟩, ⟨GateOp.or, [2, 6]⟩, ⟨GateOp.or, [10, 12]⟩, ⟨GateOp.or, [3, 8]⟩, ⟨GateOp.or, [4, 7]⟩, ⟨GateOp.and, [13, 14]⟩, ⟨GateOp.or, [9, 13]⟩, ⟨GateOp.or, [8, 17]⟩, ⟨GateOp.or, [3, 12]⟩, ⟨GateOp.or, [0, 15]⟩, ⟨GateOp.or, [11, 16]⟩, ⟨GateOp.and, [18, 20]⟩, ⟨GateOp.or, [9, 19]⟩, ⟨GateOp.and, [21, 23]⟩, ⟨GateOp.or, [22, 24]⟩], 25⟩

theorem wit_mono : Monotone2 wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem main_aux : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1948534 : ℕ).testBit (6 * u.val + v.val)) 16 := by
  refine ⟨wit, wit_mono, by decide, ?_⟩
  decide

end PEqualNP.Outside.L_meta_23051

theorem PEqualNP.Outside.L_meta_23051 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1948534 : ℕ).testBit (6 * u.val + v.val)) 16 :=
  PEqualNP.Outside.L_meta_23051.main_aux
