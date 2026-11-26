import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23052

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def wit : Circuit :=
  ⟨[⟨GateOp.or, [1, 5]⟩, ⟨GateOp.or, [8, 7]⟩, ⟨GateOp.or, [4, 0]⟩, ⟨GateOp.or, [12, 10]⟩, ⟨GateOp.or, [9, 7]⟩, ⟨GateOp.or, [12, 2]⟩, ⟨GateOp.or, [3, 14]⟩, ⟨GateOp.or, [2, 16]⟩, ⟨GateOp.and, [12, 10]⟩, ⟨GateOp.or, [0, 14]⟩, ⟨GateOp.or, [15, 6]⟩, ⟨GateOp.or, [3, 11]⟩, ⟨GateOp.or, [21, 10]⟩, ⟨GateOp.and, [17, 13]⟩, ⟨GateOp.and, [20, 22]⟩, ⟨GateOp.or, [23, 24]⟩], 25⟩

theorem wit_mono : Monotone2 wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem main_aux : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1948538 : ℕ).testBit (6 * u.val + v.val)) 16 := by
  refine ⟨wit, wit_mono, by decide, ?_⟩
  decide

end PEqualNP.Outside.L_meta_23052

theorem PEqualNP.Outside.L_meta_23052 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1948538 : ℕ).testBit (6 * u.val + v.val)) 16 :=
  PEqualNP.Outside.L_meta_23052.main_aux
