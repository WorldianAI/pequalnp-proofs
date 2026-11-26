import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23050

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def wit : Circuit :=
  ⟨[⟨GateOp.or, [1, 5]⟩, ⟨GateOp.or, [2, 10]⟩, ⟨GateOp.or, [0, 11]⟩, ⟨GateOp.or, [3, 10]⟩, ⟨GateOp.or, [2, 6]⟩, ⟨GateOp.or, [9, 14]⟩, ⟨GateOp.and, [13, 14]⟩, ⟨GateOp.or, [0, 4]⟩, ⟨GateOp.and, [7, 12]⟩, ⟨GateOp.or, [3, 8]⟩, ⟨GateOp.or, [13, 15]⟩, ⟨GateOp.and, [12, 19]⟩, ⟨GateOp.and, [17, 20]⟩, ⟨GateOp.or, [18, 22]⟩, ⟨GateOp.or, [16, 23]⟩, ⟨GateOp.or, [21, 24]⟩], 25⟩

theorem wit_mono : Monotone2 wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem main_aux : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1947518 : ℕ).testBit (6 * u.val + v.val)) 16 := by
  refine ⟨wit, wit_mono, by decide, ?_⟩
  decide

end PEqualNP.Outside.L_meta_23050

theorem PEqualNP.Outside.L_meta_23050 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1947518 : ℕ).testBit (6 * u.val + v.val)) 16 :=
  PEqualNP.Outside.L_meta_23050.main_aux
