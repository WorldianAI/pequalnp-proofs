import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23055

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def wit : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [7, 8]⟩, ⟨GateOp.or, [9, 12]⟩, ⟨GateOp.or, [5, 9]⟩, ⟨GateOp.or, [11, 12]⟩, ⟨GateOp.or, [10, 16]⟩, ⟨GateOp.and, [12, 15]⟩, ⟨GateOp.and, [2, 16]⟩, ⟨GateOp.or, [3, 13]⟩, ⟨GateOp.and, [1, 14]⟩, ⟨GateOp.and, [17, 20]⟩, ⟨GateOp.or, [19, 22]⟩, ⟨GateOp.or, [18, 23]⟩, ⟨GateOp.or, [21, 24]⟩], 25⟩

theorem wit_mono : Monotone2 wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem main_aux : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1965690 : ℕ).testBit (6 * u.val + v.val)) 16 := by
  refine ⟨wit, wit_mono, by decide, ?_⟩
  decide

end PEqualNP.Outside.L_meta_23055

theorem PEqualNP.Outside.L_meta_23055 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1965690 : ℕ).testBit (6 * u.val + v.val)) 16 :=
  PEqualNP.Outside.L_meta_23055.main_aux
