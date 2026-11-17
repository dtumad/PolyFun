/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.Tutorials.FiniteSortReadout
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Tied ranks after a nontrivial sort

Sorting the input `(2, 1, 1)` places the tied entries in the first two output ranks. The third
weight is free. Both examples use the actual sorted tuple.
-/

public section

namespace PolyFunTest.Examples.FiniteSortReadout

open _root_.Examples.FiniteSortReadout

/-- The largest entry precedes the two equal smaller entries. -/
def input : Fin 3 → ℝ := ![2, 1, 1]

private theorem sorted_input (i : Fin 3) : input (Tuple.sort input i) = ![1, 1, (2 : ℝ)] i := by
  let p := Equiv.swap (0 : Fin 3) 2
  have hp : Monotone (input ∘ p) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num [p, Equiv.swap_apply_def, input] at *
  have hi := congrFun (Tuple.comp_sort_eq_comp_iff_monotone.mpr hp).symm i
  fin_cases i <;> simpa [p, Equiv.swap_apply_def, input] using hi

/-- The weights may differ at the isolated largest rank. -/
theorem differentiableAt_fixture_iff (a b c : ℝ) :
    DifferentiableAt ℝ (sortedReadout (weighted ![a, b, c])) input ↔ a = b := by
  rw [differentiableAt_weighted_iff]
  simp only [sorted_input]
  constructor
  · intro h
    exact h 0 1 (by norm_num)
  · rintro rfl i j h
    fin_cases i <;> fin_cases j <;> norm_num at *

example : DifferentiableAt ℝ (sortedReadout (weighted ![2, 2, 7])) input :=
  (differentiableAt_fixture_iff 2 2 7).mpr rfl

example : ¬ DifferentiableAt ℝ (sortedReadout (weighted ![2, 3, 7])) input := by
  rw [differentiableAt_fixture_iff]
  norm_num

end PolyFunTest.Examples.FiniteSortReadout
