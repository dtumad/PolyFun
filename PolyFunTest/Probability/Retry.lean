/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Resumption.Measure.Retry
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-! # Boundary cases of stateful retry -/

public section

open MeasureTheory ProbabilityTheory PFunctor.Resumption PFunctor.Resumption.Retry
open scoped ENNReal

namespace PolyFunTest.Retry

/-- The first trial always succeeds, including exactly at the fuel boundary. -/
private noncomputable def always : Kernel Unit (Bool × Unit) :=
  Kernel.const _ (Measure.dirac (true, ()))

example : observe always 1 0 1 0 () = 1 := by simp

example : observe always 0 1 0 1 () = 1 := by
  simp [observe_succ, always, lintegral_dirac]

example : observe always 1 0 0 2 () = 1 := by
  simp [observe_succ, always, lintegral_dirac]

-- A lost trial can have zero retry mass and zero success mass simultaneously.
example (n : ℕ) (done cut : ℝ≥0∞) :
    observe (0 : Kernel Unit (Bool × Unit)) 1 done cut (n + 1) () = 1 := by
  simp [observe_succ]

/-- A zero trial kernel never succeeds at any observation depth. -/
theorem zero_kernel_success : expectedCharge (fun _ => (0 : Kernel Unit (Bool × Unit)))
    (fun _ _ => 0) tree (fun _ _ => 1) () = 0 := by
  rw [expectedCharge_tree]
  apply le_antisymm _ zero_le
  refine iSup_le fun n => ?_
  cases n <;> simp [observe_succ]

end PolyFunTest.Retry
