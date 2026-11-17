/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.Tutorials.SortedPairReadout
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Readouts that detect the sorting boundary

With weights 2 and 5 the derivative along the first coordinate changes between strict
orderings. At the origin the minimum has a corner and its square has derivative zero.
-/

public section

namespace PolyFunTest.Examples.SortedPairReadout

open _root_.Examples.SortedPairReadout

example : fderiv ℝ (readout 2 5) (0, 1) (1, 0) = 2 := by
  rw [(hasFDerivAt_readout_of_fst_lt 2 5 (x := (0, 1)) (by norm_num)).fderiv]
  norm_num

example : fderiv ℝ (readout 2 5) (1, 0) (1, 0) = 5 := by
  rw [(hasFDerivAt_readout_of_snd_lt 2 5 (x := (1, 0)) (by norm_num)).fderiv]
  norm_num

example (u c : ℝ) : DifferentiableAt ℝ (readout u u) (c, c) :=
  (differentiableAt_readout_tie_iff u u c).mpr rfl

/-- Choosing the smaller coordinate is nondifferentiable at every tie. -/
theorem not_differentiableAt_min (c : ℝ) :
    ¬ DifferentiableAt ℝ (fun x : ℝ × ℝ => min x.1 x.2) (c, c) := by
  have h : readout 1 0 = fun x : ℝ × ℝ => min x.1 x.2 := by
    funext x
    simp
  rw [← h, differentiableAt_readout_tie_iff]
  norm_num

/-- Squaring the minimum kills its first-order change at the origin. -/
theorem hasFDerivAt_min_sq :
    HasFDerivAt (fun x : ℝ × ℝ => (min x.1 x.2) ^ 2) (0 : (ℝ × ℝ) →L[ℝ] ℝ) (0, 0) := by
  have hp := (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt (x := ((0, 0) : ℝ × ℝ))
  have hz : HasFDerivAt (fun x : ℝ × ℝ => x.1 * x.1) (0 : (ℝ × ℝ) →L[ℝ] ℝ) (0, 0) := by
    simpa [Pi.mul_def] using! hp.mul hp
  have hs := (hasFDerivAt_comp_sorted_iff hz 0).mpr ⟨rfl, by simp⟩
  simpa [Function.comp_def, sorted, pow_two] using hs

end PolyFunTest.Examples.SortedPairReadout
