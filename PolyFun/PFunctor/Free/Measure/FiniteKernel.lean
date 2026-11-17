/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Free.Measure.FiniteKernel.Attr
public import PolyFun.PFunctor.Handler.Normalization
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# Normalizing finite expected charges

`simp only [expected_cost]` pushes the fold through program constructors, evaluates a request's
incoming charge, and integrates against explicit Dirac measures and finite mixtures. Use
`handler_nf` alongside it to reduce a stateful implementation. For a kernel given as a table of
point masses, `OpSpec.statefulExpectedCharge_eq_sum` instead writes the integral as a finite sum.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

attribute [expected_cost] PFunctor.FreeM.wpFold_bind PFunctor.FreeM.wpFold_map
  PFunctor.FreeM.wpFold_lift PFunctor.FreeM.wpFold_liftBind PFunctor.FreeM.wpFold_pure
  PFunctor.OpSpec.statefulExpectedCharge_apply PFunctor.OpSpec.expectedCharge_apply
  PFunctor.Handler.Stateful.run_map Kernel.const_apply Kernel.deterministic_apply
  lintegral_zero_measure lintegral_dirac lintegral_add_measure lintegral_smul_measure

/-- With finite answers and state, the continuation contributes its mass-weighted value at
each joint outcome. -/
theorem PFunctor.OpSpec.statefulExpectedCharge_eq_sum {P : PFunctor} {S : Type*}
    [MeasurableSpace S] [∀ a, MeasurableSpace (P.B a)] [MeasurableSingletonClass S]
    [∀ a, MeasurableSingletonClass (P.B a)] [Fintype S] [∀ a, Fintype (P.B a)]
    (K : KernelHandler P S) (c : P.A → S → ℝ≥0∞) (a : P.A) (k : P.B a → S → ℝ≥0∞) (s : S) :
    statefulExpectedCharge K c a k s =
      c a s + ∑ z : P.B a × S, k z.1 z.2 * K a s {z} := by
  rw [statefulExpectedCharge_apply, lintegral_fintype]
