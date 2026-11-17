/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Free.Measure.FiniteKernel
public import PolyFun.PFunctor.Free.Measure.StatefulExpectedChargePrice
public import PolyFun.PFunctor.Free.Do

/-!
# Upper bounds for a finite probabilistic client

The client pays for a second coin only after heads. The numerical fold and the upper-bound
verification condition give the same bound. Prices can be chosen after bounding the individual
resources, including an infinite price on an unused resource.
-/

public section

open Std.WP OrderDual PFunctor PFunctor.FreeM MeasureTheory ProbabilityTheory
open scoped ENNReal

set_option experimental.vcgen true

namespace PolyFunTest.Do.ExpectedCost

abbrev Coin : PFunctor.{0, 0} := monomial Unit Bool

private noncomputable def fair : KernelHandler Coin Unit :=
  fun _ => Kernel.const _ ((2⁻¹ : ℝ≥0∞) • (Measure.dirac (true, ()) + Measure.dirac (false, ())))

private def flipAgain : FreeM Coin Bool := do
  let first ← FreeM.lift (P := Coin) ()
  if first then FreeM.lift (P := Coin) () else pure false

private noncomputable abbrev charge : OpSpec Coin (Unit → ℝ≥0∞) :=
  OpSpec.statefulExpectedCharge fair (fun _ _ => 1)

example : wpFold charge flipAgain (fun _ _ => 0) () = 1 + 2⁻¹ := by
  simp only [flipAgain, charge, fair, expected_cost]
  norm_num [expected_cost]

section

private noncomputable abbrev meter : WPMonad (FreeM Coin) (Unit → ℝ≥0∞)ᵒᵈ EStack⟨⟩ᵒᵈ :=
  charge.toUpperWPMonad (OpSpec.statefulExpectedCharge_mono _ _)

attribute [local instance] meter

example : ⦃ toDual (fun _ : Unit => (1 + 2⁻¹ : ℝ≥0∞)) ⦄ flipAgain
    ⦃ fun (_ : Bool) => toDual (fun _ : Unit => (0 : ℝ≥0∞)) ⦄ := by
  unfold flipAgain
  vcgen
  simp only [binderNameHint, Lean.Order.rel_eq_le, toDual_le_toDual]
  intro s
  simp only [OpSpec.toUpperWPMonad_wp, fair, expected_cost]
  norm_num [expected_cost]

end

/-- Applying finite nonnegative prices to the call charges and the already proved
coordinate bounds. The resource indexed by true is unused. -/
example (p : Bool → ℝ≥0∞) :
    wpFold (OpSpec.statefulExpectedCharge fair (fun _ _ =>
      priceHom p bot_le (fun i => if i then 0 else 1))) flipAgain (fun _ _ => 0) () ≤
      p false * (1 + 2⁻¹) := by
  let c (i : Bool) (_ : Coin.A) (_ : Unit) : ℝ≥0∞ := if i then 0 else 1
  let B (i : Bool) : ℝ≥0∞ := if i then 0 else 1 + 2⁻¹
  have h (i : Bool) : wpFold (OpSpec.statefulExpectedCharge fair (c i)) flipAgain
      (fun _ _ => 0) () ≤ B i := by
    cases i <;> norm_num [c, B, flipAgain, fair, expected_cost]
  simpa [priceHom_apply, Fintype.sum_bool, B, c] using
    wpFold_statefulExpectedCharge_price_le fair p c (by fun_prop) flipAgain B () h

/-- An unspecified kernel keeps its joint continuation integral. -/
example (K : KernelHandler Coin Unit) (c : Coin.A → Unit → ℝ≥0∞) (k : Bool → Unit → ℝ≥0∞) :
    wpFold (OpSpec.statefulExpectedCharge K c) (FreeM.lift ()) k () =
      c () () + ∫⁻ z, k z.1 z.2 ∂K () () := by
  simp only [expected_cost]

/-- Choosing the finite table rule exposes both point masses, including for a lossy service. -/
example (K : KernelHandler Coin Unit) (c : Coin.A → Unit → ℝ≥0∞) (k : Bool → Unit → ℝ≥0∞) :
    wpFold (OpSpec.statefulExpectedCharge K c) (FreeM.lift ()) k () =
      c () () + (k false () * K () () {(false, ())} + k true () * K () () {(true, ())}) := by
  rw [wpFold_lift, OpSpec.statefulExpectedCharge_eq_sum (P := Coin)]
  simp [Fintype.sum_prod_type, add_comm]

end PolyFunTest.Do.ExpectedCost
