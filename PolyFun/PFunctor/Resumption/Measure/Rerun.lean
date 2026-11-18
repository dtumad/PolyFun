/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Resumption.Measure.ExpectedCharge

/-!
# Expected charges of adaptive reruns

In a fixed random world every challenge has its own price. The client may use everything it
has learned to choose its next challenge. Taking the worst price within each world gives an
expected total cost bound without any independence assumption between the choices and the world.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace PFunctor.Resumption

variable {P : PFunctor} {S α : Type*} [MeasurableSpace S] [∀ a, MeasurableSpace (P.B a)]
  [∀ a, Countable (P.B a)] [∀ a, MeasurableSingletonClass (P.B a)]

private theorem fold_charge_le_mul {β : Type*} (K : KernelHandler P S) (c d : P.A → S → ℝ≥0∞)
    (hd : ∀ a, Measurable (d a)) (B : ℝ≥0∞) (hle : ∀ a s, c a s ≤ B * d a s)
    (x : FreeM P β) (s : S) :
    FreeM.wpFold (OpSpec.statefulExpectedCharge K c) x (fun _ _ => 0) s ≤
      B * FreeM.wpFold (OpSpec.statefulExpectedCharge K d) x (fun _ _ => 0) s := by
  induction x using FreeM.rec generalizing s with
  | pure => simp
  | liftBind a k ih =>
    simp only [FreeM.wpFold_liftBind, OpSpec.statefulExpectedCharge_apply, mul_add]
    refine add_le_add (hle a s) ?_
    rw [← lintegral_const_mul _ (measurable_from_prod_countable_right fun b =>
      FreeM.measurable_wpFold_statefulExpectedCharge K d hd (k b) (fun _ => measurable_const))]
    exact lintegral_mono fun z => ih z.1 z.2

/-- A pointwise exchange rate between two per-call charges bounds the cost of an entire
unbounded adaptive program, including the work done by unfinished runs. -/
theorem expectedCharge_le_mul (K : KernelHandler P S) (c d : P.A → S → ℝ≥0∞)
    (hd : ∀ a, Measurable (d a)) (B : ℝ≥0∞) (hle : ∀ a s, c a s ≤ B * d a s)
    (x : Resumption P α) (s : S) :
    expectedCharge K c x (fun _ _ => 0) s ≤ B * expectedCharge K d x (fun _ _ => 0) s := by
  simp only [expectedCharge_eq_iSup, ENNReal.mul_iSup]
  have hz : (fun r : Option α => r.elim (fun _ : S => (0 : ℝ≥0∞)) (fun _ _ => 0)) =
      (fun _ _ => 0) := by funext r; cases r <;> rfl
  simp only [hz]
  exact iSup_mono fun n => fold_charge_le_mul K c d hd B hle (truncate n x) s

/-- A per-world price multiplies a base meter. A zero base price allows free observations
between paid challenges. -/
theorem expectedCharge_priced_reruns_le {W : Type*} [MeasurableSpace W] (μ : Measure W)
    (K : W → KernelHandler P S) (x : W → Resumption P α) (initial : W → S)
    (count : P.A → S → ℝ≥0∞) (hc : ∀ a, Measurable (count a))
    (price : W → P.A → ℝ≥0∞) (T : ℝ≥0∞) (hm : Measurable fun w => ⨆ a, price w a)
    (hcount : ∀ᵐ w ∂μ, expectedCharge (K w) count (x w) (fun _ _ => 0) (initial w) ≤ T) :
    ∫⁻ w, expectedCharge (K w) (fun a t => price w a * count a t) (x w)
      (fun _ _ => 0) (initial w) ∂μ ≤ T * ∫⁻ w, ⨆ a, price w a ∂μ := by
  rw [← lintegral_const_mul _ hm]
  apply lintegral_mono_ae
  filter_upwards [hcount] with w hw
  refine (expectedCharge_le_mul (K w) _ count hc _ (fun a _ =>
    mul_le_mul_of_nonneg_right (le_iSup (price w) a) zero_le) (x w) (initial w)).trans ?_
  rw [mul_comm T]
  exact mul_le_mul_of_nonneg_left hw zero_le

/-- A client that makes at most `T` expected unit-priced calls in each frozen world can
select its challenges adaptively. The supremum of their prices is taken inside the integral.
The kernel, initial state and client itself may all depend on the world. The statement
uses a lower integral, which gives the ordinary expectation for a measurable world cost. -/
theorem expectedCharge_reruns_le {W : Type*} [MeasurableSpace W] (μ : Measure W)
    (K : W → KernelHandler P S) (x : W → Resumption P α) (initial : W → S)
    (price : W → P.A → ℝ≥0∞) (T : ℝ≥0∞)
    (hm : Measurable fun w => ⨆ a, price w a)
    (hcount : ∀ᵐ w ∂μ, expectedCharge (K w) (fun _ _ => 1) (x w)
      (fun _ _ => 0) (initial w) ≤ T) :
    ∫⁻ w, expectedCharge (K w) (fun a _ => price w a) (x w) (fun _ _ => 0) (initial w) ∂μ ≤
      T * ∫⁻ w, ⨆ a, price w a ∂μ := by
  simpa only [mul_one] using expectedCharge_priced_reruns_le μ K x initial (fun _ _ => 1)
    (fun _ => measurable_const) price T hm hcount

end PFunctor.Resumption
