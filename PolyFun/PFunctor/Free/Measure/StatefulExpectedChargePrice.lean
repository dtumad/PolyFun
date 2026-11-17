/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Free.Measure.StatefulExpectedCharge
public import PolyFun.PFunctor.Handler.CertifiedVec

/-!
# Pricing expected charges

The price of a finite vector of nonnegative costs is its weighted sum. The expected charge of
a priced meter is exactly the price of the coordinate expectations, including for correlated
resources and for subprobability kernels.
-/

public section

open MeasureTheory
open scoped ENNReal BigOperators

universe uA uB uS v

namespace PFunctor.FreeM

variable {P : PFunctor.{uA, uB}} {S : Type uS} [MeasurableSpace S]
  [∀ a, MeasurableSpace (P.B a)] [∀ a, Countable (P.B a)]
  [∀ a, MeasurableSingletonClass (P.B a)] {ι : Type*} [Fintype ι] {α : Type v}

/-- Pricing commutes with the entire stateful expectation fold, including terminal observations. -/
theorem wpFold_statefulExpectedCharge_price (K : KernelHandler P S) (p : ι → ℝ≥0∞)
    (c : ι → P.A → S → ℝ≥0∞) (hc : ∀ i a, Measurable (c i a))
    (x : FreeM P α) (post : ι → α → S → ℝ≥0∞) (hpost : ∀ i r, Measurable (post i r)) (s : S) :
    wpFold (OpSpec.statefulExpectedCharge K (fun a t => priceHom p bot_le (fun i => c i a t)))
        x (fun r t => priceHom p bot_le (fun i => post i r t)) s =
      priceHom p bot_le (fun i => wpFold (OpSpec.statefulExpectedCharge K (c i)) x (post i) s) := by
  induction x using FreeM.rec generalizing s with
  | pure r => rfl
  | liftBind a next ih =>
    have hm (i : ι) : Measurable (fun z : P.B a × S =>
        wpFold (OpSpec.statefulExpectedCharge K (c i)) (next z.1) (post i) z.2) :=
      measurable_from_prod_countable_right fun b =>
        measurable_wpFold_statefulExpectedCharge K _ (hc i) (next b) (hpost i)
    simp only [wpFold_liftBind, OpSpec.statefulExpectedCharge_apply, ih]
    simp only [priceHom_apply, mul_add, Finset.sum_add_distrib]
    congr 1
    rw [lintegral_finsetSum Finset.univ (f := fun i (z : P.B a × S) => p i *
      wpFold (OpSpec.statefulExpectedCharge K (c i)) (next z.1) (post i) z.2)
      (fun i _ => measurable_const.mul (hm i))]
    exact Finset.sum_congr rfl (fun i _ => lintegral_const_mul _ (hm i))

/-- A price can be chosen after proving coordinate bounds. -/
theorem wpFold_statefulExpectedCharge_price_le (K : KernelHandler P S) (p : ι → ℝ≥0∞)
    (c : ι → P.A → S → ℝ≥0∞) (hc : ∀ i a, Measurable (c i a))
    (x : FreeM P α) (B : ι → ℝ≥0∞) (s : S)
    (hB : ∀ i, wpFold (OpSpec.statefulExpectedCharge K (c i)) x (fun _ _ => 0) s ≤ B i) :
    wpFold (OpSpec.statefulExpectedCharge K (fun a t => priceHom p bot_le (fun i => c i a t)))
        x (fun _ _ => 0) s ≤ priceHom p bot_le B := by
  simpa using (wpFold_statefulExpectedCharge_price K p c hc x (fun _ _ _ => 0)
    (fun _ _ => measurable_const) s).trans_le (Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (hB i) zero_le)

end PFunctor.FreeM
