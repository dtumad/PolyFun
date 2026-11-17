/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Resumption.Measure.Collect
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# One setup charge across any number of retries and stages

Every attempt has equal success and retry mass. The first one also pays five units to start
the service. Both possible outcomes leave it warm for every later attempt.
-/

public section

open PFunctor PFunctor.Resumption MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PolyFunTest.Probability.CollectPotential

abbrev Trial := monomial Unit Bool

private noncomputable def service : KernelHandler Trial Bool := fun _ =>
  Kernel.const Bool ((2 : ℝ≥0∞)⁻¹ • Measure.dirac (false, true) +
    (2 : ℝ≥0∞)⁻¹ • Measure.dirac (true, true))

private def accept (_ : ℕ) (_ : Unit) (b : Bool) : Option Unit := if b then some () else none

private def bank (warm : Bool) : ℝ≥0∞ := if warm then 0 else 5

private def price (_ : Trial.A) (warm : Bool) : ℝ≥0∞ := 1 + bank warm

private theorem retry_mass (i : ℕ) (x : Unit) (s : Bool) :
    service () s {z | accept i x z.1 = none} = (2 : ℝ≥0∞)⁻¹ := by
  simp [service, accept, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply]

/-- The setup credit is needed just once, even though the number of attempts is unbounded. -/
example (k : ℕ) :
    expectedCharge service price (Collect.collect (fun _ _ => ()) accept k ()) (fun _ _ => 0)
      false ≤ (k : ℝ≥0∞) * 2 + 5 := by
  have h := Collect.expectedCharge_collect_le_of_potential service (fun _ _ => ()) accept
    price (fun _ => Measurable.of_discrete) (fun _ _ _ => True)
    (fun _ => (2 : ℝ≥0∞)⁻¹) (fun _ => 1) (fun _ _ => bank)
    (fun _ _ _ _ => by norm_num) (fun _ _ _ _ => Filter.Eventually.of_forall fun z => by
      cases z.1 <;> simp [accept]) (fun i x s _ => by rw [retry_mass]; norm_num)
    (fun _ _ _ _ => by norm_num [service, Measure.add_apply, Measure.smul_apply,
      ENNReal.inv_two_add_inv_two])
    (fun i x s _ => by
      simp [service, accept, price, bank, lintegral_add_measure, lintegral_smul_measure])
    (fun _ _ => 0) (fun _ => measurable_const) 0 (fun _ _ _ => zero_le) k () false trivial
  simpa [bank, div_eq_mul_inv] using h

end PolyFunTest.Probability.CollectPotential
