/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Resumption.Measure.Collect
public import PolyFun.PFunctor.Resumption.Measure.MarkedResource
public import PolyFun.PFunctor.Handler.CertifiedVec

/-!
# A fair collector with two separately priced resources

A stage waits for its requested bit and switches the request after success. Each attempt
increments the coordinate of the bit actually drawn. A fair draw gives a mean of one
unit of each resource per completed stage under every nonnegative linear price.
-/

public section

open PFunctor PFunctor.Resumption MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PolyFunTest.Probability.MarkedCollector

abbrev Request := monomial Bool Bool
abbrev Counts := Bool → ℝ≥0∞
noncomputable abbrev half := (2 : ℝ≥0∞)⁻¹

def unitMark (b : Bool) : Counts := fun i => if i = b then 1 else 0

noncomputable def service : MarkedKernelHandler Request Unit Counts := fun _ =>
  Kernel.const _ (half • (Measure.dirac (true, (), unitMark true) +
    Measure.dirac (false, (), unitMark false)))

instance (a : Request.A) : IsSubprobabilityKernel (service a) := by
  constructor
  intro s
  norm_num [service, Kernel.const_apply, smul_apply, add_apply, smul_eq_mul,
    ENNReal.inv_two_add_inv_two]

noncomputable def price (w : Bool → ℝ≥0∞) : Counts →+ ℝ≥0∞ :=
  (priceHom w bot_le).toAddMonoidHom

private theorem measurable_price (w : Bool → ℝ≥0∞) : Measurable (price w) := by
  change Measurable (fun u : Counts => ∑ i, w i * u i)
  fun_prop

private theorem price_unit (w : Bool → ℝ≥0∞) (b : Bool) : price w (unitMark b) = w b := by
  change ∑ i, w i * unitMark b i = w b
  cases b <;> simp [unitMark]

noncomputable abbrev mean (w : Bool → ℝ≥0∞) := half * (w true + w false)

private theorem priced (w : Bool → ℝ≥0∞) : service.IsCharge (price w) (fun _ _ => mean w) := by
  have eqn (a : Request.A) (s : Unit) : (∫⁻ z, price w z.2.2 ∂service a s) = mean w := by
    simp [service, Kernel.const_apply, lintegral_smul_measure, lintegral_add_measure, price_unit,
      mean, mul_add]
  exact ⟨fun _ => measurable_const, fun a s => (eqn a s).le, fun a s _ => eqn a s⟩

def request (_ : ℕ) (want : Bool) : Request.A := want

def advance (_ : ℕ) (want answer : Bool) : Option Bool :=
  if answer = want then some (!want) else none

abbrev collector (k : ℕ) (want : Bool) := Collect.collect request advance k want

private theorem forget (a : Request.A) (s : Unit) : service.marginal a s =
    half • (Measure.dirac (true, ()) + Measure.dirac (false, ())) := by
  have proj : Measurable (fun z : Bool × (Unit × Counts) => (z.1, z.2.1)) := by fun_prop
  rw [service.marginal_apply a s]
  simp [service, Kernel.const_apply, Measure.map_add _ _ proj,
    Measure.map_smul half proj.aemeasurable, Measure.map_dirac' proj]

private theorem accepted (i : ℕ) (want : Bool) (s : Unit) :
    service.marginal (request i want) s {z | (advance i want z.1).isSome} = half := by
  rw [forget (request i want) s]
  cases want <;> simp [smul_apply, add_apply, Measure.dirac_apply, advance]

private theorem total (a : Request.A) (s : Unit) : service.marginal a s Set.univ = 1 := by
  norm_num [forget, smul_apply, add_apply, smul_eq_mul, ENNReal.inv_two_add_inv_two]

private theorem preserves : Collect.StagesPreserve service.marginal request advance
    (fun _ _ _ => True) := by
  intro i x t _
  exact Filter.Eventually.of_forall fun z => by
    cases z.1 <;> cases x <;> trivial

private theorem full (k : ℕ) (want : Bool) :
    returnedKernel service.marginal (collector k want) () Set.univ = 1 :=
  Collect.returnedKernel_collect_univ_of_accept service.marginal request advance
    (fun _ _ _ => True) (fun _ => half) (fun _ _ _ _ => by norm_num) preserves
    (fun i x s _ => (accepted i x s).ge) (fun i x s _ => total _ s) k want () trivial

/-- A collector of any length completes almost surely and pays the same expected marked and
incurred bills. The prices can be infinite. -/
theorem terminal_price_collect (w : Bool → ℝ≥0∞) (k : ℕ) (want : Bool) :
    ∫⁻ z, price w z.2.2 ∂service.returnedJoint (collector k want) () =
      k * (w true + w false) := by
  rw [service.lintegral_price_returnedJoint_eq (price w) (measurable_price w) (priced w)
    _ _ (full k want)]
  have cost := Collect.expectedCharge_collect_eq_of_accept service.marginal request advance
    (fun _ _ => mean w) (fun _ => measurable_const) (fun _ _ _ => True)
    (fun _ => half) (fun _ => mean w) (fun _ _ _ _ => by norm_num) preserves
    (fun i x s _ => accepted i x s) (fun i x s _ => total _ s) (fun _ _ _ _ => rfl)
    (fun _ _ => 0) (fun _ => measurable_const) 0 (fun _ _ _ => rfl) k want () trivial
  have stage : mean w / half = w true + w false := by
    rw [mean, div_eq_mul_inv, mul_comm half, mul_assoc,
      ENNReal.mul_inv_cancel (by norm_num : half ≠ 0) (by norm_num : half ≠ ∞), mul_one]
  simpa only [stage, Finset.sum_const, Finset.card_range, nsmul_eq_mul, add_zero] using cost

/-! ## A noisy terminal display -/

noncomputable def display : Kernel (Bool × Unit) Bool :=
  ⟨fun z => (3 / 4 : ℝ≥0∞) • Measure.dirac z.1 + (1 / 4 : ℝ≥0∞) • Measure.dirac (!z.1),
    Measurable.of_discrete⟩

def seesTrue (b : Bool) : ℝ≥0∞ := if b then 1 else 0

private theorem response (b : Bool) (s : Unit) :
    (∫⁻ t, seesTrue t ∂display (b, s)) = if b then 3 / 4 else 1 / 4 := by
  cases b <;> simp [display, Kernel.coe_mk, seesTrue, lintegral_add_measure, lintegral_smul_measure]

private theorem total_report : (3 : ℝ≥0∞) / 4 + 1 / 4 = 1 := by
  rw [← ENNReal.add_div, show (3 : ℝ≥0∞) + 1 = 4 by norm_num, ENNReal.div_self] <;> norm_num

instance : IsMarkovKernel display := ⟨fun _ => ⟨by
  simpa [display, Kernel.coe_mk, smul_apply, smul_eq_mul] using total_report⟩⟩

def headPrice (b : Bool) : ℝ≥0∞ := if b then 2 else 0

/-- The display reports the drawn bit correctly with probability three quarters. Both
readings use this same channel. Heads incur two units and tails are free, so the ordinary
true-report probability is one half and its cost-weighted observation is three quarters. -/
theorem noisy_display (a : Bool) :
    let x := FreeM.lift (P := Request) a
    (∫⁻ t, seesTrue t ∂((FreeM.runKernel service.marginal x ()).bind display)) = half ∧
    (∫⁻ t, seesTrue t ∂((((service.joint x ()).withDensity (fun z => price headPrice z.2.2)).map
      (fun z => (z.1, z.2.1))).bind display)) = 3 / 4 := by
  dsimp only
  constructor
  · rw [Measure.lintegral_bind display.aemeasurable Measurable.of_discrete.aemeasurable,
      FreeM.runKernel_lift (P := Request), forget a ()]
    norm_num [lintegral_smul_measure, lintegral_add_measure, response, ← mul_add]
    simpa only [one_div, mul_one] using congrArg (half * ·) total_report
  · rw [service.bill_display (price headPrice) (measurable_price _) _ _ display seesTrue
      Measurable.of_discrete, MarkedKernelHandler.bill_apply (P := Request),
      service.joint_lift a ()]
    norm_num [service, Kernel.const_apply, lintegral_smul_measure, lintegral_add_measure,
      price_unit, headPrice, response, ← mul_assoc, ENNReal.inv_mul_cancel]

end PolyFunTest.Probability.MarkedCollector
