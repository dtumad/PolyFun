/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Resumption.Measure.Rerun
import PolyFun.PFunctor.Free.Measure.FiniteKernel
import PolyFun.PFunctor.Free.Measure.MarkedResource

/-!
# Adaptive selection and resource observations

Reading a frozen bit is free. Each fixed challenge costs one on average, but the client
that reads the bit and asks for the matching challenge always pays two. A second example
separates the mean of a returned resource from the probability of crossing a threshold.
-/

public section

open PFunctor MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PolyFunTest.Probability.AdaptiveResource

abbrev Oracle := monomial (Option Bool) Bool

private noncomputable def service (w : Bool) : KernelHandler Oracle Unit := fun op =>
  Kernel.const _ (Measure.dirac (op.elim w (fun _ => true), ()))

private def finder : FreeM Oracle Bool := do
  let world ← FreeM.lift (P := Oracle) none
  FreeM.lift (some world)

private def price (w : Bool) : Option Bool → ℝ≥0∞
  | none => 0
  | some a => if a = w then 2 else 0

private def calls (a : Option Bool) (_ : Unit) : ℝ≥0∞ := if a.isSome then 1 else 0

private noncomputable def worlds : Measure Bool :=
  (2⁻¹ : ℝ≥0∞) • (Measure.dirac true + Measure.dirac false)

private theorem count_finder (w : Bool) :
    Resumption.expectedCharge (service w) calls finder.toResumption (fun _ _ => 0) () = 1 := by
  rw [Resumption.expectedCharge_toResumption (service w) calls (fun _ => measurable_const)
    finder (fun _ _ => 0) (fun _ => measurable_const)]
  cases w <;> norm_num [finder, service, calls, expected_cost]

private theorem cost_finder (w : Bool) :
    Resumption.expectedCharge (service w) (fun a t => price w a * calls a t)
      finder.toResumption (fun _ _ => 0) () = 2 := by
  rw [Resumption.expectedCharge_toResumption (service w) (fun a t => price w a * calls a t)
    (fun _ => Measurable.of_discrete) finder (fun _ _ => 0) (fun _ => measurable_const)]
  cases w <;> norm_num [finder, service, calls, price, expected_cost]

example (a : Bool) : ∫⁻ w, price w (some a) ∂worlds = 1 := by
  cases a <;> norm_num [worlds, price, lintegral_add_measure, lintegral_smul_measure,
    ENNReal.inv_mul_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num),
    ENNReal.inv_two_add_inv_two]

example : ∫⁻ w, Resumption.expectedCharge (service w) (fun a t => price w a * calls a t)
    finder.toResumption (fun _ _ => 0) () ∂worlds = 2 := by
  simp only [cost_finder]
  norm_num [worlds, lintegral_add_measure, lintegral_smul_measure,
    ENNReal.inv_mul_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num),
    ENNReal.inv_two_add_inv_two]

example : ∫⁻ w, Resumption.expectedCharge (service w) (fun a t => price w a * calls a t)
    finder.toResumption (fun _ _ => 0) () ∂worlds ≤ 1 * ∫⁻ w, ⨆ a, price w a ∂worlds :=
  Resumption.expectedCharge_priced_reruns_le worlds service (fun _ => finder.toResumption)
    (fun _ => ()) calls (fun _ => measurable_const) price 1 (Measurable.of_discrete)
    (Filter.Eventually.of_forall fun w => (count_finder w).le)

/-- The within-world envelope is attained by the matching challenge at either hidden bit. -/
private theorem sup_price (w : Bool) : (⨆ a, price w a) = 2 := by
  refine le_antisymm (iSup_le fun a => ?_) (le_iSup_of_le (some w) (by simp [price]))
  cases a with
  | none => exact zero_le
  | some a => by_cases h : a = w <;> simp [price, h]

example : ∫⁻ w, Resumption.expectedCharge (service w) (fun a t => price w a * calls a t)
    finder.toResumption (fun _ _ => 0) () ∂worlds = ∫⁻ w, ⨆ a, price w a ∂worlds := by
  simp only [sup_price, cost_finder]

private abbrev Readout := monomial Unit Unit

private noncomputable def constantMark : MarkedKernelHandler Readout Unit ℝ≥0∞ := fun _ =>
  Kernel.const Unit (Measure.dirac ((), (), 1))

private noncomputable def spreadMark : MarkedKernelHandler Readout Unit ℝ≥0∞ := fun _ =>
  Kernel.const Unit ((2⁻¹ : ℝ≥0∞) • (Measure.dirac ((), (), 0) + Measure.dirac ((), (), 2)))

private instance (a : Readout.A) : IsSubprobabilityKernel (constantMark a) := by
  unfold constantMark
  infer_instance

private instance (a : Readout.A) : IsSubprobabilityKernel (spreadMark a) := by
  constructor
  intro t
  norm_num [spreadMark, Kernel.const_apply, add_apply, smul_apply, smul_eq_mul,
    ENNReal.inv_two_add_inv_two]

private abbrev readout := FreeM.lift (P := Readout) ()

example : constantMark.bill (AddMonoidHom.id _) readout (fun _ => 1) () =
    spreadMark.bill (AddMonoidHom.id _) readout (fun _ => 1) () := by
  norm_num [readout, MarkedKernelHandler.bill_apply, constantMark, spreadMark, Kernel.const_apply,
    lintegral_add_measure, lintegral_smul_measure,
    ENNReal.inv_mul_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num),
    ENNReal.inv_two_add_inv_two]

private def overrun : Set (Unit × Unit × ℝ≥0∞) := {z | 2 ≤ z.2.2}

example : constantMark.joint readout () overrun = 0 ∧
    spreadMark.joint readout () overrun = 2⁻¹ := by
  have hm : MeasurableSet overrun := measurableSet_le measurable_const (measurable_snd.comp
    measurable_snd)
  norm_num [readout, constantMark, spreadMark, Kernel.const_apply, Measure.dirac_apply' _ hm,
    overrun, smul_apply, smul_eq_mul, Set.indicator]

end PolyFunTest.Probability.AdaptiveResource
