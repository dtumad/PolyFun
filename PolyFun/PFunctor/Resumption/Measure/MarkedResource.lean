/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Resumption.Measure.TerminalCharge
public import PolyFun.PFunctor.Free.Measure.MarkedResource

/-!
# Marked resources on unbounded resumptions

The tally records a joint law of the returned value, private state and resources spent.
For every measurable additive price, the expected terminal bill is bounded by incurred
cost, with equality at every initial state of full return mass.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PFunctor.MarkedKernelHandler

variable {P : PFunctor} {S R X : Type*} [∀ a, MeasurableSpace (P.B a)]
  [∀ a, Countable (P.B a)] [∀ a, MeasurableSingletonClass (P.B a)]
  [MeasurableSpace S] [MeasurableSpace R] [AddMonoid R] [MeasurableAdd₂ R]
  (J : MarkedKernelHandler P S R) [∀ a, IsSubprobabilityKernel (J a)]

/-- Forgetting the tally preserves all incurred charges and terminal credits on unbounded runs. -/
theorem expectedCharge_accumulate (c : P.A → S → ℝ≥0∞) (hc : ∀ a, Measurable (c a))
    (x : Resumption P X) (post : X → S → ℝ≥0∞) (hpost : ∀ v, Measurable (post v))
    (s : S) (r : R) :
    Resumption.expectedCharge J.accumulate (fun a t => c a t.1) x (fun v t => post v t.1) (s, r) =
      Resumption.expectedCharge J.marginal c x post s := by
  simp only [Resumption.expectedCharge_eq_iSup]
  congr 1
  funext n
  let f (o : Option X) := o.elim (fun _ : S => (0 : ℝ≥0∞)) post
  have eq : (fun o : Option X => o.elim (fun _ : S × R => (0 : ℝ≥0∞))
      (fun v t => post v t.1)) = (fun o t => f o t.1) := by
    funext o t
    cases o <;> rfl
  rw [eq]
  exact J.wpFold_accumulate c hc _ f (fun o => by cases o with
    | none => exact measurable_const
    | some v => exact hpost v) s r

variable [MeasurableSpace X]

/-- Pushforward of the marked return law recovers the unmarked answer and final state. -/
theorem map_returnedKernel_accumulate (x : Resumption P X) (s : S) (r : R) :
    (Resumption.returnedKernel J.accumulate x (s, r)).map (fun z => (z.1, z.2.1)) =
      Resumption.returnedKernel J.marginal x s := by
  apply Measure.ext_of_lintegral
  intro f hf
  have proj : Measurable (fun z : X × (S × R) => (z.1, z.2.1)) := by fun_prop
  rw [lintegral_map hf proj, ← Resumption.expectedCharge_zero_eq_lintegral J.accumulate x
    (fun z => f (z.1, z.2.1)) (hf.comp proj),
    ← Resumption.expectedCharge_zero_eq_lintegral _ _ _ hf]
  exact J.expectedCharge_accumulate 0 (fun _ => measurable_const) x (Function.curry f)
    (fun v => hf.comp (measurable_const.prodMk measurable_id)) s r

/-- Joint law of the return, final private state, and total mark on unbounded runs. -/
@[expose] noncomputable def returnedJoint (x : Resumption P X) : Kernel S (X × (S × R)) :=
  (Resumption.returnedKernel J.accumulate x).comap
    (fun s => (s, 0)) (measurable_id.prodMk measurable_const)

omit [MeasurableAdd₂ R] [∀ a, IsSubprobabilityKernel (J a)] in
/-- A well-founded program has the same returned marks under the resumption interpretation. -/
@[simp] theorem returnedJoint_toResumption (x : FreeM P X) (s : S) :
    J.returnedJoint x.toResumption s = J.joint x s := by
  rw [returnedJoint, Resumption.returnedKernel_toResumption, Kernel.comap_apply, joint_apply]

variable (price : R →+ ℝ≥0∞) (hp : Measurable price) {c : P.A → S → ℝ≥0∞}
  (hc : J.IsCharge price c)

include hp hc in
/-- The completed bill is bounded by all work incurred, including on nonreturning paths. -/
theorem lintegral_price_returnedJoint_le (x : Resumption P X) (s : S) :
    ∫⁻ z, price z.2.2 ∂J.returnedJoint x s ≤
      Resumption.expectedCharge J.marginal c x (fun _ _ => 0) s := by
  have h := Resumption.lintegral_meter_le_expectedCharge J.accumulate (fun a t => c a t.1)
    (fun t => price t.2) (hp.comp measurable_snd) (hc.accumulate_le J price hp) x (s, 0)
  rw [J.expectedCharge_accumulate c hc.measurable x (fun _ _ => 0) (fun _ => measurable_const)] at h
  simpa only [returnedJoint, Kernel.comap_apply, map_zero, add_zero] using h

include hp hc in
/-- At an initial state of almost-sure return the completed and incurred bills agree,
including when their common value is infinite. Full return is tested on the unmarked program. -/
theorem lintegral_price_returnedJoint_eq (x : Resumption P X) (s : S)
    (h : Resumption.returnedKernel J.marginal x s Set.univ = 1) :
    ∫⁻ z, price z.2.2 ∂J.returnedJoint x s =
      Resumption.expectedCharge J.marginal c x (fun _ _ => 0) s := by
  have proj : Measurable (fun z : X × (S × R) => (z.1, z.2.1)) := by fun_prop
  rw [← J.map_returnedKernel_accumulate x s 0, Measure.map_apply proj .univ, Set.preimage_univ] at h
  have eq := Resumption.lintegral_meter_eq_expectedCharge_of_returnMass J.accumulate
    (fun a t => c a t.1) (fun t => price t.2) (hp.comp measurable_snd)
    (J.ae_price_le_accumulate price hp) (hc.accumulate_le J price hp)
    (hc.accumulate_eq_of_mass_one J price hp) x (s, 0) h
  rw [J.expectedCharge_accumulate c hc.measurable x (fun _ _ => 0)
    (fun _ => measurable_const)] at eq
  simpa only [returnedJoint, Kernel.comap_apply, map_zero, add_zero] using eq

end PFunctor.MarkedKernelHandler
