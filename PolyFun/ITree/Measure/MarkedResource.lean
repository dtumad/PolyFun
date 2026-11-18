/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.ITree.Measure
public import PolyFun.PFunctor.Free.Measure.MarkedResource

/-!
# Resource marks on interaction trees

Projecting out an additive tally preserves the law of the result and private state. At a
starting state of full return mass, pricing the final tally gives the incurred expected cost.
Silent steps carry zero charge.
-/

public section

open MeasureTheory ProbabilityTheory PFunctor PFunctor.Resumption OmegaCompletePartialOrder
open scoped ENNReal

namespace ITree

variable {P : PFunctor} {S M X : Type*} [MeasurableSpace S] [MeasurableSpace M]
  [∀ a, MeasurableSpace (P.B a)] [∀ a, Countable (P.B a)]
  [∀ a, MeasurableSingletonClass (P.B a)] [AddMonoid M] [MeasurableAdd₂ M]
  (J : MarkedKernelHandler P S M) [∀ a, IsSubprobabilityKernel (J a)]

private noncomputable def forgetMeter :
    MeasurableExpectation S →𝒄 MeasurableExpectation (S × M) :=
  .ofFun (fun f => ⟨fun t => f.1 t.1, f.2.comp measurable_fst⟩)
    (ωScottContinuous.of_monotone_map_ωSup ⟨fun _ _ h z => h z.1, fun _ => rfl⟩)

omit [AddMonoid M] [MeasurableAdd₂ M] in
private theorem forgetMeter_apply (f : MeasurableExpectation S) (z : S × M) :
    (forgetMeter f).1 z = f.1 z.1 := rfl

/-- Reading only the private state makes every initial resource tally equivalent. -/
theorem expectedCharge_accumulate (c : P.A → S → ℝ≥0∞) (hc : ∀ a, Measurable (c a))
    (x : ITree P X) (post : X → MeasurableExpectation S) (s : S) (r : M) :
    expectedCharge J.accumulate (fun a t => c a t.1) (fun a => (hc a).comp measurable_fst)
      x (fun v => ⟨fun t => (post v).1 t.1, (post v).2.comp measurable_fst⟩) (s, r) =
      expectedCharge J.marginal c hc x post s := by
  rw [expectedCharge_eq_denote, expectedCharge_eq_denote]
  have h := denote_fusion post (statefulExpectedChargeAlgebra J.marginal c hc)
    (statefulExpectedChargeAlgebra J.accumulate (fun a t => c a t.1)
      (fun a => (hc a).comp measurable_fst)) forgetMeter rfl (fun a k => by
        apply Subtype.ext
        funext ⟨t, m⟩
        have e := J.wpFold_accumulate c hc (FreeM.lift a) (fun b => (k b).1)
          (fun b => (k b).2) t m
        change (statefulExpectedChargeAlgebra J.marginal c hc a k).1 t = _
        simp only [statefulExpectedChargeAlgebra_apply, forgetMeter_apply]
        simpa only [FreeM.wpFold_lift, OpSpec.statefulExpectedCharge_apply] using e.symm) x
  exact congrArg (fun e : MeasurableExpectation (S × M) => e.1 (s, r)) h.symm

variable [MeasurableSpace X]

/-- Erasing the marks gives the return law of the original interaction tree. -/
theorem map_returnedKernel_accumulate (x : ITree P X) (s : S) (r : M) :
    (returnedKernel J.accumulate x (s, r)).map (fun z => (z.1, z.2.1)) =
      returnedKernel J.marginal x s := by
  have hm : Measurable (fun z : X × S × M => (z.1, z.2.1)) := by fun_prop
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf hm, ← expectedCharge_zero_eq_lintegral J.marginal x _ hf]
  exact (expectedCharge_zero_eq_lintegral J.accumulate x _ (hf.comp hm) (s, r)).symm.trans
    (expectedCharge_accumulate J 0 (fun _ => measurable_const) x
      (fun x => ⟨fun t => f (x, t), hf.comp (measurable_const.prodMk measurable_id)⟩) s r)

variable (p : M →+ ℝ≥0∞) (hp : Measurable p) {c : P.A → S → ℝ≥0∞} (hc : J.IsCharge p c)

include hp hc in
/-- Under a per-operation charge certificate, returned resource marks account for at most
the work incurred before return or divergence. -/
theorem lintegral_price_accumulate_le (x : ITree P X) (s : S) :
    ∫⁻ z, p z.2.2 ∂returnedKernel J.accumulate x (s, 0) ≤
      expectedCharge J.marginal c hc.measurable x (fun _ => ⊥) s := by
  have h := lintegral_meter_le_expectedCharge J.accumulate (fun a t => c a t.1)
    (fun a => (hc.measurable a).comp measurable_fst) (fun t => p t.2)
    (hp.comp measurable_snd) (hc.accumulate_le J p hp) x (s, 0)
  simpa only [map_zero, add_zero] using h.trans_eq
    (congrArg (fun t => t + p (0 : M))
      (expectedCharge_accumulate J c hc.measurable x (fun _ => ⊥) s 0))

include hp hc in
/-- Full return mass is required only at the chosen initial state. The common expected price
of completed and incurred work can be infinite. -/
theorem lintegral_price_accumulate_eq (x : ITree P X) (s : S)
    (hmass : returnedKernel J.marginal x s Set.univ = 1) :
    ∫⁻ z, p z.2.2 ∂returnedKernel J.accumulate x (s, 0) =
      expectedCharge J.marginal c hc.measurable x (fun _ => ⊥) s := by
  have hm : Measurable (fun z : X × S × M => (z.1, z.2.1)) := by fun_prop
  rw [← map_returnedKernel_accumulate J x s 0, Measure.map_apply hm .univ,
    Set.preimage_univ] at hmass
  have h := lintegral_meter_eq_expectedCharge_of_returnMass J.accumulate (fun a t => c a t.1)
    (fun a => (hc.measurable a).comp measurable_fst) (fun t => p t.2)
    (hp.comp measurable_snd) (J.ae_price_le_accumulate p hp)
    (hc.accumulate_le J p hp) (hc.accumulate_eq_of_mass_one J p hp) x (s, 0) hmass
  simpa only [map_zero, add_zero] using h.trans
    (congrArg (fun t => t + p (0 : M))
      (expectedCharge_accumulate J c hc.measurable x (fun _ => ⊥) s 0))

end ITree
