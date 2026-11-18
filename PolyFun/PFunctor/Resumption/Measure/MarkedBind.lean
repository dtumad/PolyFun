/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Resumption.Measure.MarkedResource

/-!
# Sequencing unbounded programs with marked resources

A continuation starts from the returned private state and adds its resource to the tally of
the first program. Consequently the price of the first program contributes to the completed
bill only in proportion to the continuation's returned observation.
-/

public section

open MeasureTheory ProbabilityTheory OmegaCompletePartialOrder
open scoped ENNReal

namespace PFunctor.Resumption

variable {P : PFunctor} {S T X : Type*} [MeasurableSpace S] [MeasurableSpace T]
  [MeasurableSpace X] [∀ a, MeasurableSpace (P.B a)]
  [∀ a, Countable (P.B a)] [∀ a, MeasurableSingletonClass (P.B a)]

/-- A measurable map commuting with the operation kernels commutes with the joint
return law, including for unbounded clients. -/
theorem map_returnedKernel_state (K : KernelHandler P S) (L : KernelHandler P T)
    (φ : S → T) (hm : Measurable φ)
    (step : ∀ a s, (K a s).map (fun z => (z.1, φ z.2)) = L a (φ s))
    (x : Resumption P X) (s : S) :
    (returnedKernel K x s).map (fun z => (z.1, φ z.2)) = returnedKernel L x (φ s) := by
  let pull : MeasurableExpectation T →𝒄 MeasurableExpectation S :=
    .ofFun (fun g => ⟨g.1 ∘ φ, g.2.comp hm⟩) (ωScottContinuous.of_monotone_map_ωSup
      ⟨fun _ _ h s => h (φ s), fun _ => rfl⟩)
  let algL := statefulExpectedChargeAlgebra L 0 (fun _ => measurable_const)
  let algK := statefulExpectedChargeAlgebra K 0 (fun _ => measurable_const)
  have commute (a : P.A) (k : P.B a → MeasurableExpectation T) :
      pull (algL a k) = algK a (fun b => pull (k b)) := by
    apply Subtype.ext
    funext t
    change 0 + (∫⁻ z : P.B a × T, (k z.1).1 z.2 ∂L a (φ t)) =
      0 + (∫⁻ z : P.B a × S, (k z.1).1 (φ z.2) ∂K a t)
    have hg : Measurable (fun z : P.B a × T => (k z.1).1 z.2) :=
      measurable_from_prod_countable_right fun b => (k b).2
    have hφ : Measurable (fun z : P.B a × S => (z.1, φ z.2)) :=
      measurable_fst.prodMk (hm.comp measurable_snd)
    rw [← step, lintegral_map hg hφ]
  apply Measure.ext_of_lintegral
  intro f hf
  have hmap : Measurable (fun z : X × S => (z.1, φ z.2)) :=
    measurable_fst.prodMk (hm.comp measurable_snd)
  have hfφ : Measurable (fun z : X × S => f (z.1, φ z.2)) := hf.comp hmap
  rw [lintegral_map hf hmap, ← expectedCharge_zero_eq_lintegral K x _ hfφ,
    ← expectedCharge_zero_eq_lintegral L x f hf]
  let ret (v : X) : MeasurableExpectation T :=
    ⟨fun t => f (v, t), hf.comp (measurable_const.prodMk measurable_id)⟩
  change expectedCharge K 0 x (fun v => (pull (ret v)).1) s =
    expectedCharge L 0 x (fun v => (ret v).1) (φ s)
  rw [expectedCharge_eq_denote K 0 (fun _ => measurable_const) x (fun v => (pull (ret v)).1)
    (fun v => (pull (ret v)).2),
    expectedCharge_eq_denote L 0 (fun _ => measurable_const) x (fun v => (ret v).1)
      (fun v => (ret v).2)]
  exact congrArg (fun e : MeasurableExpectation S => e.1 s)
    (denote_fusion ret algL algK pull rfl commute x).symm

/-- Countable intermediate results make a stateful continuation jointly measurable in its
answer and incoming state. This supplies the hypothesis of the terminal bind laws. -/
theorem measurable_returnedKernel_continuation {Y : Type*} [MeasurableSpace Y]
    [Countable X] [MeasurableSingletonClass X] (K : KernelHandler P S)
    (k : X → Resumption P Y) :
    Measurable fun z : X × S => returnedKernel K (k z.1) z.2 :=
  measurable_from_prod_countable_right fun x => (returnedKernel K (k x)).measurable

end PFunctor.Resumption

namespace PFunctor.MarkedKernelHandler

variable {P : PFunctor} {S R X Y : Type*} [∀ a, MeasurableSpace (P.B a)]
  [∀ a, Countable (P.B a)] [∀ a, MeasurableSingletonClass (P.B a)]
  [MeasurableSpace S] [MeasurableSpace R] [AddMonoid R] [MeasurableAdd₂ R]
  [MeasurableSpace X] [MeasurableSpace Y]
  (J : MarkedKernelHandler P S R) [∀ a, IsSFiniteKernel (J a)]

/-- Starting with a tally prefixes it to the resources of each returning execution. -/
theorem returnedKernel_accumulate (x : Resumption P X) (s : S) (r : R) :
    Resumption.returnedKernel J.accumulate x (s, r) = (J.returnedJoint x s).map (prepend r) := by
  have shift := Resumption.map_returnedKernel_state J.accumulate J.accumulate
    (fun (t : S × R) => (t.1, r + t.2))
    (measurable_fst.prodMk (measurable_const.add measurable_snd)) (fun a ⟨t, v⟩ => by
      rw [accumulate_apply, accumulate_apply]
      change ((J a t).map (prepend v)).map (prepend r) = _
      rw [Measure.map_map (measurable_prepend r) (measurable_prepend v)]
      apply congrArg (fun f => (J a t).map f)
      funext z
      simp [prepend, add_assoc]) x (s, 0)
  change _ = (Resumption.returnedKernel J.accumulate x (s, 0)).map
    (fun z => (z.1, z.2.1, r + z.2.2))
  simpa only [add_zero] using shift.symm

omit [MeasurableAdd₂ R] [∀ a, IsSFiniteKernel (J a)] in
/-- Returning a value preserves private state and contributes the empty tally. -/
@[simp] theorem returnedJoint_pure (v : X) (s : S) :
    J.returnedJoint (Resumption.pure v) s = Measure.dirac (v, s, 0) := by
  rw [returnedJoint, Kernel.comap_apply, Resumption.returnedKernel_pure]

/-- At a query the continuation sees exactly the answer, state and mark of the call. -/
theorem returnedJoint_query (a : P.A) (k : P.B a → Resumption P X) (s : S) :
    J.returnedJoint (Resumption.query a k) s = (J a s).bind (fun z =>
      (J.returnedJoint (k z.1) z.2.1).map (prepend z.2.2)) := by
  rw [returnedJoint, Kernel.comap_apply, Resumption.returnedKernel_query, accumulate_apply]
  have h : (prepend (0 : R) : P.B a × (S × R) → _) = id := by
    funext z
    simp [prepend]
  rw [h, Measure.map_id]
  exact Measure.bind_congr_right (Filter.Eventually.of_forall fun z =>
    J.returnedKernel_accumulate (k z.1) z.2.1 z.2.2)

/-- The law of a sequential execution adds the two marks in their execution order. -/
theorem returnedJoint_bind (x : Resumption P X) (k : X → Resumption P Y)
    (hk : Measurable fun z : X × (S × R) => Resumption.returnedKernel J.accumulate (k z.1) z.2)
    (s : S) :
    J.returnedJoint (Resumption.bind x k) s = (J.returnedJoint x s).bind (fun z =>
      (J.returnedJoint (k z.1) z.2.1).map (prepend z.2.2)) := by
  rw [returnedJoint, Kernel.comap_apply, Resumption.returnedKernel_bind _ _ _ hk]
  exact Measure.bind_congr_right (Filter.Eventually.of_forall fun z =>
    J.returnedKernel_accumulate (k z.1) z.2.1 z.2.2)

omit [AddMonoid R] [MeasurableAdd₂ R] [MeasurableSpace Y] [∀ a, IsSFiniteKernel (J a)] in
/-- Incurring the first program's cost is independent of subsequent completion. The
continuation is charged precisely on reached answers and private states. -/
theorem expectedCharge_marginal_bind (c : P.A → S → ℝ≥0∞) (hc : ∀ a, Measurable (c a))
    (x : Resumption P X) (k : X → Resumption P Y)
    (hk : Measurable fun z : X × S =>
      Resumption.expectedCharge J.marginal c (k z.1) (fun _ _ => 0) z.2) (s : S) :
    Resumption.expectedCharge J.marginal c (Resumption.bind x k) (fun _ _ => 0) s =
      Resumption.expectedCharge J.marginal c x (fun _ _ => 0) s +
        ∫⁻ z, Resumption.expectedCharge J.marginal c (k z.1) (fun _ _ => 0) z.2
          ∂Resumption.returnedKernel J.marginal x s := by
  rw [Resumption.expectedCharge_bind J.marginal c hc _ _ _ (fun _ => measurable_const)]
  exact Resumption.expectedCharge_eq_add_lintegral J.marginal c x _ hk s

/-- The price integrated on the completed executions observed by a terminal test. -/
@[expose] noncomputable def returnedBill (price : R →+ ℝ≥0∞) (x : Resumption P X)
    (f : X × S → ℝ≥0∞) (s : S) : ℝ≥0∞ :=
  ∫⁻ z, price z.2.2 * f (z.1, z.2.1) ∂J.returnedJoint x s

/-- A first-stage charge is retained in proportion to the observed returns of its continuation,
from that particular answer and private state. -/
theorem returnedBill_bind (price : R →+ ℝ≥0∞) (hp : Measurable price)
    (x : Resumption P X) (k : X → Resumption P Y)
    (hk : Measurable fun z : X × (S × R) => Resumption.returnedKernel J.accumulate (k z.1) z.2)
    (f : Y × S → ℝ≥0∞) (hf : Measurable f) (s : S) :
    J.returnedBill price (Resumption.bind x k) f s = ∫⁻ z,
      (price z.2.2 * ∫⁻ t, f (t.1, t.2.1) ∂J.returnedJoint (k z.1) z.2.1) +
        J.returnedBill price (k z.1) f z.2.1 ∂J.returnedJoint x s := by
  have obs : Measurable (fun z : Y × (S × R) => f (z.1, z.2.1)) :=
    hf.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  have priced : Measurable (fun z : Y × (S × R) => price z.2.2 * f (z.1, z.2.1)) :=
    (hp.comp (measurable_snd.comp measurable_snd)).mul obs
  rw [returnedBill, returnedJoint, Kernel.comap_apply, Resumption.returnedKernel_bind _ _ _ hk,
    Measure.lintegral_bind hk.aemeasurable priced.aemeasurable]
  apply lintegral_congr
  intro z
  rw [returnedKernel_accumulate, lintegral_map priced (measurable_prepend _)]
  simp only [prepend, map_add, add_mul]
  have hm : Measurable (fun u : Y × (S × R) => price z.2.2 * f (u.1, u.2.1)) :=
    measurable_const.mul obs
  rw [lintegral_add_left hm, lintegral_const_mul _ obs]
  rfl

omit [MeasurableAdd₂ R] [∀ a, IsSFiniteKernel (J a)] in
/-- The completed bill specializes to the finite bill on well-founded programs. -/
@[simp] theorem returnedBill_toResumption (price : R →+ ℝ≥0∞) (x : FreeM P X)
    (f : X × S → ℝ≥0∞) (s : S) :
    J.returnedBill price x.toResumption f s = J.bill price x f s := by
  simp only [returnedBill, returnedJoint_toResumption, bill]

omit [∀ a, IsSFiniteKernel (J a)] in
/-- A terminal randomized display sees the same reports after forgetting the tally. -/
theorem returnedJoint_display [∀ a, IsSubprobabilityKernel (J a)] (x : Resumption P X) (s : S)
    (display : Kernel (X × S) Y) :
    (J.returnedJoint x s).bind (fun z => display (z.1, z.2.1)) =
      (Resumption.returnedKernel J.marginal x s).bind display := by
  have proj : Measurable (fun z : X × (S × R) => (z.1, z.2.1)) := by fun_prop
  rw [← J.map_returnedKernel_accumulate x s 0,
    Measure.bind_map proj.aemeasurable display.aemeasurable]
  rfl

omit [MeasurableAdd₂ R] [∀ a, IsSFiniteKernel (J a)] in
/-- A randomized terminal display pulls its test back to the same completed-run bill. -/
theorem returnedBill_display (price : R →+ ℝ≥0∞) (hp : Measurable price)
    (x : Resumption P X) (s : S) (display : Kernel (X × S) Y)
    (g : Y → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ y, g y ∂((((J.returnedJoint x s).withDensity (fun z => price z.2.2)).map
      (fun z => (z.1, z.2.1))).bind display) =
      J.returnedBill price x (fun z => ∫⁻ y, g y ∂display z) s := by
  have proj : Measurable (fun z : X × (S × R) => (z.1, z.2.1)) := by fun_prop
  rw [Measure.lintegral_bind display.aemeasurable hg.aemeasurable,
    lintegral_map (hg.lintegral_kernel (κ := display)) proj]
  exact lintegral_withDensity_eq_lintegral_mul (J.returnedJoint x s) (f := fun z => price z.2.2)
    (g := fun z => ∫⁻ y, g y ∂display (z.1, z.2.1))
    (hp.comp (measurable_snd.comp measurable_snd)) ((hg.lintegral_kernel (κ := display)).comp proj)

section Subprobability

omit [∀ a, IsSFiniteKernel (J a)]
variable [∀ a, IsSubprobabilityKernel (J a)] (p : R →+ ℝ≥0∞) (hp : Measurable p)
  {c : P.A → S → ℝ≥0∞} (hc : J.IsCharge p c)
include hp hc

/-- The completed bill is bounded by incurred cost, including on divergent programs. -/
theorem returnedBill_le_expectedCharge (x : Resumption P X) (s : S) :
    J.returnedBill p x (fun _ => 1) s ≤ Resumption.expectedCharge J.marginal c x
      (fun _ _ => 0) s := by
  simpa only [returnedBill, mul_one] using J.lintegral_price_returnedJoint_le p hp hc x s

/-- Full return from the initial state suffices for equality of both bills. -/
theorem returnedBill_eq_expectedCharge (x : Resumption P X) (s : S)
    (h : Resumption.returnedKernel J.marginal x s Set.univ = 1) :
    J.returnedBill p x (fun _ => 1) s = Resumption.expectedCharge J.marginal c x
      (fun _ _ => 0) s := by
  simpa only [returnedBill, mul_one] using J.lintegral_price_returnedJoint_eq p hp hc x s h

end Subprobability

end PFunctor.MarkedKernelHandler
