/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Free.Measure.StatefulExpectedCharge
public import PolyFun.PFunctor.Free.Measure.Kernel.Transport
public import Mathlib.Probability.Kernel.Composition.ParallelComp
import ToCslib.MeasureTheory.Integral.Lebesgue.Subprobability
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Resource marks on returning operations

A marked operation reports its answer, private state, and resource use jointly. Sequential
composition adds the marks in execution order. A measurable additive price reads their value
on completed runs. A separate per-call charge also accounts for work on branches that abort.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

universe uA uB uS uR uX uY uQ

namespace PFunctor

/-- Laws of the answer, successor state and resource mark on return from an operation. -/
abbrev MarkedKernelHandler (P : PFunctor.{uA, uB}) (S : Type uS) (R : Type uR)
    [∀ a, MeasurableSpace (P.B a)] [MeasurableSpace S] [MeasurableSpace R] :=
  (a : P.A) → Kernel S (P.B a × (S × R))

namespace MarkedKernelHandler

variable {P : PFunctor.{uA, uB}} {S : Type uS} {R : Type uR} {X : Type uX}
  {Y : Type uY} [∀ a, MeasurableSpace (P.B a)] [MeasurableSpace S] [MeasurableSpace R]

/-- Add an incoming tally to the mark reported by an operation. -/
@[expose] def prepend [Add R] (r : R) (z : X × (S × R)) : X × (S × R) :=
  (z.1, z.2.1, r + z.2.2)

theorem measurable_prepend [MeasurableSpace X] [Add R] [MeasurableAdd₂ R] (r : R) :
    Measurable (prepend r : X × (S × R) → _) :=
  measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk
    (measurable_const.add (measurable_snd.comp measurable_snd)))

variable [AddMonoid R] [MeasurableAdd₂ R] (J : MarkedKernelHandler P S R)

/-- Lift an operation to a private state carrying its tally. For s-finite kernels and
measurable addition, `accumulate_apply` identifies its action on each state. -/
noncomputable def accumulate : KernelHandler P (S × R) :=
  fun a => (J a ∥ₖ (Kernel.id : Kernel R R)).map (fun p => prepend p.2 p.1)

theorem accumulate_apply [∀ a, IsSFiniteKernel (J a)] (a : P.A) (s : S) (r : R) :
    J.accumulate a (s, r) = (J a s).map (prepend r) := by
  have hm : Measurable fun p : (P.B a × (S × R)) × R => prepend p.2 p.1 := by
    unfold prepend
    fun_prop
  rw [accumulate, Kernel.map_apply _ hm, Kernel.parallelComp_apply, Kernel.id_apply,
    Measure.prod_dirac, Measure.map_map hm measurable_prodMk_right]
  rfl

instance (a : P.A) [∀ a, IsSubprobabilityKernel (J a)] :
    IsSubprobabilityKernel (J.accumulate a) := ⟨fun ⟨s, r⟩ => by
  rw [accumulate_apply, Measure.map_apply (measurable_prepend r) .univ, Set.preimage_univ]
  exact (J a).measure_univ_le s⟩

variable [∀ a, Countable (P.B a)] [∀ a, MeasurableSingletonClass (P.B a)]
  [MeasurableSpace X] [MeasurableSpace Y]

/-- Joint law of the result, final private state, and total resource on a completed run. -/
@[expose] noncomputable def joint (x : FreeM P X) : Kernel S (X × (S × R)) :=
  (FreeM.runKernel J.accumulate x).comap (fun s => (s, 0)) (measurable_id.prodMk measurable_const)

omit [MeasurableAdd₂ R] in
theorem joint_apply (x : FreeM P X) (s : S) :
    J.joint x s = FreeM.runKernel J.accumulate x (s, 0) := rfl

omit [MeasurableAdd₂ R] in
@[simp] theorem joint_pure (x : X) (s : S) :
    J.joint (pure x) s = Measure.dirac (x, s, 0) := FreeM.runKernel_pure _ _ _

variable [∀ a, IsSubprobabilityKernel (J a)]

instance (x : FreeM P X) : IsSubprobabilityKernel (J.joint x) := by
  unfold joint
  infer_instance

@[simp] theorem joint_lift (a : P.A) (s : S) : J.joint (FreeM.lift a) s = J a s := by
  rw [joint_apply, FreeM.runKernel_lift, accumulate_apply]
  have h : (prepend (0 : R) : P.B a × (S × R) → _) = id := by ext z <;> simp [prepend]
  rw [h, Measure.map_id]

/-- An incoming tally adds a fixed mark to the joint law of a fresh run. -/
theorem runKernel_accumulate (x : FreeM P X) (s : S) (r : R) :
    FreeM.runKernel J.accumulate x (s, r) = (J.joint x s).map (prepend r) := by
  have h := FreeM.map_runKernel_state J.accumulate J.accumulate
    (fun (t : S × R) => (t.1, r + t.2))
    (measurable_fst.prodMk (measurable_const.add measurable_snd)) (I := fun _ => True)
    (fun a ⟨t, v⟩ _ => by
      rw [accumulate_apply, accumulate_apply]
      change ((J a t).map (prepend v)).map (prepend r) = _
      rw [Measure.map_map (measurable_prepend r)
        (measurable_prepend v)]
      apply congrArg (fun f => (J a t).map f)
      funext z
      change (_, _, r + (v + z.2.2)) = (_, _, (r + v) + z.2.2)
      rw [add_assoc]
      rfl)
    (fun _ _ _ => Filter.Eventually.of_forall fun _ => True.intro) x (state := (s, 0)) True.intro
  rw [joint_apply]
  change _ = (FreeM.runKernel J.accumulate x (s, 0)).map (fun z => (z.1, z.2.1, r + z.2.2))
  simpa only [add_zero] using h.symm

/-- Sequencing retains the first mark and adds the continuation's mark to it. -/
theorem joint_bind [Countable X] [MeasurableSingletonClass X]
    (x : FreeM P X) (k : X → FreeM P Y) (s : S) :
    J.joint (x.bind k) s = (J.joint x s).bind (fun z =>
      (J.joint (k z.1) z.2.1).map (prepend z.2.2)) := by
  rw [joint_apply, FreeM.runKernel_bind, joint_apply]
  exact Measure.bind_congr_right (Filter.Eventually.of_forall fun z =>
    runKernel_accumulate J (k z.1) z.2.1 z.2.2)

/-- The answer and state law obtained by forgetting the mark. -/
noncomputable def marginal : KernelHandler P S :=
  fun a => (J a).map fun z => (z.1, z.2.1)

omit [AddMonoid R] [MeasurableAdd₂ R] [∀ a, IsSubprobabilityKernel (J a)]
    [∀ a, Countable (P.B a)] [∀ a, MeasurableSingletonClass (P.B a)] in
/-- The marginal takes the measurable projection to answers and successor states. -/
theorem marginal_apply (a : P.A) (s : S) :
    J.marginal a s = (J a s).map (fun z => (z.1, z.2.1)) :=
  Kernel.map_apply _ (by fun_prop) s

instance (a : P.A) : IsSubprobabilityKernel (J.marginal a) := by
  unfold marginal
  infer_instance

/-- Forgetting the final tally commutes with executing any adaptive program. -/
theorem map_joint (x : FreeM P X) (s : S) :
    (J.joint x s).map (fun z => (z.1, z.2.1)) = FreeM.runKernel J.marginal x s := by
  apply FreeM.map_runKernel_state J.accumulate J.marginal Prod.fst measurable_fst
    (I := fun _ => True) _ (fun _ _ _ => Filter.Eventually.of_forall fun _ => True.intro)
    x (state := (s, 0)) True.intro
  rintro a ⟨t, r⟩ _
  have hm : Measurable (fun z : P.B a × (S × R) => (z.1, z.2.1)) := by fun_prop
  rw [accumulate_apply, Measure.map_map hm (measurable_prepend r), marginal, Kernel.map_apply _ hm]
  rfl

/-- Weight the price on a completed run by an observation of its result and private state. -/
@[expose] noncomputable def bill (price : R →+ ℝ≥0∞) (x : FreeM P X) (f : X × S → ℝ≥0∞) (s : S) :
    ℝ≥0∞ :=
  ∫⁻ z, price z.2.2 * f (z.1, z.2.1) ∂J.joint x s

omit [MeasurableAdd₂ R] [∀ a, IsSubprobabilityKernel (J a)] in
/-- The bill reads the price and the terminal observation from the same returned execution. -/
theorem bill_apply (price : R →+ ℝ≥0∞) (x : FreeM P X) (f : X × S → ℝ≥0∞) (s : S) :
    J.bill price x f s = ∫⁻ z, price z.2.2 * f (z.1, z.2.1) ∂J.joint x s := rfl

/-- Expected cost incurred on all reached prefixes, with the indicated price for an opaque call. -/
@[expose] noncomputable def incurred (c : P.A → S → ℝ≥0∞) (x : FreeM P X) (s : S) : ℝ≥0∞ :=
  FreeM.wpFold (OpSpec.statefulExpectedCharge J.marginal c) x (fun _ _ => 0) s

omit [AddMonoid R] [MeasurableAdd₂ R] [∀ a, IsSubprobabilityKernel (J a)]
    [∀ a, Countable (P.B a)] [∀ a, MeasurableSingletonClass (P.B a)] [MeasurableSpace X] in
/-- The incurred reading uses the usual stateful expected-charge fold with zero terminal credit. -/
theorem incurred_apply (c : P.A → S → ℝ≥0∞) (x : FreeM P X) (s : S) :
    J.incurred c x s = FreeM.wpFold (OpSpec.statefulExpectedCharge J.marginal c) x
      (fun _ _ => 0) s := rfl

variable (price : R →+ ℝ≥0∞)

omit [AddMonoid R] [MeasurableAdd₂ R] in
private theorem measurable_observe {f : X × S → ℝ≥0∞} (hf : Measurable f) :
    Measurable (fun z : X × (S × R) => f (z.1, z.2.1)) :=
  hf.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))

omit [MeasurableAdd₂ R] in
private theorem measurable_priced {f : X × S → ℝ≥0∞} (hp : Measurable price) (hf : Measurable f) :
    Measurable (fun z : X × (S × R) => price z.2.2 * f (z.1, z.2.1)) :=
  (hp.comp (measurable_snd.comp measurable_snd)).mul (measurable_observe hf)

omit [MeasurableAdd₂ R] [∀ a, IsSubprobabilityKernel (J a)] in
/-- Integrating the completed bill after any randomized terminal display pulls the
observation back along its kernel. The display can depend on the result and final state. -/
theorem bill_display (hp : Measurable price) (x : FreeM P X) (s : S) (d : Kernel (X × S) Y)
    (g : Y → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ y, g y ∂((((J.joint x s).withDensity (fun z => price z.2.2)).map
      (fun z => (z.1, z.2.1))).bind d) =
      J.bill price x (fun z => ∫⁻ y, g y ∂d z) s := by
  have hproj : Measurable fun z : X × (S × R) => (z.1, z.2.1) := by fun_prop
  rw [Measure.lintegral_bind d.aemeasurable hg.aemeasurable,
    lintegral_map (hg.lintegral_kernel (κ := d)) hproj]
  exact lintegral_withDensity_eq_lintegral_mul (J.joint x s) (f := fun z => price z.2.2)
    (g := fun z => ∫⁻ y, g y ∂d (z.1, z.2.1))
    (hp.comp (measurable_snd.comp measurable_snd)) ((hg.lintegral_kernel (κ := d)).comp hproj)

/-- Sequencing weights the price of the first run by the continuation's returned observation.
Both terms integrate over the actual answer and private state reached by the first run. -/
theorem bill_bind [Countable X] [MeasurableSingletonClass X] (hp : Measurable price)
    (x : FreeM P X) (k : X → FreeM P Y) (f : Y × S → ℝ≥0∞) (hf : Measurable f) (s : S) :
    J.bill price (x.bind k) f s = ∫⁻ z,
      (price z.2.2 * ∫⁻ t, f (t.1, t.2.1) ∂J.joint (k z.1) z.2.1) +
        J.bill price (k z.1) f z.2.1 ∂J.joint x s := by
  rw [bill, joint_apply, FreeM.runKernel_bind,
    Measure.lintegral_bind (FreeM.measurable_runKernel_continuation _ k).aemeasurable
      (measurable_priced price hp hf).aemeasurable, joint_apply]
  apply lintegral_congr
  intro z
  rw [runKernel_accumulate, lintegral_map (measurable_priced price hp hf) (measurable_prepend _)]
  simp only [prepend, map_add, add_mul]
  have hm : Measurable (fun u : Y × (S × R) => price z.2.2 * f (u.1, u.2.1)) :=
    measurable_const.mul (measurable_observe hf)
  rw [lintegral_add_left hm, lintegral_const_mul _ (measurable_observe (R := R) hf)]
  rfl

omit [AddMonoid R] [MeasurableAdd₂ R] [MeasurableSpace Y] [∀ a, IsSubprobabilityKernel (J a)] in
/-- Incurring a charge survives failure of the continuation. -/
theorem incurred_bind [Countable X] [MeasurableSingletonClass X]
    (c : P.A → S → ℝ≥0∞) (hc : ∀ a, Measurable (c a))
    (x : FreeM P X) (k : X → FreeM P Y) (s : S) :
    J.incurred c (x.bind k) s = J.incurred c x s +
      ∫⁻ z, J.incurred c (k z.1) z.2 ∂FreeM.runKernel J.marginal x s := by
  rw [incurred, FreeM.wpFold_bind']
  exact FreeM.wpFold_statefulExpectedCharge_eq_add_lintegral J.marginal c x
    (post := fun z => J.incurred c (k z.1) z.2)
    (measurable_from_prod_countable_right fun b =>
      FreeM.measurable_wpFold_statefulExpectedCharge _ _ hc (k b) (fun _ => measurable_const)) s

omit [∀ a, Countable (P.B a)] [∀ a, MeasurableSingletonClass (P.B a)] in
/-- The one-call expected tally retains the old tally only in proportion to returned mass. -/
theorem lintegral_price_accumulate (hp : Measurable price) (a : P.A) (s : S) (r : R) :
    ∫⁻ z, price z.2.2 ∂J.accumulate a (s, r) =
      price r * J a s Set.univ + ∫⁻ z, price z.2.2 ∂J a s := by
  have hm : Measurable (fun z : P.B a × (S × R) => price z.2.2) :=
    hp.comp (measurable_snd.comp measurable_snd)
  rw [accumulate_apply, lintegral_map hm (measurable_prepend r)]
  simp only [prepend, map_add, lintegral_add_left measurable_const, lintegral_const]

omit [MeasurableSpace X] in
/-- Forgetting the tally commutes with incurring a state-dependent price at every call. -/
theorem wpFold_accumulate (c : P.A → S → ℝ≥0∞) (hc : ∀ a, Measurable (c a))
    (x : FreeM P X) (post : X → S → ℝ≥0∞) (hpost : ∀ v, Measurable (post v)) (s : S) (r : R) :
    FreeM.wpFold (OpSpec.statefulExpectedCharge J.accumulate (fun a t => c a t.1))
      x (fun v t => post v t.1) (s, r) = FreeM.wpFold (OpSpec.statefulExpectedCharge J.marginal c)
        x post s := by
  induction x using FreeM.rec generalizing s r with
  | pure => rfl
  | liftBind a k ih =>
    have hm : Measurable (fun z : P.B a × S =>
        FreeM.wpFold (OpSpec.statefulExpectedCharge J.marginal c) (k z.1) post z.2) :=
      measurable_from_prod_countable_right fun b =>
        FreeM.measurable_wpFold_statefulExpectedCharge _ _ hc (k b) hpost
    have hproj : Measurable (fun z : P.B a × (S × R) => (z.1, z.2.1)) := by fun_prop
    rw [FreeM.wpFold_liftBind, FreeM.wpFold_liftBind]
    simp only [OpSpec.statefulExpectedCharge_apply, ih]
    rw [accumulate_apply, lintegral_map (measurable_observe hm) (measurable_prepend r),
      marginal, Kernel.map_apply _ hproj]
    change _ = _ + ∫⁻ z : P.B a × S,
      FreeM.wpFold (OpSpec.statefulExpectedCharge J.marginal c) (k z.1) post z.2 ∂(J a s).map _
    rw [lintegral_map hm hproj]
    rfl

/-- Local accounting for a price on resource marks. Returned bills are covered by the
incurred charge. At a state where an operation returns almost surely, they agree. -/
structure IsCharge (c : P.A → S → ℝ≥0∞) : Prop where
  /-- The expected charge is measurable in the state at invocation. -/
  measurable : ∀ a, Measurable (c a)
  /-- Charges on returning paths are included in the incurred charge. -/
  returned_le : ∀ a s, ∫⁻ z, price z.2.2 ∂J a s ≤ c a s
  /-- A lossless call records all its incurred charge. -/
  eq_of_mass_one : ∀ a s, J a s Set.univ = 1 → ∫⁻ z, price z.2.2 ∂J a s = c a s

/-- The mass of a query followed by an adaptive continuation. -/
theorem joint_liftBind_univ (a : P.A) (k : P.B a → FreeM P X) (s : S) :
    J.joint (.liftBind a k) s Set.univ =
      ∫⁻ z, J.joint (k z.1) z.2.1 Set.univ ∂J a s := by
  rw [joint_apply, FreeM.runKernel_liftBind, Measure.bind_apply .univ
    (FreeM.measurable_runKernel_continuation _ k).aemeasurable, accumulate_apply]
  have h : Measurable (fun z : P.B a × (S × R) =>
      FreeM.runKernel J.accumulate (k z.1) z.2 Set.univ) :=
    (Measure.measurable_coe .univ).comp (FreeM.measurable_runKernel_continuation _ k)
  rw [lintegral_map h (measurable_prepend 0)]
  apply lintegral_congr
  intro z
  rw [runKernel_accumulate, Measure.map_apply (measurable_prepend _) .univ, Set.preimage_univ]
  rfl

/-- The completed bill of a query and its continuation, including the price paid on that query. -/
theorem bill_liftBind_one (hp : Measurable price) (a : P.A) (k : P.B a → FreeM P X) (s : S) :
    J.bill price (.liftBind a k) (fun _ => 1) s =
      ∫⁻ z, price z.2.2 * J.joint (k z.1) z.2.1 Set.univ +
        J.bill price (k z.1) (fun _ => 1) z.2.1 ∂J a s := by
  simpa only [FreeM.liftBind_eq, joint_lift, lintegral_one] using
    (bill_bind J price hp (FreeM.lift a) k (fun _ => 1) measurable_const s)

omit [AddMonoid R] [MeasurableAdd₂ R] [∀ a, IsSubprobabilityKernel (J a)] [MeasurableSpace X] in
/-- The charge of invoking a call and continuing from its actual answer and state. -/
theorem incurred_liftBind (c : P.A → S → ℝ≥0∞) (hc : ∀ a, Measurable (c a))
    (a : P.A) (k : P.B a → FreeM P X) (s : S) :
    J.incurred c (.liftBind a k) s =
      c a s + ∫⁻ z, J.incurred c (k z.1) z.2.1 ∂J a s := by
  have hm : Measurable (fun z : P.B a × S => J.incurred c (k z.1) z.2) :=
    measurable_from_prod_countable_right fun b =>
      FreeM.measurable_wpFold_statefulExpectedCharge _ _ hc (k b) (fun _ => measurable_const)
  have hproj : Measurable (fun z : P.B a × (S × R) => (z.1, z.2.1)) := by fun_prop
  rw [incurred, FreeM.wpFold_liftBind, OpSpec.statefulExpectedCharge_apply,
    marginal, Kernel.map_apply _ hproj]
  change c a s + ∫⁻ z, J.incurred c (k z.1) z.2 ∂(J a s).map (fun z => (z.1, z.2.1)) = _
  rw [lintegral_map hm hproj]

/-- On all finite programs, incurred charge covers the bill on completed runs. -/
theorem bill_le_incurred (hp : Measurable price) {c : P.A → S → ℝ≥0∞}
    (hc : J.IsCharge price c) (x : FreeM P X) (s : S) :
    J.bill price x (fun _ => 1) s ≤ J.incurred c x s := by
  induction x using FreeM.rec generalizing s with
  | pure v =>
    change J.bill price (pure v) (fun _ => 1) s ≤ _
    rw [bill, joint_pure, lintegral_dirac' _ (measurable_priced price hp measurable_const)]
    simp
  | liftBind a k ih =>
    rw [bill_liftBind_one J price hp, incurred_liftBind J c hc.measurable]
    have hprice : Measurable (fun z : P.B a × (S × R) => price z.2.2) :=
      hp.comp (measurable_snd.comp measurable_snd)
    calc
      _ ≤ ∫⁻ z, price z.2.2 + J.incurred c (k z.1) z.2.1 ∂J a s :=
        lintegral_mono fun z => add_le_add (mul_le_of_le_one_right' <|
          (J.joint (k z.1)).measure_univ_le z.2.1) (ih z.1 z.2.1)
      _ ≤ _ := by
        rw [lintegral_add_left hprice]
        exact add_le_add_left (hc.returned_le a s) _

/-- Full return mass at the specified initial state makes its completed bill exact. -/
theorem bill_eq_incurred_of_mass_one (hp : Measurable price) {c : P.A → S → ℝ≥0∞}
    (hc : J.IsCharge price c) (x : FreeM P X) (s : S) (h : J.joint x s Set.univ = 1) :
    J.bill price x (fun _ => 1) s = J.incurred c x s := by
  induction x using FreeM.rec generalizing s with
  | pure v =>
    change J.bill price (pure v) (fun _ => 1) s = _
    rw [bill, joint_pure, lintegral_dirac' _ (measurable_priced price hp measurable_const)]
    simp [incurred]
  | liftBind a k ih =>
    rw [joint_liftBind_univ] at h
    obtain ⟨hm, hnext⟩ := measure_univ_eq_one_and_ae_eq_one_of_lintegral_eq_one
      (fun z : P.B a × (S × R) => (J.joint (k z.1)).measure_univ_le z.2.1) h
    rw [bill_liftBind_one J price hp, incurred_liftBind J c hc.measurable]
    have hprice : Measurable (fun z : P.B a × (S × R) => price z.2.2) :=
      hp.comp (measurable_snd.comp measurable_snd)
    calc
      _ = ∫⁻ z, price z.2.2 + J.incurred c (k z.1) z.2.1 ∂J a s :=
        lintegral_congr_ae (hnext.mono fun z hz => by rw [hz, mul_one, ih z.1 z.2.1 hz])
      _ = _ := by rw [lintegral_add_left hprice, hc.eq_of_mass_one a s hm]

section Tally

omit [∀ a, Countable (P.B a)] [∀ a, MeasurableSingletonClass (P.B a)]

/-- A nonnegative price of an additive tally is nondecreasing along each returned step. -/
theorem ae_price_le_accumulate (hp : Measurable price) (a : P.A) (t : S × R) :
    ∀ᵐ z ∂J.accumulate a t, price t.2 ≤ price z.2.2 := by
  obtain ⟨s, r⟩ := t
  rw [accumulate_apply]
  apply (ae_map_iff (measurable_prepend r).aemeasurable
    (p := fun z : P.B a × (S × R) => price r ≤ price z.2.2)
    (measurableSet_le measurable_const (hp.comp (measurable_snd.comp measurable_snd)))).mpr
  exact Filter.Eventually.of_forall fun z => by simp [prepend]

/-- The expected tally after a call is bounded by its initial value plus the incurred charge. -/
theorem IsCharge.accumulate_le {c : P.A → S → ℝ≥0∞} (h : J.IsCharge price c)
    (hp : Measurable price) (a : P.A) (t : S × R) :
    ∫⁻ z, price z.2.2 ∂J.accumulate a t ≤ c a t.1 + price t.2 := by
  obtain ⟨s, r⟩ := t
  rw [lintegral_price_accumulate J price hp, add_comm]
  exact add_le_add (h.returned_le a s) (mul_le_of_le_one_right' <| (J a).measure_univ_le s)

/-- A lossless marked step pays its whole incurred charge into the tally. -/
theorem IsCharge.accumulate_eq_of_mass_one {c : P.A → S → ℝ≥0∞} (h : J.IsCharge price c)
    (hp : Measurable price) (a : P.A) (t : S × R) (hm : J.accumulate a t Set.univ = 1) :
    ∫⁻ z, price z.2.2 ∂J.accumulate a t = c a t.1 + price t.2 := by
  obtain ⟨s, r⟩ := t
  rw [accumulate_apply, Measure.map_apply (measurable_prepend r) .univ, Set.preimage_univ] at hm
  rw [lintegral_price_accumulate J price hp, hm, mul_one, h.eq_of_mass_one a s hm, add_comm]

end Tally
section Substitution

variable {Q : PFunctor.{uQ, uB}} [∀ a, MeasurableSpace (Q.B a)]
  [∀ a, Countable (Q.B a)] [∀ a, MeasurableSingletonClass (Q.B a)]
  (handler : (a : Q.A) → FreeM P (Q.B a))

/-- Interpret each source operation by the joint law of its implementing program. -/
@[expose] noncomputable def comap : MarkedKernelHandler Q S R :=
  fun a => J.joint (handler a)

instance (a : Q.A) : IsSubprobabilityKernel (J.comap handler a) :=
  inferInstanceAs (IsSubprobabilityKernel (J.joint (handler a)))

omit [∀ a, Countable (Q.B a)] [∀ a, MeasurableSingletonClass (Q.B a)] in
/-- A certified charge for an opaque call can be constructed from its implementation. -/
theorem IsCharge.comap (hp : Measurable price) {c : P.A → S → ℝ≥0∞} (hc : J.IsCharge price c) :
    (J.comap handler).IsCharge price (fun a => J.incurred c (handler a)) where
  measurable a := FreeM.measurable_wpFold_statefulExpectedCharge _ _ hc.measurable (handler a)
    (fun _ => measurable_const)
  returned_le a s := by
    simpa only [bill, mul_one, MarkedKernelHandler.comap] using
      J.bill_le_incurred price hp hc (handler a) s
  eq_of_mass_one a s h := by
    simpa only [bill, mul_one, MarkedKernelHandler.comap] using
      J.bill_eq_incurred_of_mass_one price hp hc (handler a) s h

variable {A : Type uB}

/-- Inlining a handler threads the private state and preserves its joint marks. -/
theorem joint_liftM [MeasurableSpace A] (x : FreeM Q A) (s : S) :
    J.joint (x.liftM handler) s = (J.comap handler).joint x s := by
  rw [joint_apply, FreeM.runKernel_liftM, joint_apply]
  congr 2
  funext a
  apply Kernel.ext
  rintro ⟨t, r⟩
  rw [runKernel_accumulate, accumulate_apply]
  rfl

/-- Inlining incurs exactly the charge of each implementing program. -/
theorem incurred_liftM (c : P.A → S → ℝ≥0∞) (hc : ∀ a, Measurable (c a))
    (x : FreeM Q A) (s : S) :
    J.incurred c (x.liftM handler) s = (J.comap handler).incurred
      (fun a => J.incurred c (handler a)) x s := by
  induction x using FreeM.rec generalizing s with
  | pure => rfl
  | liftBind a k ih =>
    change J.incurred c ((handler a).bind (fun b => (k b).liftM handler)) s = _
    rw [incurred_bind J c hc, incurred_liftBind (J.comap handler)
      (fun b => J.incurred c (handler b))
      (fun b => FreeM.measurable_wpFold_statefulExpectedCharge _ _ hc (handler b)
        (fun _ => measurable_const)), ← map_joint J (handler a) s]
    have hm : Measurable (fun z : Q.B a × S => J.incurred c ((k z.1).liftM handler) z.2) :=
      measurable_from_prod_countable_right fun b => FreeM.measurable_wpFold_statefulExpectedCharge
        _ _ hc ((k b).liftM handler) (fun _ => measurable_const)
    have proj : Measurable (fun z : Q.B a × (S × R) => (z.1, z.2.1)) := by fun_prop
    rw [lintegral_map hm proj]
    simp only [ih, comap]

end Substitution

end MarkedKernelHandler

namespace KernelHandler

variable {P : PFunctor.{uA, uB}} {S : Type uS} {R : Type uR}
  [∀ a, MeasurableSpace (P.B a)] [MeasurableSpace S] [MeasurableSpace R]
  (K : KernelHandler P S) (mark : P.A → S → R) (hm : ∀ a, Measurable (mark a))

/-- Record the declared resource mark of an invocation alongside its answer and private state. -/
noncomputable def withStateMark : MarkedKernelHandler P S R :=
  fun a => (K a ×ₖ Kernel.deterministic (mark a) (hm a)).map
    (fun z => (z.1.1, z.1.2, z.2))

variable [∀ a, IsSubprobabilityKernel (K a)]

instance (a : P.A) : IsSubprobabilityKernel (withStateMark K mark hm a) := by
  unfold withStateMark
  infer_instance

/-- Returning from a call retains the mark assigned at invocation. -/
theorem withStateMark_apply (a : P.A) (s : S) :
    withStateMark K mark hm a s = (K a s).map (fun z => (z.1, z.2, mark a s)) := by
  have h : Measurable (fun z : (P.B a × S) × R => (z.1.1, z.1.2, z.2)) := by fun_prop
  rw [withStateMark, Kernel.map_apply _ h, Kernel.prod_apply, Kernel.deterministic_apply,
    Measure.prod_dirac, Measure.map_map h measurable_prodMk_right]
  rfl

/-- Forgetting a declared mark gives the original operation kernel. -/
@[simp] theorem marginal_withStateMark :
    (withStateMark K mark hm).marginal = K := by
  funext a
  apply Kernel.ext
  intro s
  have put : Measurable (fun z : P.B a × S => (z.1, z.2, mark a s)) := by fun_prop
  have get : Measurable (fun z : P.B a × (S × R) => (z.1, z.2.1)) := by fun_prop
  rw [MarkedKernelHandler.marginal, Kernel.map_apply _ get, withStateMark_apply,
    Measure.map_map get put]
  exact Measure.map_id

include hm in
/-- Pricing a declared mark gives a certified incurred charge, also when a call loses mass. -/
theorem isCharge_withStateMark [AddMonoid R] (price : R →+ ℝ≥0∞) (hp : Measurable price) :
    (withStateMark K mark hm).IsCharge price (fun a s => price (mark a s)) := by
  have hprice (a : P.A) : Measurable (fun z : P.B a × (S × R) => price z.2.2) :=
    hp.comp (measurable_snd.comp measurable_snd)
  have put (a : P.A) (s : S) : Measurable (fun z : P.B a × S => (z.1, z.2, mark a s)) := by
    fun_prop
  have bill (a : P.A) (s : S) : ∫⁻ z, price z.2.2 ∂(withStateMark K mark hm a s) =
      price (mark a s) * K a s Set.univ := by
    rw [withStateMark_apply, lintegral_map (hprice a) (put a s)]
    exact lintegral_const (μ := K a s) (price (mark a s))
  refine ⟨fun a => hp.comp (hm a), fun a s => ?_, fun a s h => ?_⟩
  · rw [bill]
    exact mul_le_of_le_one_right' ((K a).measure_univ_le s)
  · rw [withStateMark_apply, Measure.map_apply (put a s) .univ, Set.preimage_univ] at h
    rw [bill, h, mul_one]

end KernelHandler
end PFunctor
