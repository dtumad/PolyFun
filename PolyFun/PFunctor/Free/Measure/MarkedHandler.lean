/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Free.Measure.MarkedResource

/-!
# Marked costs through private-state handlers

A handler chooses an implementation from its own state and threads that state through later
calls. Interpreting the implementation's marked law and incurred charge at each incoming
state suffices to transfer both readings through every adaptive client.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PFunctor

universe uA uB uQ uC uT uU uS uR

namespace Handler.Stateful

variable {P : PFunctor.{uA, uB}} {Q : PFunctor.{uQ, uC}} {T : Type uC}
  [∀ a, MeasurableSpace (P.B a)] [∀ a, Countable (P.B a)] [∀ a, MeasurableSingletonClass (P.B a)]
  [∀ a, MeasurableSpace (Q.B a)] [∀ a, Countable (Q.B a)] [∀ a, MeasurableSingletonClass (Q.B a)]
  [MeasurableSpace T] (h : Stateful (FreeM P) T Q)

/-- Exact substitution for expected charge and terminal credit. A measurable state map packs
the handler's private state together with the state of its implementation kernel. -/
theorem wpFold_run_kernel {S : Type uS} {U : Type uU} [MeasurableSpace S] [MeasurableSpace U]
    (K : KernelHandler P S) (c : P.A → S → ℝ≥0∞) (L : KernelHandler Q U)
    (d : Q.A → U → ℝ≥0∞) (hd : ∀ a, Measurable (d a)) (pack : T × S → U) (hp : Measurable pack)
    (hlaw : ∀ a t s, (FreeM.runKernel K ((h a).run t) s).map
      (fun z => (z.1.1, pack (z.1.2, z.2))) = L a (pack (t, s)))
    (hcharge : ∀ a t s, FreeM.wpFold (OpSpec.statefulExpectedCharge K c) ((h a).run t)
      (fun _ _ => 0) s = d a (pack (t, s)))
    {X : Type uC} (x : FreeM Q X) (post : X → U → ℝ≥0∞) (hpost : ∀ v, Measurable (post v))
    (t : T) (s : S) :
    FreeM.wpFold (OpSpec.statefulExpectedCharge K c) (h.run x t)
      (fun p s' => post p.1 (pack (p.2, s'))) s =
      FreeM.wpFold (OpSpec.statefulExpectedCharge L d) x post (pack (t, s)) := by
  induction x using FreeM.rec generalizing t s with
  | pure v => rfl
  | liftBind a k ih =>
    rw [run_liftBind, FreeM.wpFold_bind, FreeM.wpFold_liftBind, OpSpec.statefulExpectedCharge_apply]
    let proj (z : (Q.B a × T) × S) := (z.1.1, pack (z.1.2, z.2))
    have hproj : Measurable proj := by dsimp [proj]; fun_prop
    let next (z : Q.B a × U) := FreeM.wpFold (OpSpec.statefulExpectedCharge L d) (k z.1) post z.2
    have hn : Measurable next := measurable_from_prod_countable_right fun b =>
      FreeM.measurable_wpFold_statefulExpectedCharge L d hd (k b) hpost
    have eq (v : Q.B a × T) : FreeM.wpFold (OpSpec.statefulExpectedCharge K c)
        (h.run (k v.1) v.2) (fun p s' => post p.1 (pack (p.2, s'))) =
        fun s' => next (proj (v, s')) := funext (ih v.1 v.2)
    simp only [eq]
    rw [← hlaw a t s, lintegral_map hn hproj, ← hcharge a t s]
    exact FreeM.wpFold_statefulExpectedCharge_eq_add_lintegral K c ((h a).run t)
      (post := fun z => next (proj z)) (hn.comp hproj) s

omit [∀ a, Countable (P.B a)] [∀ a, MeasurableSingletonClass (P.B a)] in
private theorem fold_zero {S : Type*} [MeasurableSpace S] {K : KernelHandler P S}
    {A : Type*} (x : FreeM P A) :
    FreeM.wpFold (OpSpec.statefulExpectedCharge K 0) x (fun _ _ => 0) = 0 := by
  induction x using FreeM.rec with
  | pure => rfl
  | liftBind a k ih =>
    funext s
    rw [FreeM.wpFold_liftBind, OpSpec.statefulExpectedCharge_apply]
    simp [ih]

private theorem fold_zero_eq_integral {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]
    (K : KernelHandler P S) (x : FreeM P A) (f : A × S → ℝ≥0∞) (hf : Measurable f) (s : S) :
    FreeM.wpFold (OpSpec.statefulExpectedCharge K 0) x (fun v t => f (v, t)) s =
      ∫⁻ z, f z ∂FreeM.runKernel K x s := by
  simpa only [fold_zero, Pi.zero_apply, zero_add] using
    FreeM.wpFold_statefulExpectedCharge_eq_add_lintegral K 0 x hf s

/-- Local agreement on the joint kernel transfers to every client even when selecting a
continuation from the handler's private state requires joint measurability. -/
theorem runKernel_run_kernel {S U : Type*} [MeasurableSpace S] [MeasurableSpace U]
    (K : KernelHandler P S) (L : KernelHandler Q U) (pack : T × S → U) (hp : Measurable pack)
    (hlaw : ∀ a t s, (FreeM.runKernel K ((h a).run t) s).map
      (fun z => (z.1.1, pack (z.1.2, z.2))) = L a (pack (t, s)))
    {X : Type uC} [MeasurableSpace X] (x : FreeM Q X) (t : T) (s : S) :
    (FreeM.runKernel K (h.run x t) s).map (fun z => (z.1.1, pack (z.1.2, z.2))) =
      FreeM.runKernel L x (pack (t, s)) := by
  apply Measure.ext_of_lintegral
  intro f hf
  have hproj : Measurable (fun z : (X × T) × S => (z.1.1, pack (z.1.2, z.2))) := by fun_prop
  rw [lintegral_map hf hproj, ← fold_zero_eq_integral K (h.run x t)
    (fun z => f (z.1.1, pack (z.1.2, z.2))) (hf.comp hproj), ← fold_zero_eq_integral L x f hf]
  exact h.wpFold_run_kernel K 0 L 0 (fun _ => measurable_const) pack hp hlaw
    (fun a t s => congrFun (fold_zero ((h a).run t)) s) x (fun v u => f (v, u))
    (fun _ => hf.comp (measurable_const.prodMk measurable_id)) t s

end Handler.Stateful

namespace MarkedKernelHandler

variable {P : PFunctor.{uA, uB}} {Q : PFunctor.{uQ, uC}} {S : Type uS} {R : Type uR}
  {T : Type uC} [∀ a, MeasurableSpace (P.B a)] [∀ a, Countable (P.B a)]
  [∀ a, MeasurableSingletonClass (P.B a)] [∀ a, MeasurableSpace (Q.B a)]
  [MeasurableSpace T] [MeasurableSpace S] [MeasurableSpace R] [AddMonoid R]
  [MeasurableAdd₂ R] (J : MarkedKernelHandler P S R) [∀ a, IsSubprobabilityKernel (J a)]
  (h : Handler.Stateful (FreeM P) T Q)

/-- Move the handler's returned private state next to the state of the kernel executing it. -/
@[expose] def threadMark {X T S R : Type*} (z : (X × T) × (S × R)) : X × ((T × S) × R) :=
  (z.1.1, (z.1.2, z.2.1), z.2.2)

theorem measurable_threadMark {X T S R : Type*} [MeasurableSpace X] [MeasurableSpace T]
    [MeasurableSpace S] [MeasurableSpace R] : Measurable (@threadMark X T S R) := by
  unfold threadMark
  fun_prop

variable (hj : ∀ a, Measurable (fun p : T × S => J.joint ((h a).run p.1) p.2))

/-- Each operation runs its implementing program from the current handler state and kernel state.
The measurability premise allows arbitrary private state spaces. -/
noncomputable def comapStateful : MarkedKernelHandler Q (T × S) R :=
  fun a => ⟨fun p => (J.joint ((h a).run p.1) p.2).map threadMark,
    (Measure.measurable_map _ measurable_threadMark).comp (hj a)⟩

omit [MeasurableAdd₂ R] [∀ a, IsSubprobabilityKernel (J a)] in
theorem comapStateful_apply (a : Q.A) (t : T) (s : S) : J.comapStateful h hj a (t, s) =
    (J.joint ((h a).run t) s).map threadMark := by rw [comapStateful]; rfl

instance (a : Q.A) : IsSubprobabilityKernel (J.comapStateful h hj a) := ⟨fun ⟨t, s⟩ => by
  rw [comapStateful_apply, Measure.map_apply measurable_threadMark .univ, Set.preimage_univ]
  exact (J.joint ((h a).run t)).measure_univ_le s⟩

variable [∀ a, Countable (Q.B a)] [∀ a, MeasurableSingletonClass (Q.B a)]
  {X : Type uC}

omit [∀ a, Countable (Q.B a)] [∀ a, MeasurableSingletonClass (Q.B a)] in
/-- The exact incurred charge of a private-state implementation certifies its joint marked law. -/
theorem IsCharge.comapStateful (price : R →+ ℝ≥0∞) (hp : Measurable price)
    {c : P.A → S → ℝ≥0∞} (hc : J.IsCharge price c)
    (hm : ∀ a, Measurable fun u : T × S => J.incurred c ((h a).run u.1) u.2) :
    (J.comapStateful h hj).IsCharge price (fun a u => J.incurred c ((h a).run u.1) u.2) := by
  have bill (a : Q.A) (t : T) (s : S) :
      ∫⁻ z, price z.2.2 ∂J.comapStateful h hj a (t, s) =
        J.bill price ((h a).run t) (fun _ => 1) s := by
    have hprice : Measurable (fun z : Q.B a × ((T × S) × R) => price z.2.2) :=
      hp.comp (measurable_snd.comp measurable_snd)
    rw [comapStateful_apply, lintegral_map hprice measurable_threadMark, bill_apply]
    simp only [threadMark, mul_one]
  refine ⟨hm, fun a ⟨t, s⟩ => ?_, fun a ⟨t, s⟩ hmass => ?_⟩
  · rw [bill]
    exact J.bill_le_incurred price hp hc ((h a).run t) s
  · rw [comapStateful_apply, Measure.map_apply measurable_threadMark .univ, Set.preimage_univ]
      at hmass
    rw [bill]
    exact J.bill_eq_incurred_of_mass_one price hp hc ((h a).run t) s hmass

/-- The bill for implementing each call suffices to compute the exact incurred charge of the
client, including marks paid before a subsequent call aborts. -/
theorem incurred_run (c : P.A → S → ℝ≥0∞)
    (hc : ∀ a, Measurable fun u : T × S => J.incurred c ((h a).run u.1) u.2)
    (x : FreeM Q X) (t : T) (s : S) :
    J.incurred c (h.run x t) s = (J.comapStateful h hj).incurred
      (fun a u => J.incurred c ((h a).run u.1) u.2) x (t, s) := by
  apply h.wpFold_run_kernel J.marginal c (J.comapStateful h hj).marginal _ hc id measurable_id
    _ (fun _ _ _ => rfl) x (fun _ _ => 0) (fun _ => measurable_const) t s
  intro a v w
  rw [← J.map_joint ((h a).run v) w, marginal_apply, comapStateful_apply]
  have hproj : Measurable (fun z : (Q.B a × T) × (S × R) => (z.1, z.2.1)) := by fun_prop
  have hpack : Measurable (fun z : (Q.B a × T) × S => (z.1.1, id (z.1.2, z.2))) := by fun_prop
  have hdrop : Measurable (fun z : Q.B a × ((T × S) × R) => (z.1, z.2.1)) := by fun_prop
  rw [Measure.map_map hpack hproj, Measure.map_map hdrop measurable_threadMark]
  rfl

/-- Threading the handler state through a marked program retains the same result, both
private states, and total resource. This equality preserves every measurable terminal bill. -/
theorem joint_run [MeasurableSpace X] (x : FreeM Q X) (t : T) (s : S) :
    (J.joint (h.run x t) s).map threadMark = (J.comapStateful h hj).joint x (t, s) := by
  rw [joint_apply, joint_apply]
  let pack (z : T × (S × R)) := ((z.1, z.2.1), z.2.2)
  have hpack : Measurable pack := by unfold pack; fun_prop
  apply h.runKernel_run_kernel J.accumulate (J.comapStateful h hj).accumulate pack hpack
    _ x t (s, 0)
  rintro a v ⟨w, r⟩
  rw [J.runKernel_accumulate, (J.comapStateful h hj).accumulate_apply a (v, w) r,
    comapStateful_apply]
  have he : Measurable (fun z : (Q.B a × T) × (S × R) => (z.1.1, pack (z.1.2, z.2))) := by
    fun_prop
  rw [Measure.map_map he (measurable_prepend r),
    Measure.map_map (measurable_prepend r) measurable_threadMark]
  rfl

end MarkedKernelHandler
end PFunctor
