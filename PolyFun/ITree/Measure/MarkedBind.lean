/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.ITree.Measure.MarkedResource
import all PolyFun.ITree.Measure
import PolyFun.PFunctor.Resumption.Measure.MarkedBind

/-!
# Marked sequencing on interaction trees

A silent step contributes the empty mark and preserves private state. This identifies the
marked return law with the resumption interpretation and carries its sequential bill law
over to interaction trees, including trees that take infinitely many silent steps.
-/

public section

open MeasureTheory ProbabilityTheory PFunctor PFunctor.MarkedKernelHandler
open scoped ENNReal

namespace ITree

universe u v

variable {P : PFunctor.{u, v}} {S M X Y : Type*} [MeasurableSpace S] [MeasurableSpace M]
  [∀ a, MeasurableSpace (P.B a)] [∀ a, Countable (P.B a)]
  [∀ a, MeasurableSingletonClass (P.B a)] [AddMonoid M] [MeasurableAdd₂ M]
  (J : MarkedKernelHandler P S M) [MeasurableSpace X] [MeasurableSpace Y]

/-- Returned values, private states and resource tallies of an interaction tree. -/
noncomputable def returnedJoint (x : ITree P X) : Kernel S (X × (S × M)) :=
  (returnedKernel J.accumulate x).comap (fun s => (s, 0)) (measurable_id.prodMk measurable_const)

omit [MeasurableAdd₂ M] in
/-- Each joint run starts with the empty tally. -/
theorem returnedJoint_apply (x : ITree P X) (s : S) :
    returnedJoint J x s = returnedKernel J.accumulate x (s, 0) := by
  rw [returnedJoint, Kernel.comap_apply]

/-- Expected resource price weighted by a terminal observation. -/
@[expose] noncomputable def returnedBill (p : M →+ ℝ≥0∞) (x : ITree P X) (f : X × S → ℝ≥0∞)
    (s : S) : ℝ≥0∞ :=
  ∫⁻ z, p z.2.2 * f (z.1, z.2.1) ∂returnedJoint J x s

omit [MeasurableAdd₂ M] in
/-- The completed bill uses every returned mark when the terminal observation is one. -/
theorem returnedBill_one (p : M →+ ℝ≥0∞) (x : ITree P X) (s : S) :
    returnedBill J p x (fun _ => 1) s = ∫⁻ z, p z.2.2 ∂returnedKernel J.accumulate x (s, 0) := by
  simp only [returnedBill, returnedJoint_apply, mul_one]

attribute [local instance] withTauMeasurableSpace withTauCountable withTauMeasurableSingletonClass

private noncomputable def withTauMark : MarkedKernelHandler (P + PFunctor.y.{u, v}) S M
  | .inl a => J a
  | .inr _ => Kernel.deterministic (fun s => (PUnit.unit, s, 0))
    (measurable_const.prodMk (measurable_id.prodMk measurable_const))

variable [∀ a, IsSFiniteKernel (J a)]

private instance (a : (P + PFunctor.y.{u, v}).A) : IsSFiniteKernel (withTauMark J a) := by
  cases a with
  | inl a => exact inferInstanceAs (IsSFiniteKernel (J a))
  | inr u => unfold withTauMark; infer_instance

omit [∀ a, Countable (P.B a)] [∀ a, MeasurableSingletonClass (P.B a)] in
private theorem accumulate_withTauMark :
    (withTauMark J).accumulate = withTauKernel J.accumulate := by
  funext a
  apply Kernel.ext
  rintro ⟨s, m⟩
  cases a with
  | inl a =>
    rw [accumulate_apply]
    exact (J.accumulate_apply a s m).symm
  | inr u =>
    rw [accumulate_apply]
    change (Measure.dirac (PUnit.unit, s, (0 : M))).map (prepend m) = Measure.dirac _
    rw [Measure.map_dirac' (measurable_prepend m)]
    simp [prepend]

private theorem returnedJoint_tau (x : ITree P X) :
    (withTauMark J).returnedJoint x.toResumptionWithTau = returnedJoint J x := by
  rw [MarkedKernelHandler.returnedJoint, accumulate_withTauMark]
  rfl

/-- Sequential execution retains both resource marks in their execution order. -/
theorem returnedJoint_bind (x : ITree P X) (k : X → ITree P Y)
    (hk : Measurable fun z : X × (S × M) => returnedKernel J.accumulate (k z.1) z.2) (s : S) :
    returnedJoint J (bind x k) s = (returnedJoint J x s).bind (fun z =>
      (returnedJoint J (k z.1) z.2.1).map (prepend z.2.2)) := by
  simp only [← returnedJoint_tau, toResumptionWithTau_bind]
  apply MarkedKernelHandler.returnedJoint_bind
  rwa [accumulate_withTauMark]

/-- The first stage's price is weighted by the continuation's observed return from its
actual answer and private state. -/
theorem returnedBill_bind (p : M →+ ℝ≥0∞) (hp : Measurable p) (x : ITree P X) (k : X → ITree P Y)
    (hk : Measurable fun z : X × (S × M) => returnedKernel J.accumulate (k z.1) z.2)
    (f : Y × S → ℝ≥0∞) (hf : Measurable f) (s : S) :
    returnedBill J p (bind x k) f s = ∫⁻ z,
      (p z.2.2 * ∫⁻ t, f (t.1, t.2.1) ∂returnedJoint J (k z.1) z.2.1) +
        returnedBill J p (k z.1) f z.2.1 ∂returnedJoint J x s := by
  simp only [returnedBill, ← returnedJoint_tau, toResumptionWithTau_bind]
  apply MarkedKernelHandler.returnedBill_bind _ _ hp _ _ _ _ hf
  rwa [accumulate_withTauMark]

section Subprobability

omit [∀ a, IsSFiniteKernel (J a)]
variable [∀ a, IsSubprobabilityKernel (J a)] (p : M →+ ℝ≥0∞) (hp : Measurable p)
  {c : P.A → S → ℝ≥0∞} (hc : J.IsCharge p c)
include hp hc

/-- The bill on completed runs is bounded by all incurred work. -/
theorem returnedBill_le_expectedCharge (x : ITree P X) (s : S) :
    returnedBill J p x (fun _ => 1) s ≤ expectedCharge J.marginal c hc.measurable x
      (fun _ => ⊥) s := by
  rw [returnedBill_one]
  exact lintegral_price_accumulate_le J p hp hc x s

/-- The completed bill accounts for all work at an initial state of almost-sure return. -/
theorem returnedBill_eq_expectedCharge (x : ITree P X) (s : S)
    (h : returnedKernel J.marginal x s Set.univ = 1) :
    returnedBill J p x (fun _ => 1) s = expectedCharge J.marginal c hc.measurable x
      (fun _ => ⊥) s := by
  rw [returnedBill_one]
  exact lintegral_price_accumulate_eq J p hp hc x s h

end Subprobability

end ITree
