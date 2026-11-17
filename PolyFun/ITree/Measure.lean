/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Resumption.Measure
public import PolyFun.ITree.Interp.Domain
public import PolyFun.ITree.Free

/-!
# Expected charge of an interaction tree

Visible requests incur state-dependent charges and update a shared state through kernels.
The price of a silent step is explicit. At zero price, weak bisimulation preserves the reading.
A positive price gives infinite expected charge to silent divergence.
-/

public section

open MeasureTheory ProbabilityTheory OmegaCompletePartialOrder
open PFunctor.Resumption (MeasurableExpectation ContinuousAlgebra statefulExpectedChargeAlgebra)
open scoped ENNReal

namespace ITree

universe uA uB uT uR

variable {P : PFunctor.{uA, uB}} {T : Type uT} {R : Type uR}
  [MeasurableSpace T] [∀ a, MeasurableSpace (P.B a)]
  [∀ a, Countable (P.B a)] [∀ a, MeasurableSingletonClass (P.B a)]
  (K : P.KernelHandler T) (c : P.A → T → ℝ≥0∞) (hc : ∀ a, Measurable (c a))

private instance withTauMeasurableSpace (a : (P + PFunctor.y.{uA, uB}).A) :
    MeasurableSpace ((P + PFunctor.y.{uA, uB}).B a) :=
  match a with
  | .inl a => inferInstanceAs (MeasurableSpace (P.B a))
  | .inr _ => inferInstanceAs (MeasurableSpace PUnit)

private instance withTauCountable (a : (P + PFunctor.y.{uA, uB}).A) :
    Countable ((P + PFunctor.y.{uA, uB}).B a) :=
  match a with
  | .inl a => inferInstanceAs (Countable (P.B a))
  | .inr _ => inferInstanceAs (Countable PUnit)

private instance withTauMeasurableSingletonClass (a : (P + PFunctor.y.{uA, uB}).A) :
    MeasurableSingletonClass ((P + PFunctor.y.{uA, uB}).B a) :=
  match a with
  | .inl a => inferInstanceAs (MeasurableSingletonClass (P.B a))
  | .inr _ => inferInstanceAs (MeasurableSingletonClass PUnit)

private noncomputable def withTauKernel : (P + PFunctor.y.{uA, uB}).KernelHandler T
  | .inl a => K a
  | .inr _ => Kernel.deterministic (fun s => (PUnit.unit, s))
    (measurable_const.prodMk measurable_id)

private def withTauPrice (tau : ℝ≥0∞) (a : (P + PFunctor.y.{uA, uB}).A) : T → ℝ≥0∞ :=
  match a with
  | .inl a => c a
  | .inr _ => fun _ => tau

omit [∀ a, MeasurableSpace (P.B a)] [∀ a, Countable (P.B a)]
  [∀ a, MeasurableSingletonClass (P.B a)] in
private theorem measurable_withTauPrice (hc : ∀ a, Measurable (c a)) (tau : ℝ≥0∞) :
    ∀ a, Measurable (withTauPrice c tau a) := by
  rintro (a | _)
  · exact hc a
  · exact measurable_const

private noncomputable def chargedAlgebra (tau : ℝ≥0∞) :
    ContinuousAlgebra (P + PFunctor.y.{uA, uB}) (MeasurableExpectation T) :=
  statefulExpectedChargeAlgebra (withTauKernel K) (withTauPrice c tau)
    (measurable_withTauPrice c hc tau)

private theorem chargedAlgebra_tau (tau : ℝ≥0∞) (u : PUnit.{uA + 1})
    (k : PUnit.{uB + 1} → MeasurableExpectation T) (s : T) :
    (chargedAlgebra K c hc tau (.inr u) k).1 s = tau + (k .unit).1 s := by
  rw [chargedAlgebra, PFunctor.Resumption.statefulExpectedChargeAlgebra_apply]
  change tau + ∫⁻ z : PUnit × T, (k z.1).1 z.2 ∂Measure.dirac (PUnit.unit, s) = _
  rw [lintegral_dirac' _ (measurable_from_prod_countable_right fun b => (k b).2)]

/-- Expected incurred charge including the price of every silent step. A return earns its
measurable terminal credit. -/
noncomputable def expectedCharge (tree : ITree P R) (ret : R → MeasurableExpectation T)
    (state : T) (tau : ℝ≥0∞ := 0) : ℝ≥0∞ :=
  (PFunctor.Resumption.denote ret (chargedAlgebra K c hc tau) (toResumptionWithTau tree)).1 state

@[simp] theorem expectedCharge_pure (r : R) (ret : R → MeasurableExpectation T)
    (s : T) (tau : ℝ≥0∞) :
    expectedCharge K c hc (ITree.pure r) ret s tau = (ret r).1 s := by
  simp [expectedCharge]

@[simp] theorem expectedCharge_step (tree : ITree P R) (ret : R → MeasurableExpectation T)
    (s : T) (tau : ℝ≥0∞) :
    expectedCharge K c hc (step tree) ret s tau = tau + expectedCharge K c hc tree ret s tau := by
  simp only [expectedCharge, toResumptionWithTau_step, PFunctor.Resumption.denote_query]
  exact chargedAlgebra_tau K c hc tau _ _ s

theorem expectedCharge_query (a : P.A) (next : P.B a → ITree P R)
    (ret : R → MeasurableExpectation T) (s : T) (tau : ℝ≥0∞) :
    expectedCharge K c hc (query a next) ret s tau =
      c a s + ∫⁻ z, expectedCharge K c hc (next z.1) ret z.2 tau ∂K a s := by
  simp only [expectedCharge, toResumptionWithTau_query, PFunctor.Resumption.denote_query]
  exact PFunctor.Resumption.statefulExpectedChargeAlgebra_apply K c hc a _ s

/-- With free silent guards, the cost is the continuous ITree interpretation. -/
theorem expectedCharge_eq_denote (tree : ITree P R) (ret : R → MeasurableExpectation T)
    (s : T) :
    expectedCharge K c hc tree ret s =
      (denote ret (statefulExpectedChargeAlgebra K c hc) tree).1 s := by
  unfold expectedCharge
  rw [← denote_toResumptionWithTau]
  have eq : chargedAlgebra K c hc 0 =
      ContinuousAlgebra.withTau (statefulExpectedChargeAlgebra K c hc) := by
    funext a
    rcases a with a | u
    · rfl
    · ext k s
      rw [chargedAlgebra_tau, zero_add]
      rfl
  rw [eq]

/-- Weakly bisimilar trees have equal costs when their silent steps cost zero. -/
theorem WeakBisim.expectedCharge_eq {left right : ITree P R} (h : WeakBisim left right)
    (ret : R → MeasurableExpectation T) (s : T) :
    expectedCharge K c hc left ret s = expectedCharge K c hc right ret s := by
  rw [expectedCharge_eq_denote, expectedCharge_eq_denote, h.denote_eq]

@[simp] theorem expectedCharge_diverge (ret : R → MeasurableExpectation T) (s : T) :
    expectedCharge K c hc diverge ret s = 0 := by
  simp only [expectedCharge_eq_denote, denote_diverge]
  rfl

/-- A divergent silent loop has infinite expected charge at any positive price. -/
theorem expectedCharge_diverge_of_pos (ret : R → MeasurableExpectation T) (s : T)
    {tau : ℝ≥0∞} (ht : 0 < tau) : expectedCharge K c hc diverge ret s tau = ⊤ := by
  by_contra h
  have loop : (diverge : ITree P R) = step diverge := eq_step_of_dest shape'_diverge
  have e := congrArg (fun t => expectedCharge K c hc t ret s tau) loop
  rw [expectedCharge_step, add_comm] at e
  exact (ENNReal.lt_add_right h ht.ne').ne e

/-- The cost of an embedded resumption uses the same joint state semantics. -/
theorem expectedCharge_toITree (tree : PFunctor.Resumption P R) (ret : R → MeasurableExpectation T)
    (s : T) : expectedCharge K c hc tree.toITree ret s =
      PFunctor.Resumption.expectedCharge K c tree (fun r => (ret r).1) s := by
  rw [expectedCharge_eq_denote, denote_toITree,
    PFunctor.Resumption.expectedCharge_eq_denote K c hc _ _ (fun r => (ret r).2)]

/-- Joint law of returns and final states. Silent steps make a deterministic transition that
leaves the state unchanged. -/
noncomputable def returnedKernel [MeasurableSpace R] (tree : ITree P R) : Kernel T (R × T) :=
  PFunctor.Resumption.returnedKernel (withTauKernel K) (toResumptionWithTau tree)

/-- Any terminal observation splits into incurred charge and its integral over actual returns,
including when the tree or the operation implementations can diverge. -/
theorem expectedCharge_eq_add_lintegral [MeasurableSpace R] (tree : ITree P R)
    (post : R × T → ℝ≥0∞) (hm : Measurable post) (s : T) (tau : ℝ≥0∞ := 0) :
    expectedCharge K c hc tree
      (fun r => ⟨fun t => post (r, t), hm.comp (measurable_const.prodMk measurable_id)⟩) s tau =
      expectedCharge K c hc tree (fun _ => ⊥) s tau + ∫⁻ z, post z ∂returnedKernel K tree s := by
  simp only [expectedCharge, chargedAlgebra, returnedKernel]
  have e := PFunctor.Resumption.expectedCharge_eq_add_lintegral (withTauKernel K)
    (withTauPrice c tau) (toResumptionWithTau tree) post hm s
  rw [PFunctor.Resumption.expectedCharge_eq_denote _ _ (measurable_withTauPrice c hc tau) _
    (Function.curry post) (fun _ => hm.comp (measurable_const.prodMk measurable_id)),
    PFunctor.Resumption.expectedCharge_eq_denote _ _ (measurable_withTauPrice c hc tau) _
    (fun _ _ => 0) (fun _ => measurable_const)] at e
  exact e

/-- The charge is measurable in the incoming state, also for paid silent steps. -/
theorem measurable_expectedCharge (tree : ITree P R) (ret : R → MeasurableExpectation T)
    (tau : ℝ≥0∞ := 0) : Measurable (fun t => expectedCharge K c hc tree ret t tau) :=
  (PFunctor.Resumption.denote ret (chargedAlgebra K c hc tau) (toResumptionWithTau tree)).2

/-- Sequencing a tree substitutes the charge of its continuation at the returned state. -/
theorem expectedCharge_bind {R' : Type*} (tree : ITree P R) (next : R → ITree P R')
    (ret : R' → MeasurableExpectation T) (s : T) (tau : ℝ≥0∞ := 0) :
    expectedCharge K c hc (bind tree next) ret s tau =
      expectedCharge K c hc tree (fun r => ⟨fun t => expectedCharge K c hc (next r) ret t tau,
        measurable_expectedCharge K c hc (next r) ret tau⟩) s tau := by
  simp only [expectedCharge, toResumptionWithTau_bind, PFunctor.Resumption.denote_bind]

section Returned

variable [MeasurableSpace R]

/-- With free operations and silent steps, the expected-charge transformer integrates the
terminal observation against the joint law of returned results and final states. -/
theorem expectedCharge_zero_eq_lintegral (tree : ITree P R)
    (post : R × T → ℝ≥0∞) (hm : Measurable post) (s : T) :
    expectedCharge K 0 (fun _ => measurable_const) tree
      (fun r => ⟨fun t => post (r, t), hm.comp (measurable_const.prodMk measurable_id)⟩) s =
      ∫⁻ z, post z ∂returnedKernel K tree s := by
  have hz : withTauPrice (P := P) (0 : P.A → T → ℝ≥0∞) 0 = 0 := by
    funext a
    cases a <;> rfl
  rw [returnedKernel, ← PFunctor.Resumption.expectedCharge_zero_eq_lintegral _ _ post hm, ← hz]
  exact congrFun (PFunctor.Resumption.expectedCharge_eq_denote _ (withTauPrice (P := P) 0 0)
    (measurable_withTauPrice 0 (fun _ => measurable_const) 0) _ (Function.curry post)
    (fun _ => hm.comp (measurable_const.prodMk measurable_id))).symm s

@[simp] theorem returnedKernel_pure (x : R) (s : T) :
    returnedKernel K (ITree.pure x) s = Measure.dirac (x, s) := by
  simp [returnedKernel]

/-- A visible request samples its answer and successor state before entering the continuation. -/
theorem returnedKernel_query (a : P.A) (next : P.B a → ITree P R) (s : T) :
    returnedKernel K (query a next) s =
      (K a s).bind (fun z => returnedKernel K (next z.1) z.2) := by
  rw [returnedKernel, toResumptionWithTau_query, PFunctor.Resumption.returnedKernel_query]
  rfl

/-- A silent step preserves the whole terminal law. -/
@[simp] theorem returnedKernel_step (tree : ITree P R) : returnedKernel K (step tree) =
    returnedKernel K tree := by
  ext1 s
  apply Measure.ext_of_lintegral
  intro f hf
  simp only [← expectedCharge_zero_eq_lintegral K _ f hf]
  exact (expectedCharge_step K (fun _ _ => 0) (fun _ => measurable_const) tree _ s 0).trans
    (zero_add _)

/-- A silently diverging tree has no terminal mass. -/
@[simp] theorem returnedKernel_diverge : returnedKernel K (diverge : ITree P R) = 0 := by
  ext1 s
  apply Measure.ext_of_lintegral
  intro f hf
  rw [← expectedCharge_zero_eq_lintegral K _ f hf, zero_apply, lintegral_zero_measure]
  exact expectedCharge_diverge K (fun _ _ => 0) (fun _ => measurable_const) _ s

theorem WeakBisim.returnedKernel_eq {left right : ITree P R} (h : WeakBisim left right) :
    returnedKernel K left = returnedKernel K right := by
  ext1 s
  apply Measure.ext_of_lintegral
  intro f hf
  rw [← expectedCharge_zero_eq_lintegral K _ f hf, ← expectedCharge_zero_eq_lintegral K _ f hf]
  exact h.expectedCharge_eq K (fun _ _ => 0) (fun _ => measurable_const) _ s

/-- The terminal law of a bind integrates the continuation's joint law from each returned state. -/
theorem returnedKernel_bind {R' : Type*} [MeasurableSpace R'] (tree : ITree P R)
    (next : R → ITree P R') (hnext : Measurable fun z : R × T => returnedKernel K (next z.1) z.2)
    (s : T) : returnedKernel K (bind tree next) s =
      (returnedKernel K tree s).bind (fun z => returnedKernel K (next z.1) z.2) := by
  rw [returnedKernel, toResumptionWithTau_bind, PFunctor.Resumption.returnedKernel_bind _ _ _ hnext]
  rfl

/-- Total terminal mass is at most one under subprobability operations. -/
instance returnedKernel.instIsSubprobabilityKernel [∀ a, IsSubprobabilityKernel (K a)]
    (tree : ITree P R) : IsSubprobabilityKernel (returnedKernel K tree) := by
  let (a : (P + PFunctor.y.{uA, uB}).A) : IsSubprobabilityKernel (withTauKernel K a) := by
    rcases a with a | _
    · exact inferInstanceAs (IsSubprobabilityKernel (K a))
    · unfold withTauKernel
      infer_instance
  unfold returnedKernel
  infer_instance

end Returned

/-- With every price and terminal credit zero, any client has zero charge. -/
@[simp] theorem expectedCharge_zero_bot (tree : ITree P R) (s : T) :
    expectedCharge K 0 (fun _ => measurable_const) tree (fun _ => ⊥) s = 0 := by
  let : MeasurableSpace R := ⊤
  exact (expectedCharge_zero_eq_lintegral K tree (fun _ => 0) measurable_const s).trans
    (by simp)

section Transfer

open PFunctor

universe u uQ uQB
variable {F : PFunctor.{u, u}} {Q : PFunctor.{uQ, uQB}} {S A : Type u}
  [MeasurableSpace S] [∀ a, MeasurableSpace (F.B a)] [∀ a, Countable (F.B a)]
  [∀ a, MeasurableSingletonClass (F.B a)]
  [∀ a, MeasurableSpace (Q.B a)] [∀ a, DiscreteMeasurableSpace (Q.B a)]
  (ν : (a : Q.A) → Measure (Q.B a)) (d : Q.A → ℝ≥0∞)

/-- Continuous interpretation of stateless, discrete-answer operations by expected charge. -/
@[expose] noncomputable def expectedChargeAlgebra : ContinuousAlgebra Q ℝ≥0∞ :=
  fun a => .ofFun (OpSpec.expectedCharge ν d a) (by
    refine ωScottContinuous.of_monotone_map_ωSup ⟨OpSpec.expectedCharge_mono ν d a, ?_⟩
    intro ch
    change (d a + ∫⁻ b, ⨆ n, ch n b ∂ν a) = ⨆ n, d a + ∫⁻ b, ch n b ∂ν a
    rw [lintegral_iSup (f := fun n b => ch n b) (fun _ => Measurable.of_discrete)
      (fun _ _ h b => ch.monotone h b), ENNReal.add_iSup])

private theorem denote_expectedChargeAlgebra_toITree {β : Type*} (x : Q.FreeM β)
    (post : β → ℝ≥0∞) :
    denote post (expectedChargeAlgebra ν d) x.toITree =
      FreeM.wpFold (OpSpec.expectedCharge ν d) x post := by
  change denote _ _ x.toResumption.toITree = _
  rw [denote_toITree, Resumption.denote_toResumption, FreeM.wpFold_eq_foldFreeM]
  rfl

variable (h : Handler.Stateful (FreeM Q) S F)
  (hK : ∀ a, Measurable fun s => FreeM.measureFold ν ((h a).run s))
  (hc : ∀ a, Measurable (h.expectedCharge ν d a))

private noncomputable def evaluateState (s : S) : MeasurableExpectation S →𝒄 ℝ≥0∞ :=
  .ofFun (fun f => f.1 s) (ωScottContinuous.of_monotone_map_ωSup
    ⟨fun _ _ h => h s, fun _ => rfl⟩)

/-- Running a stateful implementation on a possibly infinite client has the expected cost of
the client under the implementation's joint law and per-operation expected charges. -/
theorem expectedCharge_interp_run (tree : ITree F A) (ret : A → MeasurableExpectation S)
    (s : S) :
    denote (fun z : A × S => (ret z.1).1 z.2) (expectedChargeAlgebra ν d)
      ((interp (m := StateT S (ITree Q)) (fun a s => ((h a).run s).toITree) tree).run s) =
      expectedCharge (h.toKernelHandler ν hK) (h.expectedCharge ν d) hc tree ret s := by
  rw [expectedCharge_eq_denote]
  refine denote_interp_run _ _ _ evaluateState (fun _ => rfl) ?_ ret tree s
  intro a k t
  rw [denote_expectedChargeAlgebra_toITree]
  exact FreeM.wpFold_expectedCharge_eq_add_lintegral ν d ((h a).run t)
    (measurable_from_prod_countable_right fun b => (k b).2)

/-- A per-call bound on implementation charge gives an upper bound for the executed client.
The source's private state may persist across infinitely many requests. -/
theorem expectedCharge_interp_run_le (price : F.A → S → ℝ≥0∞)
    (hp : ∀ a, Measurable (price a)) (hcall : ∀ a s, h.expectedCharge ν d a s ≤ price a s)
    (tree : ITree F A) (ret : A → MeasurableExpectation S) (s : S) :
    denote (fun z : A × S => (ret z.1).1 z.2) (expectedChargeAlgebra ν d)
      ((interp (m := StateT S (ITree Q)) (fun a s => ((h a).run s).toITree) tree).run s) ≤
      expectedCharge (h.toKernelHandler ν hK) price hp tree ret s := by
  rw [expectedCharge_eq_denote]
  refine denote_interp_run_le _ _ _ (fun e s => (e : MeasurableExpectation S).1 s) ?_ ret tree s
  intro a k t
  rw [denote_expectedChargeAlgebra_toITree,
    FreeM.wpFold_expectedCharge_eq_add_lintegral ν d _
      (measurable_from_prod_countable_right fun b => (k b).2),
    Resumption.statefulExpectedChargeAlgebra_apply]
  exact add_le_add_left (hcall a t) _

end Transfer

section UnboundedHandler

open PFunctor

universe u vA vB vT
variable {F : PFunctor.{u, u}} {Q : PFunctor.{vA, vB}} {S A : Type u} {T : Type vT}
  [MeasurableSpace S] [MeasurableSpace T]
  [∀ a, MeasurableSpace (F.B a)] [∀ a, Countable (F.B a)]
  [∀ a, MeasurableSingletonClass (F.B a)]
  [∀ a, MeasurableSpace (Q.B a)] [∀ a, Countable (Q.B a)]
  [∀ a, MeasurableSingletonClass (Q.B a)]
  (h : PFunctor.Handler (StateT S (ITree Q)) F)
  (K : Q.KernelHandler T) (c : Q.A → T → ℝ≥0∞) (hc : ∀ a, Measurable (c a))

/-- An operation implementation returns its answer, its own private state, and the state of
the target operations. -/
@[expose] noncomputable def handlerReturnLaw (a : F.A) (st : S × T) : Measure (F.B a × S × T) :=
  ((returnedKernel K (h a st.1)) st.2).map MeasurableEquiv.prodAssoc

/-- Per-call charge including all work done by divergent operation implementations. -/
@[expose] noncomputable def handlerCharge (a : F.A) (st : S × T) : ℝ≥0∞ :=
  expectedCharge K c hc (h a st.1) (fun _ => ⊥) st.2

private noncomputable def observePrivateState (s : S) :
    MeasurableExpectation (S × T) →𝒄 MeasurableExpectation T :=
  .ofFun (fun f => ⟨fun t => f.1 (s, t), f.2.comp (measurable_const.prodMk measurable_id)⟩)
    (ωScottContinuous.of_monotone_map_ωSup ⟨fun _ _ h t => h (s, t), fun _ => rfl⟩)

/-- The source kernel induced by a stateful implementation. Its transition carries both the
implementation's private state and the target's state. -/
@[expose] noncomputable def handlerKernel (hK : ∀ a, Measurable (handlerReturnLaw h K a)) :
    F.KernelHandler (S × T) := fun a => ⟨handlerReturnLaw h K a, hK a⟩

private theorem denote_handler_eq (a : F.A) (k : F.B a → MeasurableExpectation (S × T))
    (s : S) (t : T) :
    (denote (fun z : F.B a × S => observePrivateState z.2 (k z.1))
      (statefulExpectedChargeAlgebra K c hc) (h a s)).1 t =
      handlerCharge h K c hc a (s, t) + ∫⁻ z, (k z.1).1 z.2 ∂handlerReturnLaw h K a (s, t) := by
  rw [← expectedCharge_eq_denote]
  have hk : Measurable (fun z : F.B a × S × T => (k z.1).1 z.2) :=
    measurable_from_prod_countable_right fun b => (k b).2
  rw [handlerReturnLaw, lintegral_map hk MeasurableEquiv.prodAssoc.measurable]
  exact expectedCharge_eq_add_lintegral K c hc (h a s)
    (fun z => (k z.1.1).1 (z.1.2, z.2)) (hk.comp MeasurableEquiv.prodAssoc.measurable) t

variable (hK : ∀ a, Measurable (handlerReturnLaw h K a))

/-- A pointwise per-operation budget bounds the executed client, including when operation
implementations diverge. Only the budget and the induced joint law must be measurable in
the two incoming states. -/
theorem expectedCharge_interp_run_unbounded_le (price : F.A → S × T → ℝ≥0∞)
    (hp : ∀ a, Measurable (price a)) (hcall : ∀ a st, handlerCharge h K c hc a st ≤ price a st)
    (tree : ITree F A) (ret : A → MeasurableExpectation (S × T)) (s : S) (t : T) :
    expectedCharge K c hc ((interp h tree).run s)
      (fun z => ⟨fun t => (ret z.1).1 (z.2, t),
        (ret z.1).2.comp (measurable_const.prodMk measurable_id)⟩) t ≤
      expectedCharge (handlerKernel h K hK) price hp tree ret (s, t) := by
  rw [expectedCharge_eq_denote, expectedCharge_eq_denote]
  refine (denote_interp_run_le h (statefulExpectedChargeAlgebra (handlerKernel h K hK) price hp)
    (statefulExpectedChargeAlgebra K c hc) (fun e s => observePrivateState s e) ?_ ret tree s) t
  intro a k state t'
  change (denote _ (statefulExpectedChargeAlgebra K c hc) (h a state)).1 t' ≤
    (statefulExpectedChargeAlgebra (handlerKernel h K hK) price hp a k).1 (state, t')
  rw [denote_handler_eq, Resumption.statefulExpectedChargeAlgebra_apply]
  exact add_le_add_left (hcall a (state, t')) _

/-- Expected-charge transfer for potentially divergent clients and operation implementations.
The lower-level kernel carries its own state. The induced source kernel keeps both states.
Silent interpreter guards cost zero. -/
theorem expectedCharge_interp_run_unbounded
    (hcost : ∀ a, Measurable (handlerCharge h K c hc a))
    (tree : ITree F A) (ret : A → MeasurableExpectation (S × T)) (s : S) (t : T) :
    expectedCharge K c hc ((interp h tree).run s)
      (fun z => ⟨fun t => (ret z.1).1 (z.2, t),
        (ret z.1).2.comp (measurable_const.prodMk measurable_id)⟩) t =
      expectedCharge (handlerKernel h K hK) (handlerCharge h K c hc) hcost tree ret (s, t) := by
  rw [expectedCharge_eq_denote, expectedCharge_eq_denote]
  have eq := denote_interp_run h
    (statefulExpectedChargeAlgebra (handlerKernel h K hK) (handlerCharge h K c hc) hcost)
    (statefulExpectedChargeAlgebra K c hc) observePrivateState (fun _ => rfl) ?_ ret tree s
  · exact congrArg (fun e : MeasurableExpectation T => e.1 t) eq
  · intro a k state
    exact Subtype.ext (funext fun t' => denote_handler_eq h K c hc a k state t')

/-- Interpreting a stateful client preserves the complete joint law of its result and both
final states. This statement is independent of any charge assigned to the operations. -/
theorem returnedKernel_interp_run [MeasurableSpace A] (tree : ITree F A) (s : S) (t : T) :
    ((returnedKernel K ((interp h tree).run s)) t).map MeasurableEquiv.prodAssoc =
      returnedKernel (handlerKernel h K hK) tree (s, t) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf MeasurableEquiv.prodAssoc.measurable]
  have hz : handlerCharge h K 0 (fun _ => measurable_const) = 0 := by
    funext a st
    exact expectedCharge_zero_bot K (h a st.1) st.2
  have hm : ∀ a, Measurable (handlerCharge h K 0 (fun _ => measurable_const) a) := by
    rw [hz]
    exact fun _ => measurable_const
  have sim := expectedCharge_interp_run_unbounded h K 0 (fun _ => measurable_const) hK hm tree
    (fun a => ⟨fun st => f (a, st), hf.comp (measurable_const.prodMk measurable_id)⟩) s t
  refine (expectedCharge_zero_eq_lintegral K _ (fun z => f (MeasurableEquiv.prodAssoc z))
    (hf.comp MeasurableEquiv.prodAssoc.measurable) t).symm.trans ?_
  refine Eq.trans ?_ (expectedCharge_zero_eq_lintegral (handlerKernel h K hK) tree f hf (s, t))
  simp only [hz] at sim
  exact sim

end UnboundedHandler

end ITree
