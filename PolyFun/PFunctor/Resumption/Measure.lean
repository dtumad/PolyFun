/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Resumption.Measure.ExpectedCharge

/-!
# The joint law of returned results and final states

A run returns at exactly one finite query depth. Summing the kernels for these disjoint
possibilities gives the terminal law, including for trees with infinite branches. The
expected-charge transformer adds the integral of terminal credit against this law to the
charge incurred along all finite prefixes.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PFunctor.Resumption

variable {P : PFunctor} {S α : Type*} [∀ a, MeasurableSpace (P.B a)] [MeasurableSpace S]
  (K : KernelHandler P S)

private theorem fold_zero_cost_zero {β : Type*} (x : FreeM P β) :
    FreeM.wpFold (OpSpec.statefulExpectedCharge K 0) x (fun _ _ => 0) = 0 := by
  induction x using FreeM.rec with
  | pure => rfl
  | liftBind a next ih =>
    funext s
    change (0 + ∫⁻ z, FreeM.wpFold (OpSpec.statefulExpectedCharge K 0) (next z.1)
      (fun _ _ => 0) z.2 ∂K a s) = 0
    simp [ih]

variable [∀ a, Countable (P.B a)] [∀ a, MeasurableSingletonClass (P.B a)] [MeasurableSpace α]

/-- Joint output and final state from runs that return after exactly the given number of queries. -/
noncomputable def returnAt : ℕ → Resumption P α → Kernel S (α × S)
  | 0, tree => match dest tree with
    | .inl x => Kernel.deterministic (fun s => (x, s)) (measurable_const.prodMk measurable_id)
    | .inr _ => 0
  | n + 1, tree => match dest tree with
    | .inl _ => 0
    | .inr ⟨a, next⟩ =>
      ⟨fun s => (K a s).bind (fun z => returnAt n (next z.1) z.2),
        (Measure.measurable_bind' (measurable_from_prod_countable_right
          (fun b => (returnAt n (next b)).measurable))).comp (K a).measurable⟩

/-- The terminal kernel sums the laws for each possible return depth. -/
noncomputable def returnedKernel (tree : Resumption P α) : Kernel S (α × S) :=
  Kernel.sum (fun n => returnAt K n tree)

private theorem returnAt_query_succ (a : P.A) (next : P.B a → Resumption P α) (n : ℕ)
    (s : S) : returnAt K (n + 1) (query a next) s =
      (K a s).bind (fun z => returnAt K n (next z.1) z.2) := by
  simp [returnAt, dest_query, Kernel.coe_mk]

private theorem lintegral_returnAt_query (a : P.A) (next : P.B a → Resumption P α)
    (n : ℕ) (f : α × S → ℝ≥0∞) (hf : Measurable f) (s : S) :
    (∫⁻ z, f z ∂returnAt K (n + 1) (query a next) s) =
      ∫⁻ z, (∫⁻ r, f r ∂returnAt K n (next z.1) z.2) ∂K a s := by
  rw [returnAt_query_succ, Measure.lintegral_bind _ hf.aemeasurable]
  apply Measurable.aemeasurable
  exact measurable_from_prod_countable_right fun b => (returnAt K n (next b)).measurable

private noncomputable abbrev prefixCost (c : P.A → S → ℝ≥0∞) (n : ℕ) (t : Resumption P α)
    (post : α → S → ℝ≥0∞) :=
  FreeM.wpFold (OpSpec.statefulExpectedCharge K c) (truncate n t)
    (fun r => r.elim (fun _ => 0) post)

private theorem prefix_decompose (c : P.A → S → ℝ≥0∞)
    (n : ℕ) (t : Resumption P α) (f : α × S → ℝ≥0∞) (hf : Measurable f) (s : S) :
    prefixCost K c n t (Function.curry f) s = prefixCost K c n t (fun _ _ => 0) s +
      ∑ j ∈ Finset.range (n + 1), ∫⁻ z, f z ∂returnAt K j t s := by
  induction n generalizing t s with
  | zero =>
    cases ht : dest t with
    | inl x =>
      simp [prefixCost, truncate_zero, ht, returnAt, Kernel.deterministic_apply,
        lintegral_dirac' _ hf]
    | inr node => simp [prefixCost, truncate_zero, ht, returnAt]
  | succ n ih =>
    cases ht : dest t with
    | inl x =>
      have he : t = pure x := eq_of_dest_eq (by simpa using ht)
      subst t
      rw [Finset.sum_range_succ']
      simp [prefixCost, returnAt, Kernel.deterministic_apply, lintegral_dirac' _ hf]
    | inr node =>
      obtain ⟨a, next⟩ := node
      have he : t = query a next := eq_of_dest_eq (by rw [dest_query]; exact ht)
      subst t
      simp only [prefixCost, truncate_query_succ, FreeM.wpFold_liftBind,
        OpSpec.statefulExpectedCharge_apply] at ⊢
      change (c a s + ∫⁻ z, prefixCost K c n (next z.1) (Function.curry f) z.2 ∂K a s) =
        (c a s + ∫⁻ z, prefixCost K c n (next z.1) (fun _ _ => 0) z.2 ∂K a s) + _
      simp_rw [ih]
      rw [Finset.sum_range_succ']
      simp only [lintegral_returnAt_query K a next _ f hf s]
      have hmeas (j : Nat) : Measurable (fun z : P.B a × S =>
          ∫⁻ r, f r ∂returnAt K j (next z.1) z.2) :=
        measurable_from_prod_countable_right fun b =>
          hf.lintegral_kernel (κ := returnAt K j (next b))
      rw [lintegral_add_right _ (Finset.measurable_sum _ (fun j _ => hmeas j)),
        lintegral_finsetSum _ (fun j _ => hmeas j), add_assoc]
      simp [returnAt]

/-- Expected incurred charge and the terminal law determine every measurable postexpectation. -/
theorem expectedCharge_eq_add_lintegral (c : P.A → S → ℝ≥0∞)
    (tree : Resumption P α) (f : α × S → ℝ≥0∞) (hf : Measurable f) (s : S) :
    expectedCharge K c tree (Function.curry f) s = expectedCharge K c tree (fun _ _ => 0) s +
      ∫⁻ z, f z ∂returnedKernel K tree s := by
  simp only [expectedCharge_eq_iSup, returnedKernel, Kernel.sum_apply, lintegral_sum_measure]
  change (⨆ n, prefixCost K c n tree (Function.curry f) s) =
    (⨆ n, prefixCost K c n tree (fun _ _ => 0) s) + _
  simp_rw [prefix_decompose K c _ tree f hf s]
  rw [ENNReal.tsum_eq_iSup_nat' (Filter.tendsto_add_atTop_nat 1)]
  apply Eq.symm
  apply ENNReal.iSup_add_iSup_of_monotone
  · exact fun i j hij => monotone_wpFold_expectedCharge_truncate K c tree _ hij s
  · intro i j hij
    exact Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))

/-- With free calls the transformer integrates just the returned outcome and final state. -/
theorem expectedCharge_zero_eq_lintegral (tree : Resumption P α) (f : α × S → ℝ≥0∞)
    (hf : Measurable f) (s : S) :
    expectedCharge K 0 tree (Function.curry f) s = ∫⁻ z, f z ∂returnedKernel K tree s := by
  rw [expectedCharge_eq_add_lintegral K 0 tree f hf s, expectedCharge_eq_iSup]
  have hz : (fun r : Option α => r.elim (fun _ : S => (0 : ℝ≥0∞)) (fun _ _ => 0)) =
      (fun _ _ => 0) := funext fun r => by cases r <;> rfl
  simp [hz, fold_zero_cost_zero]

/-- A return preserves the private state and gives the specified result with unit mass. -/
@[simp] theorem returnedKernel_pure (x : α) (s : S) :
    returnedKernel K (pure x) s = Measure.dirac (x, s) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [← expectedCharge_zero_eq_lintegral K _ f hf, expectedCharge_pure, lintegral_dirac' _ hf]
  rfl

/-- A query samples both the answer and its successor state before running the continuation. -/
theorem returnedKernel_query (a : P.A) (next : P.B a → Resumption P α) (s : S) :
    returnedKernel K (query a next) s =
      (K a s).bind (fun z => returnedKernel K (next z.1) z.2) := by
  have hm : Measurable (fun z : P.B a × S => returnedKernel K (next z.1) z.2) :=
    measurable_from_prod_countable_right (fun b => (returnedKernel K (next b)).measurable)
  apply Measure.ext_of_lintegral
  intro f hf
  rw [← expectedCharge_zero_eq_lintegral K _ f hf,
    expectedCharge_query K 0 (fun _ => measurable_const) a next (Function.curry f)
      (fun _ => hf.comp (measurable_const.prodMk measurable_id)),
    Measure.lintegral_bind hm.aemeasurable hf.aemeasurable]
  simp only [Pi.zero_apply, zero_add, expectedCharge_zero_eq_lintegral K _ f hf]

/-- The terminal kernel of a sequential program integrates the continuation's terminal law
against the first program's joint result-and-state law. -/
theorem returnedKernel_bind {β : Type*} [MeasurableSpace β] (tree : Resumption P α)
    (next : α → Resumption P β)
    (hnext : Measurable fun z : α × S => returnedKernel K (next z.1) z.2) (s : S) :
    returnedKernel K (bind tree next) s =
      (returnedKernel K tree s).bind (fun z => returnedKernel K (next z.1) z.2) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [← expectedCharge_zero_eq_lintegral K _ f hf,
    expectedCharge_bind K 0 (fun _ => measurable_const) tree next (Function.curry f)
      (fun _ => hf.comp (measurable_const.prodMk measurable_id)),
    Measure.lintegral_bind hnext.aemeasurable hf.aemeasurable]
  have hm : Measurable (fun z : α × S => ∫⁻ y, f y ∂returnedKernel K (next z.1) z.2) :=
    (Measure.measurable_lintegral hf).comp hnext
  rw [← expectedCharge_zero_eq_lintegral K tree _ hm s]
  apply congrArg (fun post => expectedCharge K 0 tree post s)
  funext x t
  exact expectedCharge_zero_eq_lintegral K (next x) f hf t

/-- Each returned outcome consumes its run's mass once, even on an unbounded tree. -/
instance returnedKernel.instIsSubprobabilityKernel [∀ a, IsSubprobabilityKernel (K a)]
    (tree : Resumption P α) : IsSubprobabilityKernel (returnedKernel K tree) := by
  constructor
  intro s
  rw [← lintegral_one, ← expectedCharge_zero_eq_lintegral K tree _ measurable_const,
    expectedCharge_eq_iSup]
  refine iSup_le fun n => ?_
  generalize truncate n tree = x
  induction x using FreeM.rec generalizing s with
  | pure r => cases r <;> simp [Function.curry]
  | liftBind a next ih =>
    simp only [FreeM.wpFold_liftBind, OpSpec.statefulExpectedCharge_apply, Pi.zero_apply, zero_add]
    exact (lintegral_mono (fun z : P.B a × S => ih z.1 z.2)).trans
      (by simpa using (K a).measure_univ_le s)

/-- Any well-founded program has the same joint law under either interpretation, including
programs whose finite paths have no common length bound. -/
theorem returnedKernel_toResumption (x : FreeM P α) :
    returnedKernel K x.toResumption = FreeM.runKernel K x := by
  ext1 s
  apply Measure.ext_of_lintegral
  intro f hf
  rw [← expectedCharge_zero_eq_lintegral K _ f hf,
    expectedCharge_toResumption K 0 (fun _ => measurable_const) x (Function.curry f) (fun _ =>
      hf.comp (measurable_const.prodMk measurable_id))]
  change FreeM.wpFold (OpSpec.statefulExpectedCharge K 0) x (fun a s => f (a, s)) s = _
  have h := FreeM.wpFold_statefulExpectedCharge_eq_add_lintegral K 0 x hf s
  simpa only [fold_zero_cost_zero, Pi.zero_apply, zero_add] using h

/-- Equality of scalar cost observations recovers both the incurred cost and the terminal
law at finite cost. At infinite cost every terminal observation is absorbed. -/
theorem expectedCharge_ext_iff (L : KernelHandler P S) (c d : P.A → S → ℝ≥0∞)
    (t u : Resumption P α) (s v : S) :
    (∀ f : α × S → ℝ≥0∞, Measurable f →
      expectedCharge K c t (Function.curry f) s = expectedCharge L d u (Function.curry f) v) ↔
    expectedCharge K c t (fun _ _ => 0) s = expectedCharge L d u (fun _ _ => 0) v ∧
      (expectedCharge K c t (fun _ _ => 0) s = ⊤ ∨
        returnedKernel K t s = returnedKernel L u v) := by
  constructor
  · intro h
    have hcost := h (fun _ => 0) measurable_const
    change expectedCharge K c t (fun _ _ => 0) s = expectedCharge L d u (fun _ _ => 0) v at hcost
    refine ⟨hcost, or_iff_not_imp_left.mpr fun hfin => Measure.ext_of_lintegral _ fun f hf => ?_⟩
    have he := h f hf
    rw [expectedCharge_eq_add_lintegral K c t f hf, expectedCharge_eq_add_lintegral L d u f hf,
      ← hcost] at he
    exact (ENNReal.add_right_inj hfin).mp he
  · rintro ⟨he, h⟩ f hf
    rw [expectedCharge_eq_add_lintegral K c t f hf, expectedCharge_eq_add_lintegral L d u f hf,
      ← he]
    rcases h with hinf | heq
    · simp only [hinf, top_add]
    · rw [heq]

end PFunctor.Resumption
