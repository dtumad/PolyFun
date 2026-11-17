/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Resumption.Collect
public import PolyFun.PFunctor.Resumption.Measure
public import PolyFun.PFunctor.Resumption.Measure.Retry
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Result-bearing retries and finite sequences of unbounded stages

A stage asks the same question until its answer yields a payload. The next stage is selected
by that payload. Costs count every attempted operation, including an operation that loses mass.
-/

public section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace PFunctor.Resumption.Collect

variable {P : PFunctor} {X S : Type*}

/-- Accepting the true Boolean recovers the Boolean retry tree. -/
theorem retry_bool :
    retry (P := Retry.Trial) () (fun b : Bool => if b then some () else none) = Retry.tree := by
  apply retry_unique
  conv_lhs => rw [Retry.tree_eq_query]
  congr 1
  funext b
  cases b <;> rfl

variable [∀ a, MeasurableSpace (P.B a)] [MeasurableSpace S]
  (K : KernelHandler P S) (a : P.A) (accept : P.B a → Option X)

/-- A finite observation cuts off with zero credit after the last permitted trial. -/
@[expose] noncomputable def observe (c : S → ℝ≥0∞) (post : X → S → ℝ≥0∞) : ℕ → S → ℝ≥0∞
  | 0, _ => 0
  | n + 1, s => c s + ∫⁻ z, (accept z.1).elim (observe c post n z.2) (fun x => post x z.2) ∂K a s

theorem expectedCharge_retry (c : P.A → S → ℝ≥0∞) (post : X → S → ℝ≥0∞) (s : S) :
    expectedCharge K c (retry a accept) post s = ⨆ n, observe K a accept (c a) post n s := by
  rw [expectedCharge_eq_iSup]
  apply iSup_congr
  intro n
  induction n generalizing s with
  | zero => rw [retry_eq_query, truncate_query_zero]; rfl
  | succ n ih =>
    rw [retry_eq_query, truncate_query_succ, FreeM.wpFold_liftBind,
      OpSpec.statefulExpectedCharge_apply, observe]
    congr 1
    apply lintegral_congr
    intro z
    cases h : accept z.1 <;> simp [ih]

/-- The stage invariant persists on a rejected answer and advances on an accepted payload. -/
abbrev Preserves (I : S → Prop) (J : X → S → Prop) : Prop :=
  ∀ s, I s → ∀ᵐ z ∂K a s, (accept z.1).elim (I z.2) (fun x => J x z.2)

/-- Zero terminal credit on every reachable acceptance gives zero expected terminal credit,
regardless of the mass of a trial. -/
theorem expectedCharge_retry_zero {a : P.A} {accept : P.B a → Option X}
    {I : S → Prop} {J : X → S → Prop} {post : X → S → ℝ≥0∞}
    (hI : Preserves K a accept I J)
    (hpost : ∀ x s, J x s → post x s = 0) {s : S} (hs : I s) :
    expectedCharge K 0 (retry a accept) post s = 0 := by
  rw [expectedCharge_retry]
  apply le_antisymm _ zero_le
  refine iSup_le fun n => ?_
  induction n generalizing s with
  | zero => exact le_rfl
  | succ n ih =>
    simp only [observe, Pi.zero_apply, zero_add, nonpos_iff_eq_zero]
    apply (lintegral_congr_ae (g := fun _ => 0) ?_).trans lintegral_zero
    filter_upwards [hI s hs] with z hz
    cases h : accept z.1 with
    | none => exact (ih (s := z.2) (by simpa [h] using hz)).antisymm zero_le
    | some x => exact hpost x z.2 (by simpa [h] using hz)

/-! ## Expected charge of a stage -/

variable [∀ a, Countable (P.B a)] [∀ a, MeasurableSingletonClass (P.B a)]

private theorem measurable_reject : MeasurableSet {z : P.B a × S | accept z.1 = none} :=
  measurable_fst (Set.to_countable {b : P.B a | accept b = none}).measurableSet

private theorem integral_branch (s : S) (F T : ℝ≥0∞) :
    (∫⁻ z, (accept z.1).elim F (fun _ => T) ∂K a s) =
      F * K a s {z | accept z.1 = none} + T * K a s {z | accept z.1 ≠ none} := by
  have hr := measurable_reject (S := S) a accept
  have ha : MeasurableSet {z : P.B a × S | accept z.1 ≠ none} := hr.compl
  rw [← lintegral_indicator_const hr, ← lintegral_indicator_const ha,
    ← lintegral_add_left (measurable_const.indicator hr)]
  apply lintegral_congr
  intro z
  cases h : accept z.1 <;> simp [h, Set.indicator]

private theorem measurable_option (f : S → ℝ≥0∞) (g : X → S → ℝ≥0∞)
    (hf : Measurable f) (hg : ∀ x, Measurable (g x)) :
    Measurable fun z : P.B a × S => (accept z.1).elim (f z.2) (fun x => g x z.2) := by
  apply measurable_from_prod_countable_right
  intro b
  cases h : accept b <;> simp [h, hf, hg]

variable {K a accept} {I : S → Prop} {J : X → S → Prop} {C p B : ℝ≥0∞}
  {post : X → S → ℝ≥0∞}

/-- The local expected-potential inequality may transfer different credit to a retry and
to each accepted payload. -/
theorem expectedCharge_retry_le_of_potential (c : P.A → S → ℝ≥0∞)
    (V : S → ℝ≥0∞) (W : X → S → ℝ≥0∞) (hp : p ≤ 1)
    (hI : Preserves K a accept I J)
    (hr : ∀ s, I s → K a s {z | accept z.1 = none} ≤ 1 - p)
    (hm : ∀ s, I s → K a s Set.univ ≤ 1)
    (hc : ∀ s, I s → c a s + ∫⁻ z, (accept z.1).elim (V z.2) (fun x => W x z.2) ∂K a s ≤
      C + V s)
    (hpost : ∀ x s, J x s → post x s ≤ B + W x s) {s : S} (hs : I s) :
    expectedCharge K c (retry a accept) post s ≤ C / p + B + V s := by
  rw [expectedCharge_retry]
  let U (n : ℕ) := C * ∑ i ∈ Finset.range n, (1 - p) ^ i
  have bound (n : ℕ) (t : S) (ht : I t) :
      observe K a accept (c a) post n t ≤ U n + B + V t := by
    induction n generalizing t with
    | zero => exact bot_le
    | succ n ih =>
      rw [observe]
      let branch (z : P.B a × S) := (accept z.1).elim (U n) (fun _ => 0)
      let credit (z : P.B a × S) := (accept z.1).elim (V z.2) (fun x => W x z.2)
      have hb : Measurable branch := measurable_option a accept _ _
        measurable_const (fun _ => measurable_const)
      have hmono : (∫⁻ z, (accept z.1).elim (observe K a accept (c a) post n z.2)
          (fun x => post x z.2) ∂K a t) ≤ ∫⁻ z, (branch z + B) + credit z ∂K a t := by
        apply lintegral_mono_ae
        filter_upwards [hI t ht] with z hz
        cases h : accept z.1 with
        | none => simpa [branch, credit, h] using ih z.2 (by simpa [h] using hz)
        | some x => simpa [branch, credit, h] using hpost x z.2 (by simpa [h] using hz)
      have hbill := hc t ht
      change c a t + (∫⁻ z, credit z ∂K a t) ≤ C + V t at hbill
      have hcost : (∫⁻ z, branch z ∂K a t) ≤ U n * (1 - p) := by
        rw [show (∫⁻ z, branch z ∂K a t) = _ from integral_branch K a accept t (U n) 0]
        simpa using mul_le_mul_right (hr t ht) (U n)
      have hconst : (∫⁻ _ : P.B a × S, B ∂K a t) ≤ B := by
        simpa using mul_le_mul_right (hm t ht) B
      calc _ ≤ c a t + ∫⁻ z, (branch z + B) + credit z ∂K a t := by gcongr
           _ = (∫⁻ z, branch z ∂K a t) + (∫⁻ _ : P.B a × S, B ∂K a t) +
               (c a t + ∫⁻ z, credit z ∂K a t) := by
                rw [lintegral_add_left (f := fun z => branch z + B) (hb.add measurable_const),
                  lintegral_add_left hb]
                ac_rfl
           _ ≤ (U n * (1 - p) + B) + (C + V t) := add_le_add (add_le_add hcost hconst) hbill
           _ = U (n + 1) + B + V t := by simp only [U, geom_sum_succ, mul_add, mul_one]; ac_rfl
  refine iSup_le fun n => (bound n s hs).trans (add_le_add_left (add_le_add_left ?_ _) _)
  have hsub := (ENNReal.cancel_of_ne (ne_top_of_le_ne_top ENNReal.one_ne_top
    (tsub_le_self : 1 - p ≤ 1))).tsub_tsub_cancel_of_le hp
  simpa [U, ENNReal.tsum_geometric, hsub, div_eq_mul_inv] using
    mul_le_mul_right (sum_le_tsum (f := fun i : ℕ => (1 - p) ^ i) (Finset.range n)) C

/-- Exact uniform prices and success probabilities give an exact stage expectation.
The accepted terminal credit may depend on the payload and state away from reached outcomes. -/
theorem expectedCharge_retry_eq (c : P.A → S → ℝ≥0∞) (hp : 0 < p) (hp' : p ≤ 1)
    (hI : Preserves K a accept I J)
    (hr : ∀ s, I s → K a s {z | accept z.1 = none} = 1 - p)
    (hm : ∀ s, I s → K a s Set.univ = 1)
    (hc : ∀ s, I s → c a s = C)
    (hpost : ∀ x s, J x s → post x s = B) {s : S} (hs : I s) :
    expectedCharge K c (retry a accept) post s = C / p + B := by
  have hsub := (ENNReal.cancel_of_ne (ne_top_of_le_ne_top ENNReal.one_ne_top
    (tsub_le_self : 1 - p ≤ 1))).tsub_tsub_cancel_of_le hp'
  let U (n : ℕ) := (C + B * p) * ∑ i ∈ Finset.range n, (1 - p) ^ i
  have eqn (n : ℕ) (t : S) (ht : I t) : observe K a accept (c a) post n t = U n := by
    induction n generalizing t with
    | zero => simp [observe, U]
    | succ n ih =>
      rw [observe, hc t ht]
      have he : {z : P.B a × S | accept z.1 ≠ none} = {z | accept z.1 = none}ᶜ := rfl
      have ha : K a t {z | accept z.1 ≠ none} = p := by
        rw [he, measure_compl (measurable_reject a accept)
          (hr t ht ▸ ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self), hm t ht, hr t ht, hsub]
      have hstep : (∫⁻ z, (accept z.1).elim (observe K a accept (c a) post n z.2)
          (fun x => post x z.2) ∂K a t) = ∫⁻ z, (accept z.1).elim (U n) (fun _ => B) ∂K a t := by
        apply lintegral_congr_ae
        filter_upwards [hI t ht] with z hz
        cases h : accept z.1 with
        | none => simpa using ih z.2 (by simpa [h] using hz)
        | some x => simpa using hpost x z.2 (by simpa [h] using hz)
      rw [hstep, integral_branch, hr t ht, ha]
      simp only [U, geom_sum_succ, mul_add, mul_one]
      ac_rfl
  rw [expectedCharge_retry]
  simp_rw [eqn _ s hs]
  change (⨆ n : ℕ, (C + B * p) * ∑ i ∈ Finset.range n, (1 - p) ^ i) = _
  rw [← ENNReal.mul_iSup, ← ENNReal.tsum_eq_iSup_nat, ENNReal.tsum_geometric, hsub,
    add_mul, mul_assoc, ENNReal.mul_inv_cancel hp.ne' (ne_top_of_le_ne_top ENNReal.one_ne_top hp'),
    mul_one, div_eq_mul_inv]

/-- A uniform positive lower bound on acceptance gives expected terminal credit at least one
when every reachable acceptance earns at least one and each reached trial is lossless. -/
theorem le_expectedCharge_retry (hp : 0 < p) (hI : Preserves K a accept I J)
    (hr : ∀ s, I s → K a s {z | accept z.1 = none} ≤ 1 - p)
    (hm : ∀ s, I s → K a s Set.univ = 1)
    (hpost : ∀ x s, J x s → 1 ≤ post x s) {s : S} (hs : I s) :
    1 ≤ expectedCharge K 0 (retry a accept) post s := by
  let q := 1 - p
  have h (n : ℕ) (t : S) (ht : I t) : 1 ≤ observe K a accept 0 post n t + q ^ n := by
    induction n generalizing t with
    | zero => simp [observe]
    | succ n ih =>
      let rem (z : P.B a × S) := (accept z.1).elim (q ^ n) (fun _ => 0)
      let step (z : P.B a × S) :=
        (accept z.1).elim (observe K a accept 0 post n z.2) (fun x => post x z.2)
      have hrem : Measurable rem := measurable_option a accept _ _ measurable_const
        (fun _ => measurable_const)
      have hmono : (∫⁻ _ : P.B a × S, 1 ∂K a t) ≤ ∫⁻ z, step z + rem z ∂K a t := by
        apply lintegral_mono_ae
        filter_upwards [hI t ht] with z hz
        cases hh : accept z.1 with
        | none => simpa [step, rem, hh] using ih z.2 (by simpa [hh] using hz)
        | some x => simpa [step, rem, hh] using hpost x z.2 (by simpa [hh] using hz)
      rw [lintegral_one, hm t ht, lintegral_add_right _ hrem] at hmono
      refine hmono.trans (add_le_add (by simp [observe, step]) ?_)
      rw [show (∫⁻ z, rem z ∂K a t) = _ from integral_branch K a accept t (q ^ n) 0, pow_succ]
      simpa using mul_le_mul_right (hr t ht) (q ^ n)
  rw [expectedCharge_retry]
  have hq : q < 1 := ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hp.ne'
  have hlim := (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hq).const_add
    (⨆ j, observe K a accept 0 post j s)
  apply le_of_le_of_eq (ge_of_tendsto hlim (Eventually.of_forall fun n =>
    (h n s hs).trans (add_le_add_left (le_iSup (fun j => observe K a accept 0 post j s) n) _)))
  simp

/-! ## Sequential stages -/

variable (K) (act : ℕ → X → P.A)
  (accept : (i : ℕ) → (x : X) → P.B (act i x) → Option X)

/-- A collection invariant advances to the next stage on success. -/
abbrev StagesPreserve (I : ℕ → X → S → Prop) :=
  ∀ i x, Preserves K (act i x) (accept i x) (I (i + 1) x) (I i)

/-- A potential can move credit between attempts, stages, and distinct accepted payloads. -/
theorem expectedCharge_collect_le_of_potential (c : P.A → S → ℝ≥0∞) (hc : ∀ a, Measurable (c a))
    (I : ℕ → X → S → Prop) (p C : ℕ → ℝ≥0∞) (V : ℕ → X → S → ℝ≥0∞)
    (hp : ∀ i x s, I (i + 1) x s → p i ≤ 1) (hI : StagesPreserve K act accept I)
    (hr : ∀ i x s, I (i + 1) x s → K (act i x) s {z | accept i x z.1 = none} ≤ 1 - p i)
    (hm : ∀ i x s, I (i + 1) x s → K (act i x) s Set.univ ≤ 1)
    (hprice : ∀ i x s, I (i + 1) x s → c (act i x) s +
      ∫⁻ z, (accept i x z.1).elim (V (i + 1) x z.2) (fun y => V i y z.2) ∂K (act i x) s ≤
        C i + V (i + 1) x s)
    (post : X → S → ℝ≥0∞) (hpost : ∀ x, Measurable (post x)) (B : ℝ≥0∞)
    (hfinish : ∀ x s, I 0 x s → post x s ≤ B + V 0 x s)
    (k : ℕ) (x : X) (s : S) (hs : I k x s) :
    expectedCharge K c (collect act accept k x) post s ≤
      (∑ i ∈ Finset.range k, C i / p i) + B + V k x s := by
  induction k generalizing x s with
  | zero => simpa using hfinish x s hs
  | succ i ih =>
    rw [collect_succ, expectedCharge_bind K c hc _ _ post hpost]
    refine (expectedCharge_retry_le_of_potential c (V (i + 1) x) (V i) (hp i x s hs)
      (hI i x) (hr i x) (hm i x) (hprice i x) ih hs).trans_eq ?_
    rw [Finset.sum_range_succ]
    ac_rfl

/-- A per-attempt price and a lower bound on its acceptance probability give the sum of
the stage budgets. Missing mass spends the current charge and ends the run. -/
theorem expectedCharge_collect_le (c : P.A → S → ℝ≥0∞) (hc : ∀ a, Measurable (c a))
    (I : ℕ → X → S → Prop) (p C : ℕ → ℝ≥0∞)
    (hp : ∀ i x s, I (i + 1) x s → p i ≤ 1) (hI : StagesPreserve K act accept I)
    (hr : ∀ i x s, I (i + 1) x s → K (act i x) s {z | accept i x z.1 = none} ≤ 1 - p i)
    (hm : ∀ i x s, I (i + 1) x s → K (act i x) s Set.univ ≤ 1)
    (hprice : ∀ i x s, I (i + 1) x s → c (act i x) s ≤ C i)
    (post : X → S → ℝ≥0∞) (hpost : ∀ x, Measurable (post x)) (B : ℝ≥0∞)
    (hfinish : ∀ x s, I 0 x s → post x s ≤ B)
    (k : ℕ) (x : X) (s : S) (hs : I k x s) :
    expectedCharge K c (collect act accept k x) post s ≤ (∑ i ∈ Finset.range k, C i / p i) + B := by
  have hz (v : Option X) : v.elim (0 : ℝ≥0∞) (fun _ => 0) = 0 := by cases v <;> rfl
  simpa using expectedCharge_collect_le_of_potential K act accept c hc I p C (fun _ _ _ => 0)
    hp hI hr hm (fun i x s hs => by simpa [hz] using hprice i x s hs)
    post hpost B (by simpa using hfinish) k x s hs

/-- Uniform conditional acceptance and a constant price on each stage give its exact
expected charge. No independence between stages is necessary. -/
theorem expectedCharge_collect_eq (c : P.A → S → ℝ≥0∞) (hc : ∀ a, Measurable (c a))
    (I : ℕ → X → S → Prop) (p C : ℕ → ℝ≥0∞)
    (hp : ∀ i x s, I (i + 1) x s → 0 < p i ∧ p i ≤ 1) (hI : StagesPreserve K act accept I)
    (hr : ∀ i x s, I (i + 1) x s → K (act i x) s {z | accept i x z.1 = none} = 1 - p i)
    (hm : ∀ i x s, I (i + 1) x s → K (act i x) s Set.univ = 1)
    (hprice : ∀ i x s, I (i + 1) x s → c (act i x) s = C i)
    (post : X → S → ℝ≥0∞) (hpost : ∀ x, Measurable (post x)) (B : ℝ≥0∞)
    (hfinish : ∀ x s, I 0 x s → post x s = B)
    (k : ℕ) (x : X) (s : S) (hs : I k x s) :
    expectedCharge K c (collect act accept k x) post s = (∑ i ∈ Finset.range k, C i / p i) + B := by
  induction k generalizing x s with
  | zero => simpa using hfinish x s hs
  | succ i ih =>
    rw [collect_succ, expectedCharge_bind K c hc _ _ post hpost,
      expectedCharge_retry_eq c (hp i x s hs).1 (hp i x s hs).2 (hI i x) (hr i x) (hm i x)
        (hprice i x) ih hs, Finset.sum_range_succ]
    ac_rfl

variable [MeasurableSpace X]

/-- Every returned payload and final state satisfies the final invariant, even for a
lossy or nonterminating collector. -/
theorem ae_returnedKernel_collect (I : ℕ → X → S → Prop) (hI : StagesPreserve K act accept I)
    (hfinal : MeasurableSet {z : X × S | I 0 z.1 z.2})
    (k : ℕ) (x : X) (s : S) (hs : I k x s) :
    ∀ᵐ z ∂returnedKernel K (collect act accept k x) s, I 0 z.1 z.2 := by
  let bad := {z : X × S | ¬I 0 z.1 z.2}
  have hb : MeasurableSet bad := hfinal.compl
  let reward : X × S → ℝ≥0∞ := bad.indicator (fun _ => 1)
  have hreward : Measurable reward := measurable_const.indicator hb
  have hz : expectedCharge K 0 (collect act accept k x) (Function.curry reward) s = 0 := by
    induction k generalizing x s with
    | zero => simp [Function.curry, reward, bad, hs]
    | succ i ih =>
      rw [collect_succ, expectedCharge_bind K 0 (fun _ => measurable_const) _ _
        (Function.curry reward) (fun y => hreward.comp (measurable_const.prodMk measurable_id))]
      exact expectedCharge_retry_zero K (hI i x) ih hs
  rw [expectedCharge_zero_eq_lintegral K _ reward hreward, show reward = _ from rfl,
    lintegral_indicator_const hb, one_mul] at hz
  exact ae_iff.mpr hz

/-- The final joint return law has mass one whenever every stage is lossless and has a
positive uniform chance of success on its invariant. -/
theorem returnedKernel_collect_univ (I : ℕ → X → S → Prop) (p : ℕ → ℝ≥0∞)
    (hp : ∀ i x s, I (i + 1) x s → 0 < p i ∧ p i ≤ 1) (hI : StagesPreserve K act accept I)
    (hr : ∀ i x s, I (i + 1) x s → K (act i x) s {z | accept i x z.1 = none} ≤ 1 - p i)
    (hm : ∀ i x s, I (i + 1) x s → K (act i x) s Set.univ = 1)
    (k : ℕ) (x : X) (s : S) (hs : I k x s) :
    returnedKernel K (collect act accept k x) s Set.univ = 1 := by
  rw [← lintegral_one, ← expectedCharge_zero_eq_lintegral K _ _ measurable_const]
  change expectedCharge K 0 (collect act accept k x) (fun _ _ => 1) s = 1
  apply le_antisymm
  · simpa using expectedCharge_collect_le K act accept 0 (fun _ => measurable_const) I p
      (fun _ => 0) (fun i y t ht => (hp i y t ht).2) hI hr (fun i y t ht => (hm i y t ht).le)
      (by simp) (fun _ _ => 1) (fun _ => measurable_const) 1 (by simp) k x s hs
  · induction k generalizing x s with
    | zero => simp
    | succ i ih =>
      rw [collect_succ, expectedCharge_bind K 0 (fun _ => measurable_const) _ _ _
        (fun _ => measurable_const)]
      exact le_expectedCharge_retry (hp i x s hs).1 (hI i x) (hr i x) (hm i x) ih hs

section

omit [MeasurableSpace X]

/-- Rejected answers carry the mass left after subtracting all payload-bearing answers. -/
theorem rejectMass_eq_sub_acceptMass (a : P.A) (pick : P.B a → Option X) (s : S)
    (hfin : K a s {z | (pick z.1).isSome} ≠ ∞) :
    K a s {z | pick z.1 = none} = K a s Set.univ - K a s {z | (pick z.1).isSome} := by
  have he : {z : P.B a × S | pick z.1 = none} = {z | (pick z.1).isSome}ᶜ := by
    ext z
    cases h : pick z.1 <;> simp [h]
  rw [he, measure_compl _ hfin]
  exact measurable_fst (Set.to_countable {b : P.B a | (pick b).isSome}).measurableSet

private theorem reject_le_of_accept_ge {a : P.A} {pick : P.B a → Option X} {s : S} {q : ℝ≥0∞}
    (hm : K a s Set.univ ≤ 1) (ha : q ≤ K a s {z | (pick z.1).isSome}) :
    q ≤ 1 ∧ K a s {z | pick z.1 = none} ≤ 1 - q := by
  have hle : K a s {z | (pick z.1).isSome} ≤ K a s Set.univ :=
    measure_mono (Set.subset_univ _)
  refine ⟨ha.trans (hle.trans hm), ?_⟩
  rw [rejectMass_eq_sub_acceptMass K a pick s (ne_top_of_le_ne_top ENNReal.one_ne_top
    (hle.trans hm))]
  exact tsub_le_tsub hm ha

/-- A lower bound on the mass of accepted answers bounds the expected bill even when a
trial can abort. The mass and price obligations apply at reached states. -/
theorem expectedCharge_collect_le_of_accept (c : P.A → S → ℝ≥0∞) (hc : ∀ a, Measurable (c a))
    (I : ℕ → X → S → Prop) (p C : ℕ → ℝ≥0∞) (hI : StagesPreserve K act accept I)
    (ha : ∀ i x s, I (i + 1) x s → p i ≤ K (act i x) s {z | (accept i x z.1).isSome})
    (hm : ∀ i x s, I (i + 1) x s → K (act i x) s Set.univ ≤ 1)
    (hprice : ∀ i x s, I (i + 1) x s → c (act i x) s ≤ C i)
    (post : X → S → ℝ≥0∞) (hpost : ∀ x, Measurable (post x)) (B : ℝ≥0∞)
    (hfinish : ∀ x s, I 0 x s → post x s ≤ B) (k : ℕ) (x : X) (s : S) (hs : I k x s) :
    expectedCharge K c (collect act accept k x) post s ≤ (∑ i ∈ Finset.range k, C i / p i) + B :=
  expectedCharge_collect_le K act accept c hc I p C
    (fun i x s h => (reject_le_of_accept_ge K (hm i x s h) (ha i x s h)).1) hI
    (fun i x s h => (reject_le_of_accept_ge K (hm i x s h) (ha i x s h)).2)
    hm hprice post hpost B hfinish k x s hs

/-- Exact acceptance probabilities and prices on each reached, lossless trial determine the
expected charge of all stages. -/
theorem expectedCharge_collect_eq_of_accept (c : P.A → S → ℝ≥0∞) (hc : ∀ a, Measurable (c a))
    (I : ℕ → X → S → Prop) (p C : ℕ → ℝ≥0∞) (hp : ∀ i x s, I (i + 1) x s → 0 < p i)
    (hI : StagesPreserve K act accept I)
    (ha : ∀ i x s, I (i + 1) x s → K (act i x) s {z | (accept i x z.1).isSome} = p i)
    (hm : ∀ i x s, I (i + 1) x s → K (act i x) s Set.univ = 1)
    (hprice : ∀ i x s, I (i + 1) x s → c (act i x) s = C i)
    (post : X → S → ℝ≥0∞) (hpost : ∀ x, Measurable (post x)) (B : ℝ≥0∞)
    (hfinish : ∀ x s, I 0 x s → post x s = B) (k : ℕ) (x : X) (s : S) (hs : I k x s) :
    expectedCharge K c (collect act accept k x) post s = (∑ i ∈ Finset.range k, C i / p i) + B := by
  have hle i x s (h : I (i + 1) x s) :=
    (measure_mono (μ := K (act i x) s) (Set.subset_univ {z | (accept i x z.1).isSome})).trans_eq
      (hm i x s h)
  apply expectedCharge_collect_eq K act accept c hc I p C
    (fun i x s h => ⟨hp i x s h, ha i x s h ▸ hle i x s h⟩) hI _ hm hprice post hpost B
    hfinish k x s hs
  intro i x s h
  rw [rejectMass_eq_sub_acceptMass K (act i x) (accept i x) s
    (ne_top_of_le_ne_top ENNReal.one_ne_top (hle i x s h)), hm i x s h, ha i x s h]

end

/-- Positive stage-wise acceptance bounds imply total return mass one when each reached attempt
has unit mass. -/
theorem returnedKernel_collect_univ_of_accept (I : ℕ → X → S → Prop) (p : ℕ → ℝ≥0∞)
    (hp : ∀ i x s, I (i + 1) x s → 0 < p i) (hI : StagesPreserve K act accept I)
    (ha : ∀ i x s, I (i + 1) x s → p i ≤ K (act i x) s {z | (accept i x z.1).isSome})
    (hm : ∀ i x s, I (i + 1) x s → K (act i x) s Set.univ = 1)
    (k : ℕ) (x : X) (s : S) (hs : I k x s) :
    returnedKernel K (collect act accept k x) s Set.univ = 1 :=
  returnedKernel_collect_univ K act accept I p (fun i x s h =>
    ⟨hp i x s h, (reject_le_of_accept_ge K (hm i x s h).le (ha i x s h)).1⟩) hI
    (fun i x s h => (reject_le_of_accept_ge K (hm i x s h).le (ha i x s h)).2) hm k x s hs

end PFunctor.Resumption.Collect
