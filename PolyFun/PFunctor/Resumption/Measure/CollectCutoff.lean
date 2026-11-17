/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Resumption.Measure.Collect
public import Mathlib.Probability.Distributions.Binomial
public import ToCslib.MeasureTheory.MeasurableSpace.Option

/-!
# A global attempt budget for an adaptive collector

Each attempt either retries the current stage or advances to the next stage with a payload.
Truncating the actual collector counts attempts across stage boundaries. A uniform lower bound
on conditional success gives a binomial bound on the mass still running at the cutoff.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PFunctor.Resumption.Collect

private noncomputable def weight (p : ℝ≥0∞) (n j : ℕ) : ℝ≥0∞ :=
  n.choose j * p ^ j * (1 - p) ^ (n - j)

/-- The probability that fewer than `k` successes occur in `n` independent trials with
success probability `p ≤ 1`. -/
noncomputable def binomialTail (p : ℝ≥0∞) (n k : ℕ) : ℝ≥0∞ :=
  ∑ j ∈ Finset.range k, weight p n j

@[simp] theorem binomialTail_zero_stages (p : ℝ≥0∞) (n : ℕ) : binomialTail p n 0 = 0 := by
  simp [binomialTail]

@[simp] theorem binomialTail_zero_attempts (p : ℝ≥0∞) (k : ℕ) : binomialTail p 0 (k + 1) = 1 := by
  simp [binomialTail, Finset.sum_range_succ', weight]

@[simp] theorem binomialTail_one_stage (p : ℝ≥0∞) (n : ℕ) :
    binomialTail p n 1 = (1 - p) ^ n := by simp [binomialTail, weight]

private theorem weight_succ (p : ℝ≥0∞) (n j : ℕ) :
    weight p (n + 1) (j + 1) = (1 - p) * weight p n (j + 1) + p * weight p n j := by
  by_cases h : j < n
  · have he : n - j = n - (j + 1) + 1 := by omega
    simp only [weight, Nat.choose_succ_succ, Nat.cast_add, Nat.add_sub_add_right, pow_succ, he]
    ring
  · obtain hj | hj := lt_or_eq_of_le (Nat.le_of_not_gt h)
    · simp [weight, Nat.choose_eq_zero_of_lt (by omega : n + 1 < j + 1),
        Nat.choose_eq_zero_of_lt (by omega : n < j + 1), Nat.choose_eq_zero_of_lt hj]
    · subst j
      simp [weight, pow_succ, mul_comm]

/-- Pascal's recurrence splits an attempt into retrying and advancing one stage. -/
theorem binomialTail_succ (p : ℝ≥0∞) (n k : ℕ) :
    binomialTail p (n + 1) (k + 1) =
      (1 - p) * binomialTail p n (k + 1) + p * binomialTail p n k := by
  simp only [binomialTail, Finset.sum_range_succ', weight_succ, Finset.sum_add_distrib,
    ← Finset.mul_sum]
  simp [weight, pow_succ, mul_add]
  ring

/-- Identification with Mathlib's binomial distribution at the strict cutoff. -/
theorem binomialTail_eq_binomial (p : Set.Icc (0 : ℝ) 1) (n k : ℕ) :
    binomialTail (ENNReal.ofReal p) n k = binomial n p (Set.Iio k) := by
  have he : (Set.Iio k : Set ℕ) = (Finset.range k : Set ℕ) := by ext j; simp
  rw [he, ← sum_measure_singleton]
  apply Finset.sum_congr rfl
  intro j _
  rw [binomial_singleton, weight,
    ENNReal.ofReal_mul (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg p.2.1 _)),
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by exact p.2.1),
    ENNReal.ofReal_pow (sub_nonneg.mpr p.2.2), ENNReal.ofReal_sub _ p.2.1]
  simp

variable {P : PFunctor} {X S : Type*}
  (act : ℕ → X → P.A) (accept : (i : ℕ) → (x : X) → P.B (act i x) → Option X)

/-- A positive-stage collector performs exactly one request before either retrying or advancing. -/
theorem collect_succ_eq_query (k : ℕ) (x : X) :
    collect act accept (k + 1) x = query (act k x) (fun b =>
      (accept k x b).elim (collect act accept (k + 1) x) (collect act accept k)) := by
  conv_lhs => rw [collect_succ, retry_eq_query, bind_query]
  congr 1
  funext b
  cases accept k x b <;> simp [collect_succ]

variable [∀ a, MeasurableSpace (P.B a)] [MeasurableSpace S] (K : KernelHandler P S)

/-- Mass at the cutoff leaf of the program truncated after a single global budget of requests.
Branches that lose mass at a request contribute zero. -/
@[expose] noncomputable def cutoff (n k : ℕ) (x : X) (s : S) : ℝ≥0∞ :=
  FreeM.wpFold (OpSpec.statefulExpectedCharge K 0) (truncate n (collect act accept k x))
    (fun result _ => result.elim 1 (fun _ => 0)) s

@[simp] theorem cutoff_zero_stages (n : ℕ) (x : X) (s : S) :
    cutoff act accept K n 0 x s = 0 := by simp [cutoff]

@[simp] theorem cutoff_zero_attempts (k : ℕ) (x : X) (s : S) :
    cutoff act accept K 0 (k + 1) x s = 1 := by
  rw [cutoff, collect_succ_eq_query, truncate_query_zero]
  rfl

theorem cutoff_succ (n k : ℕ) (x : X) (s : S) :
    cutoff act accept K (n + 1) (k + 1) x s =
      ∫⁻ z, (accept k x z.1).elim (cutoff act accept K n (k + 1) x z.2)
        (fun y => cutoff act accept K n k y z.2) ∂K (act k x) s := by
  rw [cutoff, collect_succ_eq_query, truncate_query_succ, FreeM.wpFold_liftBind,
    OpSpec.statefulExpectedCharge_apply, Pi.zero_apply, Pi.zero_apply, zero_add]
  apply lintegral_congr
  intro z
  cases accept k x z.1 <;> simp [cutoff]

private theorem binomialTail_mono (p : ℝ≥0∞) (n k : ℕ) :
    binomialTail p n k ≤ binomialTail p n (k + 1) :=
  Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.le_succ k))

private theorem binomialTail_succ_diff {p : ℝ≥0∞} (hp : p ≤ 1) (n k : ℕ) :
    binomialTail p (n + 1) (k + 1) =
      (binomialTail p n (k + 1) - binomialTail p n k) * (1 - p) + binomialTail p n k := by
  rw [binomialTail_succ]
  let f := binomialTail p n (k + 1)
  let t := binomialTail p n k
  change (1 - p) * f + p * t = (f - t) * (1 - p) + t
  calc _ = (1 - p) * (f - t + t) + p * t := by rw [tsub_add_cancel_of_le (binomialTail_mono p n k)]
       _ = (f - t) * (1 - p) + t * ((1 - p) + p) := by ring
       _ = _ := by rw [tsub_add_cancel_of_le hp, mul_one]

variable [∀ a, Countable (P.B a)] [∀ a, MeasurableSingletonClass (P.B a)]

/-- The cutoff fold is the mass of the actual `none` result of the truncated collector.
A lost branch contributes to neither the returned nor the cutoff event. -/
theorem cutoff_eq_runKernel [MeasurableSpace X] (n k : ℕ) (x : X) (s : S) :
    cutoff act accept K n k x s =
      FreeM.runKernel K (truncate n (collect act accept k x)) s {z | z.1 = none} := by
  let prog := truncate n (collect act accept k x)
  let event := {z : Option X × S | z.1 = none}
  have he : MeasurableSet event := measurable_fst Option.measurableSet_none
  have hf : Measurable (event.indicator (1 : Option X × S → ℝ≥0∞)) := measurable_const.indicator he
  change FreeM.wpFold (OpSpec.statefulExpectedCharge K 0) prog _ s = FreeM.runKernel K prog s event
  rw [← returnedKernel_toResumption K prog, ← lintegral_indicator_one he,
    ← expectedCharge_zero_eq_lintegral K _ _ hf,
    expectedCharge_toResumption K 0 (fun _ => measurable_const) prog
      (Function.curry (event.indicator 1))
      (fun _ => hf.comp (measurable_const.prodMk measurable_id))]
  apply congrArg (fun post => FreeM.wpFold (OpSpec.statefulExpectedCharge K 0) prog post s)
  funext r t
  cases r <;> simp [event, Set.indicator, Function.curry]

private theorem integral_branch_diff {a : P.A} (read : P.B a → Option X) (s : S)
    {f t : ℝ≥0∞} (h : t ≤ f) :
    (∫⁻ z, (read z.1).elim f (fun _ => t) ∂K a s) =
      (f - t) * K a s {z | read z.1 = none} + t * K a s Set.univ := by
  have hm : MeasurableSet {z : P.B a × S | read z.1 = none} :=
    measurable_fst (Set.to_countable {b : P.B a | read b = none}).measurableSet
  rw [← lintegral_indicator_const hm, ← lintegral_const, ← lintegral_add_left
    (measurable_const.indicator hm)]
  apply lintegral_congr
  intro z
  cases hz : read z.1 <;> simp [Set.indicator, hz, tsub_add_cancel_of_le h]

variable {k : ℕ} {p : ℝ≥0∞} (I : ℕ → X → S → Prop)
  (hI : ∀ i < k, ∀ x, Preserves K (act i x) (accept i x) (I (i + 1) x) (I i))

include hI

/-- Bounding rejection by `1 - p` at every reached attempt bounds global cutoff mass by the
probability of fewer than `k` successes in `n` fresh trials. The private state and the next
stage may depend on the entire observed history. -/
theorem cutoff_le_binomialTail (hp : p ≤ 1)
    (hr : ∀ i < k, ∀ x s, I (i + 1) x s → K (act i x) s {z | accept i x z.1 = none} ≤ 1 - p)
    (hm : ∀ i < k, ∀ x s, I (i + 1) x s → K (act i x) s Set.univ ≤ 1)
    (n : ℕ) {x : X} {s : S} (hs : I k x s) :
    cutoff act accept K n k x s ≤ binomialTail p n k := by
  suffices ∀ i ≤ k, ∀ x s, I i x s → cutoff act accept K n i x s ≤ binomialTail p n i from
    this k le_rfl x s hs
  intro i hi x s hs
  induction n generalizing i x s with
  | zero => cases i <;> simp
  | succ n ih =>
    cases i with
    | zero => simp
    | succ i =>
      have hi' : i < k := by omega
      rw [cutoff_succ, binomialTail_succ_diff hp]
      calc _ ≤ ∫⁻ z, (accept i x z.1).elim (binomialTail p n (i + 1))
                    (fun _ => binomialTail p n i) ∂K (act i x) s := by
               apply lintegral_mono_ae
               filter_upwards [hI i hi' x s hs] with z hz
               cases h : accept i x z.1 with
               | none => exact ih _ hi _ _ (by simpa [h] using hz)
               | some y => exact ih _ hi'.le _ _ (by simpa [h] using hz)
           _ ≤ _ := by
               rw [integral_branch_diff K _ _ (binomialTail_mono p n i)]
               simpa using add_le_add (mul_le_mul_right (hr i hi' x s hs) _)
                 (mul_le_mul_right (hm i hi' x s hs) _)

/-- A lower bound on acceptance probability at every reached stage gives the usual binomial
cutoff bound under subprobability trials. -/
theorem cutoff_le_binomial (p : Set.Icc (0 : ℝ) 1)
    (ha : ∀ i < k, ∀ x s, I (i + 1) x s →
      ENNReal.ofReal p ≤ K (act i x) s {z | accept i x z.1 ≠ none})
    (hm : ∀ i < k, ∀ x s, I (i + 1) x s → K (act i x) s Set.univ ≤ 1)
    (n : ℕ) {x : X} {s : S} (hs : I k x s) :
    cutoff act accept K n k x s ≤ binomial n p (Set.Iio k) := by
  rw [← binomialTail_eq_binomial]
  have hp : ENNReal.ofReal p ≤ 1 := ENNReal.ofReal_le_one.mpr p.2.2
  apply cutoff_le_binomialTail act accept K I hI hp _ hm n hs
  intro i hi x s hs
  apply ENNReal.le_sub_of_add_le_right ENNReal.ofReal_ne_top
  have he : MeasurableSet {z : P.B (act i x) × S | accept i x z.1 = none} :=
    measurable_fst (Set.to_countable {b | accept i x b = none}).measurableSet
  exact (add_le_add_right (ha i hi x s hs) _).trans
    ((measure_add_measure_compl he).trans_le (hm i hi x s hs))

/-- For normalized trials with exact conditional success probability `p`, the finite cutoff
has exactly the binomial tail. This includes independent fresh draws at each request. -/
theorem cutoff_eq_binomialTail (hp : p ≤ 1)
    (hr : ∀ i < k, ∀ x s, I (i + 1) x s → K (act i x) s {z | accept i x z.1 = none} = 1 - p)
    (hm : ∀ i < k, ∀ x s, I (i + 1) x s → K (act i x) s Set.univ = 1)
    (n : ℕ) {x : X} {s : S} (hs : I k x s) :
    cutoff act accept K n k x s = binomialTail p n k := by
  suffices ∀ i ≤ k, ∀ x s, I i x s → cutoff act accept K n i x s = binomialTail p n i from
    this k le_rfl x s hs
  intro i hi x s hs
  induction n generalizing i x s with
  | zero => cases i <;> simp
  | succ n ih =>
    cases i with
    | zero => simp
    | succ i =>
      have hi' : i < k := by omega
      rw [cutoff_succ, binomialTail_succ_diff hp]
      calc _ = ∫⁻ z, (accept i x z.1).elim (binomialTail p n (i + 1))
                    (fun _ => binomialTail p n i) ∂K (act i x) s := by
               apply lintegral_congr_ae
               filter_upwards [hI i hi' x s hs] with z hz
               cases h : accept i x z.1 with
               | none => exact ih _ hi _ _ (by simpa [h] using hz)
               | some y => exact ih _ hi'.le _ _ (by simpa [h] using hz)
           _ = _ := by
               rw [integral_branch_diff K _ _ (binomialTail_mono p n i),
                 hr i hi' x s hs, hm i hi' x s hs, mul_one]

end PFunctor.Resumption.Collect
