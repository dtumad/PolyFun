/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Resumption.Measure.Collect
public import ToCslib.Probability.UniformOn
public import ToCslib.MeasureTheory.MeasurableSpace.Option
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card

/-!
# Collecting coupons in discovery order

Every draw returns a coupon. The collector appends an unseen coupon to the list and retries
after a duplicate. With fresh uniform draws on `Fin n`, the mean number of draws is `n` times
the `n`th harmonic number and the output is almost surely a permutation of all coupons.
-/

public section

open MeasureTheory ProbabilityTheory PFunctor PFunctor.Resumption
open scoped ENNReal

namespace PolyFunExamples.CouponCollector

/-- One request for a coupon from a population of size `n`. -/
abbrev Draw (n : ℕ) := monomial Unit (Fin n)

/-- Read a fresh, uniform coupon on every call. -/
noncomputable def fresh (n : ℕ) : KernelHandler (Draw n) Unit :=
  KernelHandler.ofMeasure fun _ => uniformOn Set.univ

/-- Keep the coupons in discovery order. A duplicate leaves the stage pending. -/
def accept {n : ℕ} (seen : List (Fin n)) (b : Fin n) : Option (List (Fin n)) :=
  if b ∈ seen then none else some (seen ++ [b])

/-- At a stage with `k` discoveries outstanding, exactly `n - k` distinct coupons are present. -/
def Valid {n : ℕ} (k : ℕ) (seen : List (Fin n)) : Prop :=
  seen.Nodup ∧ seen.length + k = n

private theorem valid_accept {n k : ℕ} {seen out : List (Fin n)} {b : Fin n}
    (h : Valid (k + 1) seen) (hb : accept seen b = some out) : Valid k out := by
  simp only [accept] at hb
  split at hb
  · contradiction
  · rename_i hnew
    cases hb
    constructor
    · have hd (a : Fin n) (ha : a ∈ seen) : a ≠ b := fun e => hnew (e ▸ ha)
      simpa [List.nodup_append, h.1] using hd
    · have := h.2
      simp only [List.length_append, List.length_singleton]
      omega

private theorem unseen_card {n k : ℕ} {seen : List (Fin n)} (h : Valid k seen) :
    (Finset.univ.filter (fun b : Fin n => b ∉ seen)).card = k := by
  classical
  have he : Finset.univ.filter (fun b : Fin n => b ∉ seen) = seen.toFinsetᶜ := by ext; simp
  rw [he, Finset.card_compl, Fintype.card_fin, List.toFinset_card_of_nodup h.1]
  have := h.2
  omega

/-- The new-coupon probability is the number of unseen coupons divided by the population. -/
theorem fresh_success_mass {n k : ℕ} {seen : List (Fin n)} (h : Valid k seen) (s : Unit) :
    fresh n () s {z | (accept seen z.1).isSome} = (k : ℝ≥0∞) / n := by
  change ((uniformOn Set.univ : Measure (Fin n)).map (fun b => (b, ())))
    {z | (accept seen z.1).isSome} = _
  rw [Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete]
  have he : (fun b : Fin n => (b, ())) ⁻¹' {z | (accept seen z.1).isSome} = {b | b ∉ seen} := by
    ext b
    simp [accept]
  rw [he, uniformOn_univ_apply_setOf, unseen_card h, Fintype.card_fin]

private instance (n : Nat) [NeZero n] (a : (Draw n).A) : IsMarkovKernel (fresh n a) where
  isProbabilityMeasure s := by
    change IsProbabilityMeasure ((uniformOn Set.univ : Measure (Fin n)).map (fun b => (b, ())))
    infer_instance


private theorem valid_perm {n : ℕ} {seen : List (Fin n)} (h : Valid 0 seen) :
    seen.Perm (List.finRange n) := by
  have hall : seen.toFinset = Finset.univ := Finset.eq_univ_of_card _ (by
    simpa [List.toFinset_card_of_nodup h.1] using h.2)
  apply (List.perm_ext_iff_of_nodup h.1 (List.nodup_finRange _)).2
  intro b
  have hb : b ∈ seen.toFinset := hall ▸ Finset.mem_univ b
  simp [List.mem_toFinset.mp hb]

private theorem harmonic_sum (n : ℕ) :
    (∑ i ∈ Finset.range n, (1 : ℝ≥0∞) / ((i + 1 : ℕ) / (n : ℝ≥0∞))) =
      n * ∑ i ∈ Finset.range n, (1 : ℝ≥0∞) / (i + 1 : ℕ) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [one_div, ENNReal.inv_div (.inl (ENNReal.natCast_ne_top _)) (.inr (by positivity))]
  simp [div_eq_mul_inv]

private theorem stage_mass {n k : ℕ} {seen : List (Fin n)} (h : Valid (k + 1) seen) (s : Unit) :
    fresh n () s Set.univ = 1 := by
  have hs := h.2
  have : NeZero n := ⟨by omega⟩
  exact measure_univ

/-- The same client runs on any service for drawing coupons. -/
def program (n : ℕ) : Resumption (Draw n) (List (Fin n)) :=
  Collect.collect (fun _ _ => ()) (fun _ => accept) n []

private theorem preserves (n : ℕ) : Collect.StagesPreserve (fresh n) (fun _ _ => ())
    (fun _ => accept) (fun k seen _ => Valid k seen) := by
  intro i seen s h
  apply Filter.Eventually.of_forall
  intro z
  change (accept seen z.1).elim (Valid (i + 1) seen) (Valid i)
  cases hb : accept seen z.1 with
  | none => exact h
  | some out => exact valid_accept h hb

private theorem valid_nil (n : ℕ) : Valid n ([] : List (Fin n)) := ⟨by simp, by simp⟩

/-- The expected number of draws to obtain every coupon is `n` times the harmonic sum. -/
theorem expected_draws (n : ℕ) :
    expectedCharge (fresh n) (fun _ _ => 1) (program n) (fun _ _ => 0) () =
      n * ∑ i ∈ Finset.range n, (1 : ℝ≥0∞) / (i + 1 : ℕ) := by
  rw [← harmonic_sum]
  simpa [program] using Collect.expectedCharge_collect_eq_of_accept (fresh n) (fun _ _ => ())
    (fun _ => accept) (fun _ _ => 1) (fun _ => measurable_const) (fun k seen _ => Valid k seen)
    (fun i => (i + 1 : ℕ) / (n : ℝ≥0∞)) (fun _ => 1)
    (fun _ _ _ _ => ENNReal.div_pos (by positivity) (ENNReal.natCast_ne_top _)) (preserves n)
    (fun _ _ s h => fresh_success_mass h s) (fun _ _ s h => stage_mass h s) (by simp)
    (fun _ _ => 0) (fun _ => measurable_const) 0 (by simp) n [] () (valid_nil n)

/-- Fresh draws deliver a full list with probability one, also for an empty population. -/
theorem returned_mass (n : ℕ) [MeasurableSpace (List (Fin n))] :
    returnedKernel (fresh n) (program n) () Set.univ = 1 :=
  Collect.returnedKernel_collect_univ_of_accept (fresh n) (fun _ _ => ()) (fun _ => accept)
    (fun k seen _ => Valid k seen) (fun i => (i + 1 : ℕ) / (n : ℝ≥0∞))
    (fun _ _ _ _ => ENNReal.div_pos (by positivity) (ENNReal.natCast_ne_top _)) (preserves n)
    (fun _ _ s h => (fresh_success_mass h s).ge)
    (fun _ _ s h => stage_mass h s) n [] () (valid_nil n)

/-- The output contains every coupon exactly once, in its order of discovery. -/
theorem returned_perm (n : ℕ) [MeasurableSpace (List (Fin n))]
    [MeasurableSingletonClass (List (Fin n))] :
    ∀ᵐ z ∂returnedKernel (fresh n) (program n) (), z.1.Perm (List.finRange n) :=
  (Collect.ae_returnedKernel_collect (fresh n) (fun _ _ => ()) (fun _ => accept)
    (fun k seen _ => Valid k seen) (preserves n) MeasurableSet.of_discrete n [] ()
    (valid_nil n)).mono fun _ => valid_perm

/-- The concrete examples observe arbitrary sets of coupon lists. -/
local instance instListFinMeasurableSpace (n : ℕ) : MeasurableSpace (List (Fin n)) := ⊤

/-- An empty collection returns immediately and pays no charge. -/
theorem empty_population :
    expectedCharge (fresh 0) (fun _ _ => 1) (program 0) (fun _ _ => 0) () = 0 ∧
      returnedKernel (fresh 0) (program 0) () = Measure.dirac ([], ()) := by
  simp [program]

/-- The service draws a uniform coupon on its first request and replays it thereafter. -/
noncomputable def cached : KernelHandler (Draw 2) (Option (Fin 2)) := fun _ =>
  Kernel.ofFunOfCountable fun state => match state with
    | none => (uniformOn Set.univ : Measure (Fin 2)).map (fun b => (b, some b))
    | some b => Measure.dirac (b, some b)

private theorem cached_last (b : Fin 2) (c : ℝ≥0∞) (post : List (Fin 2) → Option (Fin 2) → ℝ≥0∞) :
    expectedCharge cached (fun _ _ => c)
      (Collect.collect (P := Draw 2) (fun _ _ => ()) (fun _ => accept) 1 [b]) post (some b) =
        ⨆ i : ℕ, i * c := by
  rw [Collect.collect_succ, expectedCharge_bind cached _ (fun _ => measurable_const) _ _ post
    (fun _ => Measurable.of_discrete), Collect.expectedCharge_retry (P := Draw 2) cached]
  simp only [Collect.collect_zero, expectedCharge_pure]
  apply iSup_congr
  intro n
  induction n with
  | zero => simp [Collect.observe]
  | succ n ih =>
    rw [Collect.observe.eq_def (P := Draw 2)]
    change c + (∫⁻ z, (accept [b] z.1).elim _ _ ∂Measure.dirac (b, some b)) = _
    simp [lintegral_dirac, accept, ih, Nat.cast_succ, add_mul, add_comm]

private theorem cached_value (c : ℝ≥0∞) (post : List (Fin 2) → Option (Fin 2) → ℝ≥0∞) :
    expectedCharge cached (fun _ _ => c) (program 2) post none = c + ⨆ i : ℕ, i * c := by
  rw [program, Collect.collect_succ, expectedCharge_bind cached _ (fun _ => measurable_const)
    _ _ post (fun _ => Measurable.of_discrete), Collect.retry_eq_query,
    expectedCharge_query cached _ (fun _ => measurable_const) _ _ _
      (fun _ => Measurable.of_discrete)]
  congr 1
  change (∫⁻ z, _ ∂((uniformOn Set.univ : Measure (Fin 2)).map (fun b => (b, some b)))) = _
  rw [lintegral_map Measurable.of_discrete Measurable.of_discrete]
  simp [accept, expectedCharge_pure, cached_last]

/-- Two distinct coupons cannot be collected from a service that replays its first draw.
Every trial costs one, so the infinite retries have infinite expected cost. -/
theorem cached_failure :
    returnedKernel cached (program 2) none = 0 ∧
      expectedCharge cached (fun _ _ => 1) (program 2) (fun _ _ => 0) none = ∞ := by
  constructor
  · apply Measure.measure_univ_eq_zero.mp
    rw [← lintegral_one, ← expectedCharge_zero_eq_lintegral cached _ _ measurable_const]
    change expectedCharge cached (fun _ _ => 0) (program 2) (fun _ _ => 1) none = 0
    simpa using cached_value 0 (fun _ _ => 1)
  · simpa [ENNReal.iSup_natCast] using cached_value 1 (fun _ _ => 0)

end PolyFunExamples.CouponCollector
