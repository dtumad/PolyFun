/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Resumption.Measure.Collect

/-!
# Per-stage fuel converges to the unbounded collector

When each stage receives the same finite fuel, every finite sequence of accepted attempts
eventually fits. With zero terminal credit on exhaustion, these increasing observations recover
the expected charge of the unbounded program, including cost on paths that never complete.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PFunctor.Resumption.Collect

variable {P : PFunctor} {X S : Type*} [∀ a, MeasurableSpace (P.B a)] [MeasurableSpace S]
  (K : KernelHandler P S) (c : P.A → S → ℝ≥0∞)

/-- The bounded program executes exactly the finite stage observation with a zero cutoff. -/
theorem wpFold_retryWithin (a : P.A) (accept : P.B a → Option X) (post : X → S → ℝ≥0∞)
    (n : ℕ) (s : S) :
    FreeM.wpFold (OpSpec.statefulExpectedCharge K c) (retryWithin a accept n)
      (fun r t => r.elim 0 (fun x => post x t)) s = observe K a accept (c a) post n s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    rw [retryWithin_succ, FreeM.wpFold_liftBind, OpSpec.statefulExpectedCharge_apply, observe]
    congr 1
    apply lintegral_congr
    intro z
    cases h : accept z.1 <;> simp [ih]

private theorem observe_mono_post (a : P.A) (accept : P.B a → Option X) {f g : X → S → ℝ≥0∞}
    (h : ∀ x s, f x s ≤ g x s) (n : ℕ) (s : S) :
    observe K a accept (c a) f n s ≤ observe K a accept (c a) g n s := by
  induction n generalizing s with
  | zero => exact le_rfl
  | succ n ih =>
    simp only [observe]
    apply add_le_add_right
    apply lintegral_mono
    intro z
    dsimp only
    cases h' : accept z.1 with
    | none => exact ih z.2
    | some x => exact h x z.2

private theorem observe_mono_fuel (a : P.A) (accept : P.B a → Option X) (f : X → S → ℝ≥0∞)
    (s : S) : Monotone fun n => observe K a accept (c a) f n s := by
  apply monotone_nat_of_le_succ
  intro n
  induction n generalizing s with
  | zero => exact bot_le
  | succ n ih =>
    simp only [observe]
    apply add_le_add_right
    apply lintegral_mono
    intro z
    dsimp only
    cases h : accept z.1 with
    | none => exact ih z.2
    | some _ => exact le_rfl

variable (act : ℕ → X → P.A) (accept : (i : ℕ) → (x : X) → P.B (act i x) → Option X)

/-- The bounded program earns its terminal credit only on a completed collection. -/
noncomputable abbrev boundedCharge (post : X → S → ℝ≥0∞) (n k : ℕ) (x : X) (s : S) :=
  FreeM.wpFold (OpSpec.statefulExpectedCharge K c) (collectWithin act accept n k x)
    (fun r t => r.elim 0 (fun y => post y t)) s

@[simp] theorem boundedCharge_zero (post : X → S → ℝ≥0∞) (n : ℕ) (x : X) (s : S) :
    boundedCharge K c act accept post n 0 x s = post x s := rfl

theorem boundedCharge_succ (post : X → S → ℝ≥0∞) (n k : ℕ) (x : X) (s : S) :
    boundedCharge K c act accept post n (k + 1) x s =
      observe K (act k x) (accept k x) (c (act k x))
        (boundedCharge K c act accept post n k) n s := by
  rw [boundedCharge, collectWithin_succ, FreeM.wpFold_bind']
  rw [← wpFold_retryWithin K c]
  apply congrArg (fun f => FreeM.wpFold (OpSpec.statefulExpectedCharge K c)
    (retryWithin (act k x) (accept k x) n) f s)
  funext r t
  cases r <;> rfl

/-- More fuel at each stage increases every bounded observation. -/
theorem monotone_boundedCharge (post : X → S → ℝ≥0∞) (k : ℕ) (x : X) (s : S) :
    Monotone fun n => boundedCharge K c act accept post n k x s := by
  intro m n h
  dsimp only
  induction k generalizing x s with
  | zero => exact le_rfl
  | succ k ih =>
    rw [boundedCharge_succ, boundedCharge_succ]
    exact (observe_mono_post K c _ _ ih _ _).trans (observe_mono_fuel K c _ _ _ s h)

variable [∀ a, Countable (P.B a)] [∀ a, MeasurableSingletonClass (P.B a)]

private theorem measurable_observe (hc : ∀ a, Measurable (c a)) (a : P.A)
    (accept : P.B a → Option X) (f : X → S → ℝ≥0∞) (hf : ∀ x, Measurable (f x)) (n : ℕ) :
    Measurable (observe K a accept (c a) f n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    apply (hc a).add (Measurable.lintegral_kernel _)
    apply measurable_from_prod_countable_right
    intro b
    cases h : accept b with
    | none => simpa [h] using ih
    | some x => simpa [h] using hf x

private theorem observe_iSup_post (hc : ∀ a, Measurable (c a)) (a : P.A) (accept : P.B a → Option X)
    (f : ℕ → X → S → ℝ≥0∞) (hf : ∀ n x, Measurable (f n x))
    (hm : ∀ x s, Monotone (fun n => f n x s))
    (j : ℕ) (s : S) :
    observe K a accept (c a) (fun x t => ⨆ n, f n x t) j s =
      ⨆ n, observe K a accept (c a) (f n) j s := by
  induction j generalizing s with
  | zero => simp [observe]
  | succ j ih =>
    simp only [observe]
    have ht (z : P.B a × S) : (accept z.1).elim
        (observe K a accept (c a) (fun x t => ⨆ n, f n x t) j z.2) (fun x => ⨆ n, f n x z.2) =
        ⨆ n, (accept z.1).elim (observe K a accept (c a) (f n) j z.2) (fun x => f n x z.2) := by
      cases h : accept z.1 <;> simp [ih]
    simp_rw [ht]
    rw [lintegral_iSup, ENNReal.add_iSup]
    · intro n
      apply measurable_from_prod_countable_right
      intro b
      cases h : accept b with
      | none => simpa [h] using measurable_observe K c hc a accept (f n) (hf n) j
      | some x => simpa [h] using hf n x
    · intro m n h z
      dsimp only
      cases hh : accept z.1 with
      | none => exact observe_mono_post K c _ _ (fun x t => hm x t h) j z.2
      | some x => exact hm x z.2 h

/-- A single increasing fuel shared across all stages recovers the expected cost and
terminal observation of the unbounded collector. No losslessness hypothesis is required. -/
theorem expectedCharge_collect_eq_iSup_boundedCharge (hc : ∀ a, Measurable (c a))
    (post : X → S → ℝ≥0∞) (hp : ∀ x, Measurable (post x)) (k : ℕ) (x : X) (s : S) :
    expectedCharge K c (collect act accept k x) post s =
      ⨆ n, boundedCharge K c act accept post n k x s := by
  induction k generalizing x s with
  | zero => simp
  | succ k ih =>
    rw [collect_succ, expectedCharge_bind K c hc _ _ _ hp, expectedCharge_retry]
    have hi (y : X) : expectedCharge K c (collect act accept k y) post =
        fun t => ⨆ n, boundedCharge K c act accept post n k y t := funext (ih y)
    simp_rw [hi]
    have hf (n : ℕ) (x : X) : Measurable (boundedCharge K c act accept post n k x) := by
      apply FreeM.measurable_wpFold_statefulExpectedCharge K c hc
      rintro (_ | y)
      · exact measurable_const
      · exact hp y
    simp_rw [observe_iSup_post K c hc _ _ _ hf (monotone_boundedCharge K c act accept post k)]
    simp only [boundedCharge_succ]
    apply le_antisymm
    · refine iSup_le fun j => iSup_le fun n => ?_
      refine le_trans ?_ (le_iSup _ (max j n))
      refine (observe_mono_post K c _ _ (fun y t => monotone_boundedCharge K c act accept post k y t
        (le_max_right j n)) _ _).trans ?_
      exact observe_mono_fuel K c _ _ _ s (le_max_left j n)
    · refine iSup_le fun n => le_trans ?_ (le_iSup _ n)
      exact le_iSup (fun m => observe K (act k x) (accept k x) (c (act k x))
        (boundedCharge K c act accept post m k) n s) n

end PFunctor.Resumption.Collect
