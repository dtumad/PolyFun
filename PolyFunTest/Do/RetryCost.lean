/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Resumption.Measure.CollectLimit
public import PolyFun.PFunctor.Free.Do
public import PolyFun.ITree.WP.ExpectedCharge
public import PolyFun.ITree.WP.Upstream
import PolyFun.PFunctor.Free.Measure.FiniteKernel

/-!
# Stateful retry budgets through core verification conditions

A list cursor records the remaining fuel. At each trial the potential may depend on the private
state, and an accepted answer receives its own terminal credit. The core loop rule reduces
the proof to the supplied one-trial inequality.
-/

public section

open Std.WP OrderDual PFunctor PFunctor.FreeM Resumption.Collect MeasureTheory ProbabilityTheory
open scoped ENNReal

set_option experimental.vcgen true

namespace PolyFunTest.Do.RetryCost

variable {P : PFunctor.{0, 0}} {S X : Type}

private def retryStep (a : P.A) (accept : P.B a → Option X) (_ : Unit) :
    Option X → FreeM P (ForInStep (Option X))
  | some x => pure (.done (some x))
  | none => do
    let b ← FreeM.lift (P := P) a
    pure (match accept b with | none => .yield none | some x => .done (some x))

private theorem forIn_retryStep (a : P.A) (accept : P.B a → Option X) (xs : List Unit) :
    forIn (m := FreeM P) xs none (retryStep a accept) = retryWithin a accept xs.length := by
  induction xs with
  | nil => simp
  | cons u xs ih =>
    simp only [List.forIn_cons, retryStep, List.length_cons, retryWithin_succ, bind_assoc]
    rw [FreeM.liftBind_eq]
    congr 1
    funext b
    cases accept b <;> simp [ih]

variable [MeasurableSpace S] [∀ a, MeasurableSpace (P.B a)]
  (K : P.KernelHandler S) (c : P.A → S → ℝ≥0∞)

private noncomputable abbrev meter :
    WPMonad (FreeM P) (S → ℝ≥0∞)ᵒᵈ EStack⟨⟩ᵒᵈ :=
  (OpSpec.statefulExpectedCharge K c).toUpperWPMonad (OpSpec.statefulExpectedCharge_mono K c)


/-- A potential indexed by the remaining trials bounds a finite retry with credit on success. -/
theorem retryWithin_le (a : P.A) (accept : P.B a → Option X) (V : ℕ → S → ℝ≥0∞)
    (post : X → S → ℝ≥0∞)
    (round : ∀ n s, c a s + ∫⁻ z, (accept z.1).elim (V n z.2) (fun x => post x z.2) ∂K a s ≤
      V (n + 1) s) (n : ℕ) (s : S) :
    wpFold (OpSpec.statefulExpectedCharge K c) (retryWithin a accept n)
      (fun r t => r.elim 0 (fun x => post x t)) s ≤ V n s := by
  let _ := meter K c
  let xs := List.replicate n ()
  have ht : ⦃ toDual (V xs.length) ⦄ forIn (m := FreeM P) xs none (retryStep a accept)
      ⦃ fun r => toDual (fun t => r.elim 0 (fun x => post x t)) ⦄ := by
    vcgen [retryStep] invariants
      · fun _ suff r => toDual (fun t => r.elim (V suff.length t) (fun x => post x t))
    case vc1 => rfl
    case vc2 r =>
      cases r with
      | none => exact fun _ => zero_le
      | some x => rfl
    case vc3 => simp_all
    case vc4 pref cur suff eqxs r hr =>
      subst r
      simp only [Lean.Order.rel_eq_le, toDual_le_toDual, Option.elim_none, List.length_cons,
        binderNameHint, OpSpec.toUpperWPMonad_wp, wpFold_pure, ofDual_toDual]
      intro t
      rw [OpSpec.statefulExpectedCharge_apply]
      refine le_trans (le_of_eq ?_) (round suff.length t)
      congr 1
      apply lintegral_congr
      intro z
      cases hb : accept z.1 <;> rfl
  have he := ht.1 s
  rw [OpSpec.toUpperWPMonad_wp, forIn_retryStep] at he
  change wpFold (OpSpec.statefulExpectedCharge K c) (retryWithin a accept xs.length)
    (fun r t => r.elim 0 (fun x => post x t)) s ≤ V xs.length s at he
  simpa [xs] using he

/-- The same one-round certificate bounds all the finite approximants of the unbounded tree. -/
theorem retry_le_of_round (a : P.A) (accept : P.B a → Option X)
    (V : ℕ → S → ℝ≥0∞) (post : X → S → ℝ≥0∞)
    (round : ∀ n s, c a s + ∫⁻ z, (accept z.1).elim (V n z.2) (fun x => post x z.2) ∂K a s ≤
      V (n + 1) s) (s : S) :
    Resumption.expectedCharge K c (retry a accept) post s ≤ ⨆ n, V n s := by
  rw [expectedCharge_retry]
  apply iSup_mono
  intro n
  rw [← wpFold_retryWithin]
  exact retryWithin_le K c a accept V post round n s

/-- A state-dependent potential that covers the immediate expected cost and the residual
potential on retry bounds the unbounded program. -/
theorem retry_le_of_potential (a : P.A) (accept : P.B a → Option X)
    (V : S → ℝ≥0∞) (post : X → S → ℝ≥0∞)
    (round : ∀ s, c a s + ∫⁻ z, (accept z.1).elim (V z.2) (fun x => post x z.2) ∂K a s ≤
      V s) (s : S) :
    Resumption.expectedCharge K c (retry a accept) post s ≤ V s := by
  simpa using retry_le_of_round K c a accept (fun _ => V) post (fun _ => round) s

/-- With attempt price at most B and conditional retry mass at most 1-p, the verified
loop costs at most B/p. The kernel may lose mass on an attempt. -/
theorem retry_le_div [∀ a, Countable (P.B a)] [∀ a, MeasurableSingletonClass (P.B a)]
    (a : P.A) (accept : P.B a → Option X) (B p : ℝ≥0∞) (hp : p ≤ 1)
    (price : ∀ s, c a s ≤ B) (reject : ∀ s, K a s {z | accept z.1 = none} ≤ 1 - p) (s : S) :
    Resumption.expectedCharge K c (retry a accept) (fun _ _ => 0) s ≤ B / p := by
  let q := 1 - p
  let V (n : ℕ) := B * ∑ i ∈ Finset.range n, q ^ i
  have hm : MeasurableSet {z : P.B a × S | accept z.1 = none} :=
    measurable_fst (Set.to_countable {b : P.B a | accept b = none}).measurableSet
  apply (retry_le_of_round K c a accept (fun n _ => V n) (fun _ _ => 0) ?_ s).trans
  · refine iSup_le fun n => ?_
    have h := sum_le_tsum (f := fun i : ℕ => q ^ i) (Finset.range n)
    have hfin : q ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
    have hsub := (ENNReal.cancel_of_ne hfin).tsub_tsub_cancel_of_le hp
    simpa [V, q, ENNReal.tsum_geometric, hsub, div_eq_mul_inv] using mul_le_mul_right h B
  · intro n t
    have calcIntegral : (∫⁻ z, (accept z.1).elim (V n) (fun _ => 0) ∂K a t) =
        V n * K a t {z | accept z.1 = none} := by
      rw [← lintegral_indicator_const hm]
      apply lintegral_congr
      intro z
      cases h : accept z.1 <;> simp [Set.indicator, h]
    rw [calcIntegral]
    refine (add_le_add (price t) (mul_le_mul_right (reject t) (V n))).trans_eq ?_
    simp only [V, geom_sum_succ, mul_add, mul_one, q]
    ac_rfl

private abbrev Trial := Resumption.Retry.Trial

/-- A cold trial costs two, rejects and warms the service. A warm trial costs one and
succeeds. A single state-dependent potential certifies both initial budgets. -/
example (warm : Bool) :
    let K : KernelHandler Trial Bool :=
      KernelHandler.ofFun (fun _ s => (s, true)) (fun _ => Measurable.of_discrete)
    let c : Trial.A → Bool → ℝ≥0∞ := fun _ s => if s then 1 else 2
    Resumption.expectedCharge K c (retry () (fun b : Bool => if b then some () else none))
      (fun _ _ => 0) warm ≤ if warm then 1 else 3 := by
  intro service price
  apply retry_le_of_potential service price () _ (fun s => if s then 1 else 3) (fun _ _ => 0)
  intro s
  cases s <;> norm_num [service, price, KernelHandler.ofFun, Kernel.deterministic_apply]

/-- The dual total-correctness interpretation states the incurred budget at every initial state. -/
example [∀ a, Countable (P.B a)] [∀ a, MeasurableSingletonClass (P.B a)]
    (hc : ∀ a, Measurable (c a)) (tree : ITree P X)
    (post : X → Resumption.MeasurableExpectation S) (budget : S → ℝ≥0∞) :
    letI := ITree.wpMonadTotal (OpSpec.statefulExpectedCharge K c)
      (OpSpec.statefulExpectedCharge_mono K c)
    letI : WPMonad (ITree P) (S → ℝ≥0∞)ᵒᵈ EStack⟨⟩ᵒᵈ := ExactWPMonad.dual
    (⦃ toDual budget ⦄ tree ⦃ fun x => toDual (post x).1 ⦄) ↔
      ∀ s, ITree.expectedCharge K c hc tree post s ≤ budget s := by
  let _ := ITree.wpMonadTotal (OpSpec.statefulExpectedCharge K c)
    (OpSpec.statefulExpectedCharge_mono K c)
  let _ : WPMonad (ITree P) (S → ℝ≥0∞)ᵒᵈ EStack⟨⟩ᵒᵈ := ExactWPMonad.dual
  simp only [ITree.expectedCharge_eq_wpTotal]
  constructor
  · intro h
    have le := h.1
    change ((ITree.wpMonadTotal (OpSpec.statefulExpectedCharge K c)
      (OpSpec.statefulExpectedCharge_mono K c)).toWP _).wp tree (fun x => (post x).1) () ≤
      budget at le
    rwa [ITree.wpMonadTotal_wp] at le
  · intro h
    refine ⟨?_⟩
    change ((ITree.wpMonadTotal (OpSpec.statefulExpectedCharge K c)
      (OpSpec.statefulExpectedCharge_mono K c)).toWP _).wp tree (fun x => (post x).1) () ≤ budget
    rwa [ITree.wpMonadTotal_wp]

/-! ## An already-initialized service skips its setup request -/

abbrev Tick : PFunctor.{0, 0} := ⟨Unit, fun _ => Unit⟩

private def twice : Handler.Stateful (FreeM Tick) Unit Tick := fun _ => StateT.mk fun s => do
  let _ ← FreeM.lift (P := Tick) ()
  let _ ← FreeM.lift (P := Tick) ()
  pure ((), s)

private def setup : Handler.Stateful (FreeM Tick) Bool Tick := fun _ => StateT.mk fun ready => do
  if ready then pure ((), true)
  else
    let _ ← FreeM.lift (P := Tick) ()
    pure ((), true)

private noncomputable abbrev charge : OpSpec Tick ℝ≥0∞ :=
  OpSpec.expectedCharge (fun _ => Measure.dirac ()) (fun _ => 1)

private noncomputable abbrev tickMeter : WPMonad (FreeM Tick) ℝ≥0∞ᵒᵈ EStack⟨⟩ᵒᵈ :=
  charge.toUpperWPMonad (OpSpec.expectedCharge_mono _ _)

attribute [local instance] tickMeter

/-- A pair of linked requests incurs one setup charge when cold and zero when warm. -/
example (ready : Bool) :
    ⦃ toDual (if ready then 0 else (1 : ℝ≥0∞)) ⦄
      (twice.link setup).run (FreeM.lift (P := Tick) ()) ((), ready)
    ⦃ fun (_ : Unit × Unit × Bool) => toDual (0 : ℝ≥0∞) ⦄ := by
  have run : (twice.link setup).run (FreeM.lift (P := Tick) ()) ((), ready) =
      (if ready then pure ((), (), true) else do
        let _ ← FreeM.lift (P := Tick) ()
        pure ((), (), true)) := by
    rw [Handler.Stateful.run_link]
    cases ready <;> rfl
  rw [run]
  cases ready
  · change ⦃ toDual (1 : ℝ≥0∞) ⦄ (do
        let _ ← FreeM.lift (P := Tick) ()
        pure ((), (), true) : FreeM Tick (Unit × Unit × Bool)) ⦃ fun _ => toDual (0 : ℝ≥0∞) ⦄
    vcgen
    simp [Lean.Order.rel_eq_le, binderNameHint, expected_cost]
  · change ⦃ toDual (0 : ℝ≥0∞) ⦄ (pure ((), (), true) : FreeM Tick (Unit × Unit × Bool))
      ⦃ fun _ => toDual (0 : ℝ≥0∞) ⦄
    vcgen

end PolyFunTest.Do.RetryCost
