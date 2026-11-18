/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Resumption.Measure
import ToCslib.MeasureTheory.Integral.Lebesgue.Subprobability

/-!
# Accumulated resources on unbounded runs

A nondecreasing meter in the private state records resources on each returned run. Its
expected terminal value agrees with the initial value plus incurred cost at every state
of almost-sure return, even when the expected cost is infinite.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PFunctor.Resumption

variable {P : PFunctor} {S α : Type*} [MeasurableSpace S] [MeasurableSpace α]
  [∀ a, MeasurableSpace (P.B a)] [∀ a, Countable (P.B a)]
  [∀ a, MeasurableSingletonClass (P.B a)]
  (K : KernelHandler P S) (c : P.A → S → ℝ≥0∞) (V : S → ℝ≥0∞) (hV : Measurable V)

include hV in
/-- A local upper bound on the increase of a meter bounds its expected terminal value.
The argument allows missing mass and infinite charges. -/
theorem lintegral_meter_le_expectedCharge
    (hstep : ∀ a s, ∫⁻ z, V z.2 ∂K a s ≤ c a s + V s)
    (x : Resumption P α) (s : S) :
    ∫⁻ z, V z.2 ∂returnedKernel K x s ≤ expectedCharge K c x (fun _ _ => 0) s + V s := by
  rw [← expectedCharge_zero_eq_lintegral K x (fun z => V z.2) (hV.comp measurable_snd)]
  change expectedCharge K 0 x (fun _ t => V t) s ≤ _
  simpa only [zero_add] using expectedCharge_le_of_potential K c 0 (fun _ => True) V hV
    (fun _ _ _ => Filter.Eventually.of_forall fun _ => trivial)
    (fun a t _ => by simpa using hstep a t) x (fun _ _ => 0) (s := s) trivial

variable (hgrow : ∀ a s, ∀ᵐ z ∂K a s, V s ≤ V z.2)

include hgrow in
private theorem meter_mul_fold_le {β : Type*}
    (x : FreeM P β) (f : β → S → ℝ≥0∞) (hf : ∀ b, Measurable (f b)) (s : S) :
    V s * FreeM.wpFold (OpSpec.statefulExpectedCharge K 0) x f s ≤
      FreeM.wpFold (OpSpec.statefulExpectedCharge K 0) x (fun b t => V t * f b t) s := by
  induction x using FreeM.rec generalizing s with
  | pure => exact le_rfl
  | liftBind a k ih =>
    simp only [FreeM.wpFold_liftBind, OpSpec.statefulExpectedCharge_apply, Pi.zero_apply, zero_add]
    rw [← lintegral_const_mul _ (measurable_from_prod_countable_right fun b =>
      FreeM.measurable_wpFold_statefulExpectedCharge K _ (fun _ => measurable_const) (k b) hf)]
    apply lintegral_mono_ae
    filter_upwards [hgrow a s] with z hz
    exact (mul_le_mul_of_nonneg_right hz zero_le).trans (ih z.1 z.2)

include hV hgrow in
/-- Each returned execution carries at least its initial meter value. -/
theorem meter_mul_returnMass_le_lintegral (x : Resumption P α) (s : S) :
    V s * returnedKernel K x s Set.univ ≤ ∫⁻ z, V z.2 ∂returnedKernel K x s := by
  rw [← lintegral_one, ← expectedCharge_zero_eq_lintegral K x _ measurable_const,
    ← expectedCharge_zero_eq_lintegral K x (fun z => V z.2) (hV.comp measurable_snd)]
  simp only [expectedCharge_eq_iSup, ENNReal.mul_iSup]
  apply iSup_mono
  intro n
  let f (r : Option α) := r.elim (fun _ : S => (0 : ℝ≥0∞)) (fun _ _ => 1)
  have h := meter_mul_fold_le K V hgrow (truncate n x) f
    (fun r => by cases r <;> exact measurable_const) s
  have eq : (fun r : Option α => r.elim (fun _ : S => (0 : ℝ≥0∞)) (fun _ => V)) =
      (fun b t => V t * f b t) := by
    funext r t
    cases r <;> simp [f]
  change V s * FreeM.wpFold _ _ f s ≤ FreeM.wpFold _ _
    (fun r : Option α => r.elim (fun _ : S => (0 : ℝ≥0∞)) (fun _ => V)) s
  rw [eq]
  exact h

variable [∀ a, IsSubprobabilityKernel (K a)]

private theorem full_query {a : P.A} {k : P.B a → Resumption P α} {s : S}
    (h : returnedKernel K (query a k) s Set.univ = 1) :
    K a s Set.univ = 1 ∧ ∀ᵐ z ∂K a s, returnedKernel K (k z.1) z.2 Set.univ = 1 := by
  have hm : Measurable (fun z : P.B a × S => returnedKernel K (k z.1) z.2) :=
    measurable_from_prod_countable_right fun b => (returnedKernel K (k b)).measurable
  rw [returnedKernel_query, Measure.bind_apply MeasurableSet.univ hm.aemeasurable] at h
  have hle (z : P.B a × S) : returnedKernel K (k z.1) z.2 Set.univ ≤ 1 :=
    measure_univ_le _
  exact measure_univ_eq_one_and_ae_eq_one_of_lintegral_eq_one hle h

include hV hgrow in
/-- At an initial state of full return mass, every incurred charge is present on the
completed runs. Local prices only need to be exact at operations of full mass. -/
theorem lintegral_meter_eq_expectedCharge_of_returnMass
    (hstep : ∀ a s, ∫⁻ z, V z.2 ∂K a s ≤ c a s + V s)
    (hexact : ∀ a s, K a s Set.univ = 1 → ∫⁻ z, V z.2 ∂K a s = c a s + V s)
    (x : Resumption P α) (s : S) (hmass : returnedKernel K x s Set.univ = 1) :
    ∫⁻ z, V z.2 ∂returnedKernel K x s = expectedCharge K c x (fun _ _ => 0) s + V s := by
  apply le_antisymm (lintegral_meter_le_expectedCharge K c V hV hstep x s)
  rw [expectedCharge_eq_iSup, ENNReal.iSup_add]
  apply iSup_le
  intro n
  have hz : (fun r : Option α => r.elim (fun _ : S => (0 : ℝ≥0∞)) (fun _ _ => 0)) =
      (fun _ _ => 0) := by funext r; cases r <;> rfl
  simp only [hz]
  induction n generalizing x s with
  | zero =>
    have h := meter_mul_returnMass_le_lintegral K V hV hgrow x s
    rw [hmass, mul_one] at h
    rw [truncate_zero]
    split <;> simpa using h
  | succ n ih =>
    cases hx : dest x with
    | inl r =>
      have he : x = pure r := eq_of_dest_eq (by simpa using hx)
      subst x
      have hm : Measurable (fun z : α × S => V z.2) := hV.comp measurable_snd
      simp [lintegral_dirac' _ hm]
    | inr node =>
      obtain ⟨a, k⟩ := node
      have he : x = query a k := eq_of_dest_eq (by rw [dest_query]; exact hx)
      subst x
      obtain ⟨hone, hall⟩ := full_query K hmass
      have hmeas : Measurable (fun z : P.B a × S => returnedKernel K (k z.1) z.2) :=
        measurable_from_prod_countable_right fun b => (returnedKernel K (k b)).measurable
      have hout : Measurable (fun z : α × S => V z.2) := hV.comp measurable_snd
      have hin : Measurable (fun z : P.B a × S => V z.2) := hV.comp measurable_snd
      rw [truncate_query_succ, FreeM.wpFold_liftBind, OpSpec.statefulExpectedCharge_apply,
        returnedKernel_query, Measure.lintegral_bind hmeas.aemeasurable
          hout.aemeasurable, add_right_comm, ← hexact a s hone, add_comm,
          ← lintegral_add_right _ hin]
      exact lintegral_mono_ae (hall.mono fun z hz => ih (k z.1) z.2 hz)

end PFunctor.Resumption
