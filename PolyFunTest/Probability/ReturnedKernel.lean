/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import Examples.Tutorials.ExpectedRetry
public import PolyFun.PFunctor.Resumption.Measure

/-!
# Terminal observations under abort and infinite cost

These tests compare the returned law and the cost of reaching a request independently.
-/

public section

open MeasureTheory ProbabilityTheory PFunctor PFunctor.Resumption
open scoped ENNReal

namespace PolyFunTest.Probability.ReturnedKernel

/-- A single operation returning no information. -/
abbrev Tick := monomial Unit Unit

private def once (result : Bool) : FreeM Tick Bool :=
  FreeM.liftBind () fun _ => pure result

private noncomputable def live : KernelHandler Tick Unit :=
  fun _ => Kernel.deterministic (fun s => ((), s)) (measurable_const.prodMk measurable_id)

private theorem returned_once (b : Bool) :
    returnedKernel live (once b).toResumption () = Measure.dirac (b, ()) := by
  rw [returnedKernel_toResumption live (once b), once, FreeM.runKernel_liftBind live]
  simp only [live, Kernel.deterministic_apply, FreeM.runKernel_pure]
  exact Measure.dirac_bind (Measure.measurable_dirac.comp
    (measurable_const.prodMk measurable_snd) : Measurable fun out : Unit × Unit =>
      Measure.dirac (b, out.2)) _

private theorem infinite_tick (b : Bool) (post : Bool → Unit → ℝ≥0∞) :
    expectedCharge live (fun _ _ => ⊤) (once b).toResumption post () = ⊤ := by
  rw [expectedCharge_toResumption live _ (fun _ => measurable_const) _ post
    (fun _ => Measurable.of_discrete), once, FreeM.wpFold_liftBind]
  simp

example : (∀ post : Bool → Unit → ℝ≥0∞,
    expectedCharge live (fun _ _ => ⊤) (once true).toResumption post () =
    expectedCharge live (fun _ _ => ⊤) (once false).toResumption post ()) ∧
    returnedKernel live (once true).toResumption () ≠
      returnedKernel live (once false).toResumption () := by
  refine ⟨fun post => (infinite_tick true post).trans (infinite_tick false post).symm, ?_⟩
  rw [returned_once, returned_once]
  intro h
  have he := congrArg (fun μ : Measure (Bool × Unit) => μ {(true, ())}) h
  simp at he

private abbrev Halt := monomial Unit Empty

private def blocked : FreeM Halt Unit := FreeM.liftBind () Empty.elim

example : expectedCharge (S := Unit) 0 (fun _ _ => 3) blocked.toResumption (fun _ _ => 0) () = 3 ∧
    returnedKernel (S := Unit) 0 blocked.toResumption () = 0 := by
  constructor
  · rw [expectedCharge_toResumption (P := Halt) (S := Unit) 0 (fun _ _ => 3)
      (fun _ => measurable_const) blocked (fun _ _ => 0) (fun _ => measurable_const),
      blocked, FreeM.wpFold_liftBind]
    simp
  · rw [returnedKernel_toResumption (S := Unit) 0 blocked, blocked,
      FreeM.runKernel_liftBind (P := Halt) (S := Unit) 0]
    simp

open PolyFunExamples.ExpectedRetry PFunctor.Resumption.Retry

private noncomputable abbrev trials : KernelHandler Trial ℕ := fun _ => fresh

private def retryThen (b : Bool) : Resumption Trial Bool :=
  Resumption.bind tree (fun _ => Resumption.pure b)

private theorem retry_mass : returnedKernel trials tree 0 Set.univ = 1 := by
  rw [← lintegral_one, ← expectedCharge_zero_eq_lintegral trials tree _ measurable_const]
  exact fresh_success 0

/-- Each program returns its chosen Boolean with probability one. -/
private theorem retryThen_result (b : Bool) :
    (returnedKernel trials (retryThen b) 0).map Prod.fst = Measure.dirac b := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf measurable_fst, lintegral_dirac' _ hf,
    ← expectedCharge_zero_eq_lintegral trials (retryThen b) (fun z => f z.1)
      (hf.comp measurable_fst) 0, retryThen,
    expectedCharge_bind trials 0 (fun _ => measurable_const) tree _ _
      (fun _ => Measurable.of_discrete)]
  simp only [expectedCharge_pure]
  change expectedCharge trials 0 tree (Function.curry (fun _ => f b)) 0 = f b
  rw [expectedCharge_zero_eq_lintegral trials tree _ measurable_const, lintegral_const, retry_mass,
    mul_one]

private theorem retryThen_charge (b : Bool) :
    expectedCharge trials (fun _ i => 2 ^ i) (retryThen b) (fun _ _ => 0) 0 = ∞ := by
  rw [retryThen, expectedCharge_bind trials _ (fun _ => Measurable.of_discrete)
    tree _ (fun _ _ => 0) (fun _ => measurable_const)]
  simpa only [expectedCharge_pure] using fresh_doubling_cost

/-- Every request has finite price. Both choices return almost surely, yet scalar cost
observations agree for every measurable postcost and the two terminal laws differ. -/
example :
    (∀ i : ℕ, (2 : ℝ≥0∞) ^ i < ∞) ∧
    (∀ b, (returnedKernel trials (retryThen b) 0).map Prod.fst = Measure.dirac b) ∧
    (∀ f : Bool × ℕ → ℝ≥0∞, Measurable f →
      expectedCharge trials (fun _ i => 2 ^ i) (retryThen true) (Function.curry f) 0 =
      expectedCharge trials (fun _ i => 2 ^ i) (retryThen false) (Function.curry f) 0) ∧
    returnedKernel trials (retryThen true) 0 ≠ returnedKernel trials (retryThen false) 0 := by
  refine ⟨fun i => ENNReal.pow_lt_top (by norm_num), retryThen_result, ?_, ?_⟩
  · apply (expectedCharge_ext_iff trials trials _ _ _ _ 0 0).2
    exact ⟨(retryThen_charge true).trans (retryThen_charge false).symm,
      .inl (retryThen_charge true)⟩
  · intro h
    have he := congrArg (fun μ : Measure (Bool × ℕ) => μ.map Prod.fst) h
    rw [retryThen_result, retryThen_result] at he
    have ht := congrArg (fun μ : Measure Bool => μ {true}) he
    simp at ht

end PolyFunTest.Probability.ReturnedKernel
