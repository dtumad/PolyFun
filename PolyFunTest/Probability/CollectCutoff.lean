/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Resumption.Measure.CollectCutoff

/-!
# A single attempt budget for collecting fresh successes

The truncated program is observed directly. With fresh Bernoulli trials its unfinished mass
is exactly the binomial lower tail. One stage recovers the geometric retry tail.
-/

public section

open MeasureTheory ProbabilityTheory PFunctor PFunctor.Resumption Collect
open scoped ENNReal

namespace PolyFunTest.Probability.CollectCutoff

abbrev Trial : PFunctor.{0, 0} := ⟨Unit, fun _ => Bool⟩

def act (_ : ℕ) (_ : Unit) : Trial.A := ()

def accept (_ : ℕ) (_ : Unit) : Bool → Option Unit
  | false => none
  | true => some ()

noncomputable def trials (p : Set.Icc (0 : ℝ) 1) : KernelHandler Trial Unit :=
  fun _ => Kernel.const Unit (bernoulliMeasure (true, ()) (false, ()) p)

private theorem fresh (p : Set.Icc (0 : ℝ) 1) (n k : ℕ) :
    cutoff act accept (trials p) n k () () = binomialTail (ENNReal.ofReal p) n k := by
  apply cutoff_eq_binomialTail act accept (trials p) (fun _ _ _ => True)
    (fun _ _ _ _ _ => Filter.Eventually.of_forall fun z => by cases z.1 <;> trivial)
    (ENNReal.ofReal_le_one.mpr p.2.2) _ _ n trivial
  · intro i hi x s _
    change bernoulliMeasure (true, ()) (false, ()) p {z | accept i x z.1 = none} = _
    rw [bernoulliMeasure_apply_of_notMem_of_mem p (Set.to_countable _).measurableSet
      (by simp [accept]) (by simp [accept])]
    rw [← ENNReal.ofReal_coe_nnreal, unitInterval.coe_toNNReal, unitInterval.coe_symm_eq,
      ENNReal.ofReal_sub _ p.2.1, ENNReal.ofReal_one]
  · intro i hi x s _
    change bernoulliMeasure (true, ()) (false, ()) p Set.univ = 1
    exact measure_univ

/-- The event of a cutoff after `n` total attempts is the event of fewer than `k` heads. -/
theorem fresh_return_cutoff (p : Set.Icc (0 : ℝ) 1) (n k : ℕ) :
    FreeM.runKernel (trials p) (truncate n (collect act accept k ())) () {z | z.1 = none} =
      binomial n p (Set.Iio k) := by
  rw [← cutoff_eq_runKernel, fresh, binomialTail_eq_binomial]

example (p : Set.Icc (0 : ℝ) 1) (n : ℕ) :
    cutoff act accept (trials p) n 1 () () = (1 - ENNReal.ofReal p) ^ n := by
  rw [fresh, binomialTail_one_stage]

/-- One attempt can never finish two stages, even at success probability one. -/
example : cutoff act accept (trials 1) 1 2 () () = 1 := by
  rw [fresh, binomialTail_succ]
  simp

/-- With two required successes and three fair trials the global cutoff has mass one half. -/
example :
    cutoff act accept (trials ⟨1 / 2, by norm_num⟩) 3 2 () () = (2 : ℝ≥0∞)⁻¹ := by
  rw [fresh]
  norm_num [binomialTail_succ, binomialTail_one_stage, ENNReal.ofReal_div_of_pos]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  repeat first | rw [ENNReal.toReal_add (by finiteness) (by finiteness)] | rw [ENNReal.toReal_mul]
  norm_num

private noncomputable def lossy : KernelHandler Trial Unit := fun _ =>
  Kernel.const Unit ((2 : ℝ≥0∞)⁻¹ • Measure.dirac (true, ()))

/-- Half the mass returns immediately and half is lost. No branch reaches the second attempt,
and the mass that completed the stage is one half. -/
example :
    cutoff act accept lossy 2 1 () () = 0 ∧
      returnedKernel lossy (collect act accept 1 ()) () Set.univ = (2 : ℝ≥0∞)⁻¹ := by
  constructor
  · rw [cutoff_succ]
    simp [lossy, lintegral_smul_measure, lintegral_dirac, accept]
  · rw [collect_succ_eq_query, returnedKernel_query (P := Trial)]
    rw [Measure.bind_apply MeasurableSet.univ Measurable.of_discrete.aemeasurable]
    simp [lossy, lintegral_smul_measure, lintegral_dirac, accept]

end PolyFunTest.Probability.CollectCutoff
