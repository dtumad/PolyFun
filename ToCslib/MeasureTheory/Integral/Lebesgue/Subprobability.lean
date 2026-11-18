/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import ToCslib.MeasureTheory.Measure.Subprobability
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Full expectation under a subprobability measure

A weight bounded by one can have integral one only when the measure has full mass and the
weight itself is one almost everywhere.
-/

public section

open scoped ENNReal
namespace MeasureTheory

/-- Integral one under a subprobability forces total mass and almost-everywhere value one. -/
theorem measure_univ_eq_one_and_ae_eq_one_of_lintegral_eq_one
    {A : Type*} [MeasurableSpace A] {μ : Measure A}
    [IsSubprobabilityMeasure μ] {f : A → ℝ≥0∞} (hle : ∀ z, f z ≤ 1)
    (h : ∫⁻ z, f z ∂μ = 1) : μ Set.univ = 1 ∧ ∀ᵐ z ∂μ, f z = 1 := by
  have hμ : μ Set.univ = 1 := le_antisymm (measure_univ_le μ) (by
    rw [← h]
    simpa only [lintegral_one] using (lintegral_mono (μ := μ) hle))
  refine ⟨hμ, ae_eq_of_ae_le_of_lintegral_le (Filter.Eventually.of_forall hle)
    (by simp [h]) (g := fun _ => 1) aemeasurable_const ?_⟩
  simp only [lintegral_one, hμ, h, le_refl]

end MeasureTheory
