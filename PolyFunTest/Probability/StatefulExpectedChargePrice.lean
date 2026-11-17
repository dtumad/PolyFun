/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Free.Measure.StatefulExpectedChargePrice

/-!
# Expected prices and correlation

A measured fair coin generates two resources. In one reading they are incurred together and
in another they are mutually exclusive. Every nonnegative linear price has the same expectation
in both readings, while the event that both resources cost one distinguishes them.
-/

public section

open MeasureTheory ProbabilityTheory PFunctor PFunctor.FreeM
open scoped ENNReal

namespace PolyFunTest.Probability.ExpectedChargePrice

abbrev Coin : PFunctor.{0, 0} := ⟨Unit, fun _ => Bool⟩

private noncomputable def coin : KernelHandler Coin Unit :=
  fun _ => Kernel.const _ ((2 : ℝ≥0∞)⁻¹ • (Measure.dirac (true, ()) + Measure.dirac (false, ())))

private def bitCost (b : Bool) : ℝ≥0∞ := if b then 1 else 0

private def together (_ : Bool) (b : Bool) (_ : Unit) : ℝ≥0∞ := bitCost b

private def apart (i b : Bool) (_ : Unit) : ℝ≥0∞ := bitCost (i == b)

private noncomputable abbrev readCost (post : Bool → Unit → ℝ≥0∞) :=
  wpFold (OpSpec.statefulExpectedCharge coin (fun _ _ => 0)) (FreeM.lift ()) post ()

private theorem price_eq (p : Bool → ℝ≥0∞) (f : Bool → Bool → Unit → ℝ≥0∞) :
    readCost (fun r s => priceHom p bot_le (fun i => f i r s)) =
      priceHom p bot_le (fun i => readCost (f i)) := by
  simpa [readCost] using wpFold_statefulExpectedCharge_price coin p (fun _ _ _ => 0)
    (fun _ _ => measurable_const) (FreeM.lift ()) f (fun _ _ => Measurable.of_discrete) ()

example (p : Bool → ℝ≥0∞) :
    readCost (fun r s => priceHom p bot_le (fun i => together i r s)) =
      readCost (fun r s => priceHom p bot_le (fun i => apart i r s)) := by
  rw [price_eq, price_eq]
  congr 1
  funext i
  cases i <;> simp [readCost, coin, together, apart, bitCost]

example :
    readCost (fun b s => together true b s * together false b s) = 2⁻¹ ∧
    readCost (fun b s => apart true b s * apart false b s) = 0 := by
  simp [readCost, coin, together, apart, bitCost]

end PolyFunTest.Probability.ExpectedChargePrice
