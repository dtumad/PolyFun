/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.ITree.Measure
public import PolyFun.ITree.WP.Basic

/-!
# Expected incurred charge as a total weakest precondition

With free silent steps, pointwise evaluation of the measurable cost semantics gives the
least-fixed-point reading on all state functions. The two fixed points live in different
orders: measurable expectations admit increasing countable suprema, while the space used
by the weakest precondition admits arbitrary suprema.
-/

public section

open MeasureTheory ProbabilityTheory OmegaCompletePartialOrder PFunctor
open PFunctor.Resumption (MeasurableExpectation statefulExpectedChargeAlgebra)
open scoped ENNReal

namespace ITree

universe u v

private theorem map_fix_eq_lfp {D L : Type*} [OmegaCompletePartialOrder D] [OrderBot D]
    [CompleteLattice L] (f : D →𝒄 D) (g : L →o L) (h : D → L)
    (chainSup : ∀ ch : Chain D, h (ωSup ch) = ⨆ n, h (ch n)) (strict : h ⊥ = ⊥)
    (comm : ∀ x, h (f x) = g (h x)) : h f.fix = g.lfp := by
  apply le_antisymm
  · apply f.fix_induction (fun x => h x ≤ g.lfp)
    · simp only [strict, bot_le]
    · intro x hx
      simpa only [comm, g.map_lfp] using g.monotone hx
    · intro ch hch
      rw [chainSup]
      exact iSup_le hch
  · apply g.lfp_le_fixed
    rw [← comm, f.map_fix]

/-- An observation preserving bottom and increasing suprema takes a continuous interpretation
to the total weakest precondition if it commutes with each visible operation. -/
theorem observe_denote_eq_wpTotal {P : PFunctor.{u, v}} {R D L : Type*}
    [OmegaCompletePartialOrder D] [OrderBot D] [CompleteLattice L]
    (alg : Resumption.ContinuousAlgebra P D) (Φ : OpSpec P L) (hΦ : Φ.Monotone)
    (observe : D → L) (strict : observe ⊥ = ⊥)
    (chainSup : ∀ ch : Chain D, observe (ωSup ch) = ⨆ n, observe (ch n))
    (atQuery : ∀ a (k : P.B a → D), observe (alg a k) = Φ a (observe ∘ k))
    (post : R → D) (tree : ITree P R) :
    observe (denote post alg tree) = wpTotal Φ tree (observe ∘ post) := by
  rw [denote_eq_fix, wpTotal_eq_lfp hΦ]
  let read (k : ITree P R → D) (t : ITree P R) := observe (k t)
  have eq := map_fix_eq_lfp (domainStep post alg) (wpStep hΦ (observe ∘ post)) read
    (fun ch => by
      funext t
      change observe (ωSup (ch.map (Pi.evalOrderHom t))) = _
      simp only [chainSup, iSup_apply]
      rfl)
    (funext fun _ => strict)
    (fun k => by
      funext t
      change observe (match shape' t with
        | ⟨.pure r, _⟩ => post r
        | ⟨.step, next⟩ => k (next PUnit.unit)
        | ⟨.query a, next⟩ => alg a (fun b => k (next b))) = wpLayer _ _ _ (shape' t)
      rcases shape' t with ⟨_ | _ | a, next⟩
      · rfl
      · rfl
      · exact atQuery a _)
  exact congrFun eq tree

/-- When silent steps cost zero, the total weakest precondition is the incurred expected
charge, including the terminal credit on returning paths. -/
theorem expectedCharge_eq_wpTotal {P : PFunctor.{u, v}} {S R : Type*}
    [MeasurableSpace S] [∀ a, MeasurableSpace (P.B a)]
    [∀ a, Countable (P.B a)] [∀ a, MeasurableSingletonClass (P.B a)]
    (K : P.KernelHandler S) (c : P.A → S → ℝ≥0∞) (hc : ∀ a, Measurable (c a))
    (tree : ITree P R) (post : R → MeasurableExpectation S) (s : S) :
    expectedCharge K c hc tree post s =
      wpTotal (OpSpec.statefulExpectedCharge K c) tree (fun r => (post r).1) s := by
  rw [expectedCharge_eq_denote]
  have eq := observe_denote_eq_wpTotal (statefulExpectedChargeAlgebra K c hc)
    (OpSpec.statefulExpectedCharge K c) (OpSpec.statefulExpectedCharge_mono K c)
    (fun f => f.1) rfl (fun _ => by funext t; simp [iSup_apply]; rfl)
    (fun _ _ => rfl) post tree
  exact congrFun eq s

end ITree
