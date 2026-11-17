/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Mathlib.Analysis.Calculus.FDeriv.Congr

/-!
# Derivatives on a finite family of cells

A derivative at a point can be checked on finitely many cells whose union contains a neighborhood.
Only cells with that point in their closure contribute. For closed cells with unique derivatives,
this gives a criterion expressed in terms of the derivatives of locally agreeing branches.
-/

public section

namespace Examples.FiniteCellDerivative

open Filter Set
open scoped Topology

variable {𝕜 E F ι : Type*} [NontriviallyNormedField 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]
  {f : E → F} {D : E →L[𝕜] F} {x : E}

private theorem hasFDerivWithinAt_finsetUnion (s : Finset ι) (cell : ι → Set E)
    (h : ∀ i ∈ s, HasFDerivWithinAt f D (cell i) x) :
    HasFDerivWithinAt f D (⋃ i ∈ s, cell i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.set_biUnion_insert]
    exact (h i (by simp)).union (ih fun j hj => h j (by simp [hj]))

/-- A local finite cover detects the derivative on just those cells accumulating at the point. -/
theorem hasFDerivAt_iff_of_finiteCover (s : Finset ι) (cell : ι → Set E)
    (hcover : (⋃ i ∈ s, cell i) ∈ 𝓝 x) :
    HasFDerivAt f D x ↔ ∀ i ∈ s, x ∈ closure (cell i) → HasFDerivWithinAt f D (cell i) x := by
  refine ⟨fun h _ _ _ => h.hasFDerivWithinAt, fun h => ?_⟩
  apply (hasFDerivWithinAt_finsetUnion s cell _).hasFDerivAt hcover
  intro i hi
  by_cases hx : x ∈ closure (cell i)
  · exact h i hi hx
  · exact HasFDerivWithinAt.empty.mono_of_mem_nhdsWithin (by
      simp [notMem_closure_iff_nhdsWithin_eq_bot.mp hx])

variable [ContinuousAdd E] [ContinuousSMul 𝕜 E]
  [ContinuousAdd F] [ContinuousSMul 𝕜 F] [T2Space F]

/-- On cells that are closed at the point and admit unique derivatives there, the derivative of
the assembled map is precisely the common derivative of the active branches. -/
theorem hasFDerivAt_iff_activeBranches (s : Finset ι) (cell : ι → Set E)
    (hcover : (⋃ i ∈ s, cell i) ∈ 𝓝 x)
    (hclosed : ∀ i ∈ s, x ∈ closure (cell i) → x ∈ cell i)
    (branch : ι → E → F) (derivative : ι → E →L[𝕜] F)
    (hbranch : ∀ i ∈ s, x ∈ cell i → HasFDerivWithinAt (branch i) (derivative i) (cell i) x)
    (hagrees : ∀ i ∈ s, x ∈ cell i → f =ᶠ[𝓝[cell i] x] branch i)
    (hunique : ∀ i ∈ s, x ∈ cell i → UniqueDiffWithinAt 𝕜 (cell i) x) :
    HasFDerivAt f D x ↔ ∀ i ∈ s, x ∈ cell i → derivative i = D := by
  have hcell (i : ι) (hi : i ∈ s) (hx : x ∈ cell i) :
      HasFDerivWithinAt f (derivative i) (cell i) x :=
    ((hagrees i hi hx).hasFDerivWithinAt_iff_of_mem hx).mpr (hbranch i hi hx)
  constructor
  · intro h i hi hx
    exact (hunique i hi hx).eq (hcell i hi hx) h.hasFDerivWithinAt
  · intro h
    apply (hasFDerivAt_iff_of_finiteCover s cell hcover).mpr
    intro i hi hcl
    have hx := hclosed i hi hcl
    exact (hcell i hi hx).congr_fderiv (h i hi hx)

end Examples.FiniteCellDerivative
