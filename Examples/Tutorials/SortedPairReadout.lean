/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Linear
public import Mathlib.Topology.Algebra.Module.Equiv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Calculus.TangentCone.Real

/-!
# Differentiating a readout after sorting two real coordinates

At a tie, either ordering can hold at nearby points. A differentiable readout of the two
coordinates stays differentiable after sorting exactly when its derivative at the tie is
unchanged by swapping the coordinates. For the scalar readout that assigns weights to the
smaller and larger values, this condition says that the two weights agree.
-/

public section

namespace Examples.SortedPairReadout

open Set

/-- Put the smaller of the two real coordinates first. -/
@[expose] def sorted (x : ℝ × ℝ) : ℝ × ℝ := (min x.1 x.2, max x.1 x.2)

private theorem uniqueDiff_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f g : E →L[ℝ] ℝ) (x y : E) (hx : f x ≤ g x) (hy : f y < g y) :
    UniqueDiffWithinAt ℝ {z | f z ≤ g z} x := by
  apply uniqueDiffWithinAt_convex _ _ (subset_closure (show x ∈ {z | f z ≤ g z} from hx))
  · intro u hu v hv a b ha hb _
    change f (a • u + b • v) ≤ g (a • u + b • v)
    simpa using add_le_add (mul_le_mul_of_nonneg_left hu ha) (mul_le_mul_of_nonneg_left hv hb)
  · exact ⟨y, interior_maximal (fun _ (hz : f _ < g _) => hz.le)
      (isOpen_lt f.continuous g.continuous) hy⟩

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {h : ℝ × ℝ → F} {D : (ℝ × ℝ) →L[ℝ] F} {c : ℝ}

/-- On a strictly increasing pair, the sorting permutation is locally the identity. -/
theorem hasFDerivAt_comp_sorted_of_fst_lt {x : ℝ × ℝ} (hx : x.1 < x.2)
    (hd : HasFDerivAt h D x) : HasFDerivAt (h ∘ sorted) D x := by
  apply hd.congr_of_eventuallyEq
  filter_upwards [continuous_fst.continuousAt.eventually_lt continuous_snd.continuousAt hx]
    with z hz
  simp [Function.comp_apply, sorted, min_eq_left hz.le, max_eq_right hz.le]

/-- On a strictly decreasing pair, the readout differentiates at the swapped input. -/
theorem hasFDerivAt_comp_sorted_of_snd_lt {x : ℝ × ℝ} (hx : x.2 < x.1)
    (hd : HasFDerivAt h D x.swap) :
    HasFDerivAt (h ∘ sorted) (D.comp (ContinuousLinearEquiv.prodComm ℝ ℝ ℝ).toContinuousLinearMap)
      x := by
  let swap := (ContinuousLinearEquiv.prodComm ℝ ℝ ℝ).toContinuousLinearMap
  have hs : HasFDerivAt (h ∘ swap) (D.comp swap) x :=
    (show HasFDerivAt h D (swap x) from hd).comp x swap.hasFDerivAt
  apply hs.congr_of_eventuallyEq
  filter_upwards [continuous_snd.continuousAt.eventually_lt continuous_fst.continuousAt hx]
    with z hz
  simp [Function.comp_apply, sorted, min_eq_right hz.le, max_eq_left hz.le, swap, Prod.swap]

/-- A proposed derivative of the sorted readout must agree with both ordering branches.
Either branch derivative is sufficient when the two coincide. -/
theorem hasFDerivAt_comp_sorted_iff (hd : HasFDerivAt h D (c, c)) (L : (ℝ × ℝ) →L[ℝ] F) :
    HasFDerivAt (h ∘ sorted) L (c, c) ↔
      L = D ∧ L = D.comp (ContinuousLinearEquiv.prodComm ℝ ℝ ℝ).toContinuousLinearMap := by
  let f := ContinuousLinearMap.fst ℝ ℝ ℝ
  let g := ContinuousLinearMap.snd ℝ ℝ ℝ
  let lower := {x : ℝ × ℝ | f x ≤ g x}
  let upper := {x : ℝ × ℝ | g x ≤ f x}
  let swap := (ContinuousLinearEquiv.prodComm ℝ ℝ ℝ).toContinuousLinearMap
  have hl : HasFDerivWithinAt (h ∘ sorted) D lower (c, c) := by
    apply HasFDerivWithinAt.congr' (s := lower) hd.hasFDerivWithinAt _
      (show f (c, c) ≤ g (c, c) from le_rfl)
    intro z (hz : z.1 ≤ z.2)
    simp [Function.comp_apply, sorted, min_eq_left hz, max_eq_right hz]
  have hu : HasFDerivWithinAt (h ∘ sorted) (D.comp swap) upper (c, c) := by
    have hs : HasFDerivAt (h ∘ swap) (D.comp swap) (c, c) :=
      (show HasFDerivAt h D (swap (c, c)) from hd).comp (c, c) swap.hasFDerivAt
    apply HasFDerivWithinAt.congr' (s := upper) hs.hasFDerivWithinAt _
      (show g (c, c) ≤ f (c, c) from le_rfl)
    intro z (hz : z.2 ≤ z.1)
    simp [Function.comp_apply, sorted, min_eq_right hz, max_eq_left hz, swap, Prod.swap]
  constructor
  · intro hs
    exact ⟨(uniqueDiff_le f g (c, c) (0, 1) le_rfl (by norm_num [f, g])).eq
        hs.hasFDerivWithinAt hl,
      (uniqueDiff_le g f (c, c) (1, 0) le_rfl (by norm_num [f, g])).eq hs.hasFDerivWithinAt hu⟩
  · rintro ⟨rfl, hswap⟩
    have cover : lower ∪ upper = univ :=
      Set.eq_univ_of_forall (fun z => le_total (f z) (g z))
    exact hasFDerivWithinAt_univ.mp (cover ▸ hl.union (hswap ▸ hu))

/-- At equal coordinates, sorting preserves differentiability of a readout exactly when
its derivative is invariant under the coordinate swap. -/
theorem differentiableAt_comp_sorted_iff (hd : DifferentiableAt ℝ h (c, c)) :
    DifferentiableAt ℝ (h ∘ sorted) (c, c) ↔
      fderiv ℝ h (c, c) = (fderiv ℝ h (c, c)).comp
        (ContinuousLinearEquiv.prodComm ℝ ℝ ℝ).toContinuousLinearMap := by
  constructor
  · intro hs
    obtain ⟨he, hs⟩ := (hasFDerivAt_comp_sorted_iff hd.hasFDerivAt _).mp hs.hasFDerivAt
    exact he.symm.trans hs
  · intro hs
    exact ((hasFDerivAt_comp_sorted_iff hd.hasFDerivAt _).mpr ⟨rfl, hs⟩).differentiableAt

/-! ## Weighted readouts -/

/-- The linear readout of coordinates in their given order. -/
noncomputable def weightedCoords (u v : ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  u • ContinuousLinearMap.fst ℝ ℝ ℝ + v • ContinuousLinearMap.snd ℝ ℝ ℝ

@[simp] theorem weightedCoords_apply (u v : ℝ) (x : ℝ × ℝ) :
    weightedCoords u v x = u * x.1 + v * x.2 := by
  simp [weightedCoords]

private theorem weightedCoords_comp_swap (u v : ℝ) :
    (weightedCoords u v).comp (ContinuousLinearEquiv.prodComm ℝ ℝ ℝ).toContinuousLinearMap =
      weightedCoords v u := by
  apply ContinuousLinearMap.ext
  intro x
  simp [Prod.swap, add_comm]

/-- Apply weights `u` and `v` to the smaller and larger coordinates, respectively. -/
noncomputable def readout (u v : ℝ) : ℝ × ℝ → ℝ := weightedCoords u v ∘ sorted

@[simp] theorem readout_apply (u v : ℝ) (x : ℝ × ℝ) :
    readout u v x = u * min x.1 x.2 + v * max x.1 x.2 := by
  simp [readout, sorted]

/-- Equal weights make the readout agree globally with the unsorted linear map. -/
theorem readout_self (u : ℝ) : readout u u = weightedCoords u u := by
  funext x
  rcases le_total x.1 x.2 with h | h
  · simp [min_eq_left h, max_eq_right h]
  · simp [min_eq_right h, max_eq_left h, add_comm]

/-- A strictly increasing input retains the two derivative weights in their given order. -/
theorem hasFDerivAt_readout_of_fst_lt (u v : ℝ) {x : ℝ × ℝ} (hx : x.1 < x.2) :
    HasFDerivAt (readout u v) (weightedCoords u v) x :=
  hasFDerivAt_comp_sorted_of_fst_lt hx (weightedCoords u v).hasFDerivAt

/-- A strictly decreasing input reverses the two derivative weights. -/
theorem hasFDerivAt_readout_of_snd_lt (u v : ℝ) {x : ℝ × ℝ} (hx : x.2 < x.1) :
    HasFDerivAt (readout u v) (weightedCoords v u) x := by
  rw [← weightedCoords_comp_swap]
  exact hasFDerivAt_comp_sorted_of_snd_lt hx (weightedCoords u v).hasFDerivAt

/-- At a tie the readout is differentiable exactly when its two weights agree. -/
theorem differentiableAt_readout_tie_iff (u v c : ℝ) :
    DifferentiableAt ℝ (readout u v) (c, c) ↔ u = v := by
  rw [readout, differentiableAt_comp_sorted_iff (weightedCoords u v).differentiableAt,
    (weightedCoords u v).fderiv, weightedCoords_comp_swap]
  constructor
  · intro h
    simpa using DFunLike.congr_fun h ((1, 0) : ℝ × ℝ)
  · rintro rfl
    rfl

end Examples.SortedPairReadout
