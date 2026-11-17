/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.Tutorials.FiniteCellDerivative
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Data.Fintype.Perm
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Comp

/-!
# Derivatives of sorted finite tuples

Sorting a tuple permutes its coordinates. At a tie several permutations give the same sorted
tuple. If the readout is differentiable there, its derivative must agree after precomposition
with each possible permutation for the sorted readout to have a derivative. A scalar weighted
readout satisfies this condition exactly when its weights agree
at ranks occupied by equal entries. The argument includes the empty tuple.
-/

public section

open Filter Set
open scoped Topology

namespace Examples.FiniteSortReadout

open Examples.FiniteCellDerivative

variable {n : Nat}

/-- Coordinates are weakly increasing in the order listed by the permutation. -/
def chamber (p : Equiv.Perm (Fin n)) : Set (Fin n → ℝ) := { x | Monotone (x ∘ p) }

/-- A chamber is closed because each of its coordinate comparisons is closed. -/
theorem isClosed_chamber (p : Equiv.Perm (Fin n)) : IsClosed (chamber p) := by
  change IsClosed ((fun x : Fin n → ℝ => x ∘ p) ⁻¹' {f : Fin n → ℝ | Monotone f})
  exact (isClosed_monotone (β := Fin n) (α := ℝ)).preimage
    (continuous_pi fun i => continuous_apply (p i))

/-- Convex combinations preserve the inequalities defining a chamber. -/
theorem convex_chamber (p : Equiv.Perm (Fin n)) : Convex ℝ (chamber p) := by
  intro x hx y hy a b ha hb _ i j hij
  exact add_le_add (mul_le_mul_of_nonneg_left (hx hij) ha) (mul_le_mul_of_nonneg_left (hy hij) hb)

private theorem eventually_strictMono (p : Equiv.Perm (Fin n)) {x : Fin n → ℝ}
    (hx : StrictMono (x ∘ p)) : ∀ᶠ y : Fin n → ℝ in 𝓝 x, StrictMono (y ∘ p) := by
  have hpair (i j : Fin n) : ∀ᶠ y : Fin n → ℝ in 𝓝 x, i < j → y (p i) < y (p j) := by
    by_cases hij : i < j
    · exact ((continuous_apply (p i)).continuousAt.eventually_lt
        (continuous_apply (p j)).continuousAt (hx hij)).mono fun _ hy _ => hy
    · exact .of_forall fun _ h => (hij h).elim
  have hall : ∀ᶠ y : Fin n → ℝ in 𝓝 x, ∀ i j : Fin n, i < j → y (p i) < y (p j) :=
    eventually_all.mpr fun i => eventually_all.mpr fun j => hpair i j
  exact hall.mono fun _ hy _ _ hij => hy _ _ hij

/-- A strict ordering determines the same sorting permutation throughout a neighborhood. -/
theorem eventually_sort_eq (p : Equiv.Perm (Fin n)) {x : Fin n → ℝ}
    (hx : StrictMono (x ∘ p)) : ∀ᶠ y in 𝓝 x, Tuple.sort y = p := by
  filter_upwards [eventually_strictMono p hx] with y hy
  refine (Tuple.eq_sort_iff.mpr ⟨hy.monotone, ?_⟩).symm
  exact fun _ _ _ h => (congrArg p (hy.injective h)).le

/-- Assigning each permuted coordinate its rank gives an interior point. -/
theorem interior_chamber_nonempty (p : Equiv.Perm (Fin n)) :
    (interior (chamber p)).Nonempty := by
  let x : Fin n → ℝ := fun i => ((p.symm i).val : ℝ)
  have hx : StrictMono (x ∘ p) := fun _ _ hij => by
    simpa [x] using (Nat.cast_lt.mpr hij : (_ : ℝ) < _)
  exact ⟨x, mem_interior_iff_mem_nhds.mpr <|
    (eventually_strictMono p hx).mono fun _ hy => hy.monotone⟩

/-- The closed chamber determines a derivative uniquely, including at its boundary. -/
theorem uniqueDiffOn_chamber (p : Equiv.Perm (Fin n)) : UniqueDiffOn ℝ (chamber p) :=
  uniqueDiffOn_convex (convex_chamber p) (interior_chamber_nonempty p)

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Reindex the coordinates by a fixed permutation as a continuous linear map. -/
def permute (p : Equiv.Perm (Fin n)) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (p i)

/-- Sort the tuple in ascending order, then evaluate the readout on the sorted tuple. -/
noncomputable def sortedReadout (read : (Fin n → ℝ) → Y) (x : Fin n → ℝ) : Y :=
  read (x ∘ Tuple.sort x)

/-- At a fixed input, precompose the readout derivative with every permutation sorting that
input. A proposed derivative works exactly when each of those composites is the proposed map. -/
theorem hasFDerivAt_sortedReadout_iff {read : (Fin n → ℝ) → Y} (x : Fin n → ℝ)
    {L : (Fin n → ℝ) →L[ℝ] Y} (hread : HasFDerivAt read L (x ∘ Tuple.sort x))
    (D : (Fin n → ℝ) →L[ℝ] Y) :
    HasFDerivAt (sortedReadout read) D x ↔
      ∀ p : Equiv.Perm (Fin n), x ∈ chamber p → L.comp (permute p) = D := by
  let cover : Finset (Equiv.Perm (Fin n)) := Finset.univ
  have full : (⋃ p ∈ cover, chamber p) = univ := by
    apply eq_univ_of_forall
    intro y
    exact mem_iUnion.mpr ⟨Tuple.sort y,
      mem_iUnion.mpr ⟨Finset.mem_univ _, Tuple.monotone_sort y⟩⟩
  have hcell (p : Equiv.Perm (Fin n)) :
      EqOn (sortedReadout read) (read ∘ permute p) (chamber p) :=
    fun _ hy => congrArg read (Tuple.comp_sort_eq_comp_iff_monotone.mpr hy).symm
  have hbranch (p : Equiv.Perm (Fin n)) (hx : x ∈ chamber p) :
      HasFDerivAt (read ∘ permute p) (L.comp (permute p)) x := by
    have hlocal : HasFDerivAt read L (permute p x) := by
      change HasFDerivAt read L (x ∘ p)
      rwa [Tuple.comp_sort_eq_comp_iff_monotone.mpr hx]
    exact hlocal.comp x (permute p).hasFDerivAt
  have h := hasFDerivAt_iff_activeBranches (D := D) cover chamber (by simp [full])
    (fun p _ hp => (isClosed_chamber p).closure_eq ▸ hp)
    (fun p => read ∘ permute p) (fun p => L.comp (permute p))
    (fun p _ hp => (hbranch p hp).hasFDerivWithinAt)
    (fun p _ _ => (hcell p).eventuallyEq_nhdsWithin)
    (fun p _ hx => uniqueDiffOn_chamber p x hx)
  simpa [cover] using h

/-- Apply the specified weight to each rank and sum. -/
noncomputable def weighted (w : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] ℝ :=
  ∑ i, w i • ContinuousLinearMap.proj (R := ℝ) i

private theorem weighted_permute_apply (w : Fin n → ℝ) (p : Equiv.Perm (Fin n))
    (x : Fin n → ℝ) :
    (weighted w).comp (permute p) x = ∑ k, w (p.symm k) * x k := by
  change (weighted w) (permute p x) = _
  simp only [weighted, sum_apply, smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
  rw [← Equiv.sum_comp p (fun k => w (p.symm k) * x k)]
  simp [permute]

private theorem weighted_permute_eq_iff (w : Fin n → ℝ) (p q : Equiv.Perm (Fin n)) :
    (weighted w).comp (permute p) = (weighted w).comp (permute q) ↔
      ∀ k, w (p.symm k) = w (q.symm k) := by
  constructor
  · intro h k
    have hk := congrArg (fun L : (Fin n → ℝ) →L[ℝ] ℝ => L (Pi.single k 1)) h
    change (weighted w).comp (permute p) (Pi.single k 1) =
      (weighted w).comp (permute q) (Pi.single k 1) at hk
    rw [weighted_permute_apply, weighted_permute_apply] at hk
    simpa [Pi.single_apply, mul_ite] using hk
  · intro h
    ext x
    simp only [weighted_permute_apply, h]

/-- A weighted readout of sorted coordinates is differentiable exactly when equal sorted
entries carry equal weights. This includes ties of any multiplicity and the empty tuple. -/
theorem differentiableAt_weighted_iff (w x : Fin n → ℝ) :
    DifferentiableAt ℝ (sortedReadout (weighted w)) x ↔
      ∀ i j, x (Tuple.sort x i) = x (Tuple.sort x j) → w i = w j := by
  let p := Tuple.sort x
  have hp : x ∈ chamber p := Tuple.monotone_sort x
  have criterion := hasFDerivAt_sortedReadout_iff (read := weighted w) x (weighted w).hasFDerivAt
  constructor
  · rintro ⟨D, hD⟩ i j ht
    let q := (Equiv.swap i j).trans p
    have hq : x ∘ q = x ∘ p := by
      funext k
      change x (p (Equiv.swap i j k)) = x (p k)
      by_cases hi : k = i
      · simpa [hi, p] using ht.symm
      by_cases hj : k = j
      · simpa [hj, p] using ht
      · rw [Equiv.swap_apply_of_ne_of_ne hi hj]
    have hqp : (weighted w).comp (permute q) = (weighted w).comp (permute p) := by
      exact ((criterion D).mp hD q (show Monotone (x ∘ q) by rw [hq]; exact hp)).trans
        ((criterion D).mp hD p hp).symm
    have hw := (weighted_permute_eq_iff w q p).mp hqp (p i)
    simpa [q] using hw.symm
  · intro h
    refine ⟨(weighted w).comp (permute p), (criterion _).mpr ?_⟩
    intro q hq
    apply (weighted_permute_eq_iff w q p).mpr
    intro k
    apply h
    have hsort : x ∘ q = x ∘ p := Tuple.comp_sort_eq_comp_iff_monotone.mpr hq
    simpa [p] using (congrFun hsort (q.symm k)).symm

end Examples.FiniteSortReadout
