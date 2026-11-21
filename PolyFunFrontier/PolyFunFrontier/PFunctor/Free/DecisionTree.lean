/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
-- frontier: CslibFrontier.Computability.DecisionTree.FreeM
-- frontier: CslibFrontier.Computability.DecisionTree.Parity

public import CslibFrontier.Computability.DecisionTree.FreeM
public import CslibFrontier.Computability.DecisionTree.Parity
public import PolyFun.PFunctor.Bound

/-!
# Decision-tree depth and free-program roll bounds

A Boolean decision tree has depth at most `n` precisely when its free program has total roll bound
`n`. The tree and program are related by cslib-frontier's `Cslib.DecisionTree.equivFreeM`.
The parity and sensitivity bounds for these programs are in
`PolyFunFrontier.PFunctor.Free.DecisionTree.LowerBound`.
-/

public section

universe u v

namespace Cslib.DecisionTree

open PFunctor

variable {ι : Type u} {β : Type v}

/-- The depth of a decision tree is the total roll bound of its free program. -/
theorem depth_le_iff_isTotalRollBound (t : DecisionTree ι β) (n : ℕ) :
    t.depth ≤ n ↔ t.toFreeM.IsTotalRollBound n := by
  induction t generalizing n with
  | leaf => simp
  | node i t₀ t₁ ih₀ ih₁ =>
    rw [toFreeM_node, FreeM.isTotalRollBound_lift_bind_iff, Bool.forall_bool]
    simp only [depth_node, Bool.cond_false, Bool.cond_true, ← ih₀, ← ih₁]
    omega

/-- A free program over Boolean queries has total roll bound `n` exactly when its decision tree has
depth at most `n`. -/
theorem depth_ofFreeM_le_iff (p : (monomial ι Bool).FreeM β) (n : ℕ) :
    (ofFreeM p).depth ≤ n ↔ p.IsTotalRollBound n := by
  rw [depth_le_iff_isTotalRollBound, toFreeM_ofFreeM]

end Cslib.DecisionTree
