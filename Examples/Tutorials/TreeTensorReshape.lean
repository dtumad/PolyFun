/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.Tutorials.TreeTensorTraversal
public import Examples.Tutorials.TreeTensorScatter
public import PolyFun.PFunctor.Lens.Yoneda

/-!
# Reshaping a tree and returning weights to it

An in-order traversal gives every tree position a flat index. A selection of these indices
may repeat or omit entries. Its forward action reads the selected entries. Its reverse action
adds weights at repeated indices and returns zero at omitted positions. The two theorems
compare the executable passes with the forward and reverse actions of the same composite lens.
-/

public section

namespace Examples.TreeTensor

open PFunctor

variable {α : Type*} {m n : Nat}

/-- Materialize selected vector entries. Each output chooses its own input index. -/
def gather (r : Fin m → Fin n) (x : Vector α n) : Vector α m :=
  Vector.ofFn fun j => x.get (r j)

/-- At a fixed tree shape the traversal and selection are lenses between single-shape layouts. -/
def layout (s : Shape) (r : Fin m → Fin (size s)) :
    Lens (purePower.{0, 0} (Pos s)) (purePower.{0, 0} (Fin m)) :=
  Lens.purePowerMap r ∘ₗ (Lens.purePowerMap (inorder.toFunB s) :
    Lens (purePower.{0, 0} (Pos s)) (purePower.{0, 0} (Fin (size s))))

/-- Gathering from the materialized tree agrees with the composite lens. -/
theorem gather_flatten_get (s : Shape) (x : Pos s → α) (r : Fin m → Fin (size s)) (j : Fin m) :
    (gather r (flatten s x)).get j =
      ((layout s r).mapObj (Obj.mk PUnit.unit x)).snd j := by
  change (Vector.ofFn _)[j.val] = _
  rw [Vector.getElem_ofFn]
  exact flatten_get s x (r j)

/-- Scatter weights into a flat buffer and read that buffer at the index of a tree position. -/
def returnWeights [Zero α] [Add α] (s : Shape) (r : Fin m → Fin (size s))
    (w : Vector α m) : Pos s → α :=
  let buffer := scatter r w
  fun p => buffer.get ((indexEquiv s).symm p)

/-- At every original position the two reverse stages compute the fibre sum for the composite. -/
theorem returnWeights_eq_mapDomain [AddCommMonoid α] (s : Shape) (r : Fin m → Fin (size s))
    (w : Vector α m) (p : Pos s) :
    returnWeights s r w p =
      Finsupp.mapDomain ((layout s r).toFunB PUnit.unit)
        (Finsupp.equivFunOnFinite.symm w.get) p := by
  change (scatter r w).get ((indexEquiv s).symm p) =
    (Finsupp.mapDomain ((indexEquiv s) ∘ r) _) p
  rw [scatter_spec, Finsupp.mapDomain_comp, Finsupp.mapDomain_equiv_apply]

end Examples.TreeTensor
