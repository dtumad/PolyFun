/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Lens.Basic
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# In-order traversal as a polynomial lens

A binary tree has one entry at each node and leaf. The in-order lens sends its shape to the
number of entries and sends each flat index back to its tree position. A separate executable
walk appends vectors as it recurses. Its lookup theorem identifies the walk with this lens.
The convention follows Bruno Gavranović's
[TensorType traversal example](https://github.com/bgavran/TensorType/blob/7715491df8a38e121489187f0a2383523af69d47/examples/TensorManipulation.idr#L215-L232).
-/

public section

namespace Examples.TreeTensor

/-- The shape of a binary tree with a payload at every node and every leaf. -/
inductive Shape where
  | leaf
  | node (left right : Shape)
  deriving DecidableEq, Repr

/-- The locations at which an all-node tree carries an entry. -/
inductive Pos : Shape → Type where
  | atLeaf : Pos .leaf
  | left {l r : Shape} : Pos l → Pos (.node l r)
  | atNode {l r : Shape} : Pos (.node l r)
  | right {l r : Shape} : Pos r → Pos (.node l r)
  deriving DecidableEq, Repr

/-- Number of payloads visited in order. -/
@[expose] def size : Shape → Nat
  | .leaf => 1
  | .node l r => size l + (1 + size r)

/-- The polynomial of labelled binary trees. -/
abbrev treeP : PFunctor := ⟨Shape, Pos⟩

/-- The polynomial of flat vectors of arbitrary length. -/
abbrev flatP : PFunctor := ⟨Nat, Fin⟩

private def leafPositions : Fin 1 ≃ Pos .leaf where
  toFun _ := .atLeaf
  invFun _ := 0
  left_inv _ := Subsingleton.elim _ _
  right_inv p := by cases p; rfl

private def nodePositions (l r : Shape) : Pos l ⊕ (Fin 1 ⊕ Pos r) ≃ Pos (.node l r) where
  toFun
    | .inl p => .left p
    | .inr (.inl _) => .atNode
    | .inr (.inr p) => .right p
  invFun
    | .left p => .inl p
    | .atNode => .inr (.inl 0)
    | .right p => .inr (.inr p)
  left_inv
    | .inl _ => rfl
    | .inr (.inl k) => by
      have hk : k = 0 := Subsingleton.elim _ _
      subst k
      rfl
    | .inr (.inr _) => rfl
  right_inv p := by cases p <;> rfl

/-- Convert between an in-order index and a tree position in either direction. -/
def indexEquiv : (s : Shape) → Fin (size s) ≃ Pos s
  | .leaf => leafPositions
  | .node l r =>
    let rest := finSumFinEquiv.symm.trans ((Equiv.refl (Fin 1)).sumCongr (indexEquiv r))
    (finSumFinEquiv.symm.trans ((indexEquiv l).sumCongr rest)).trans (nodePositions l r)

/-- Flattening sends the shape to its size and pulls payloads from in-order positions. -/
@[expose] def inorder : PFunctor.Lens treeP flatP where
  toFunA := size
  toFunB := fun s => indexEquiv s

@[simp] theorem inorder_toFunA (s : Shape) : inorder.toFunA s = size s := rfl

@[simp] theorem inorder_toFunB (s : Shape) (i : Fin (size s)) :
    inorder.toFunB s i = indexEquiv s i := rfl

/-- Materialize a tree by walking the left subtree, the current node and the right subtree. -/
@[expose] def flatten {α : Type*} : (s : Shape) → (Pos s → α) → Vector α (size s)
  | .leaf, x => Vector.replicate 1 (x .atLeaf)
  | .node l r, x =>
    flatten l (fun p => x (.left p)) ++
      (Vector.replicate 1 (x .atNode) ++ flatten r (fun p => x (.right p)))

private theorem append_get_left {α : Type*} {n m : Nat} (xs : Vector α n) (ys : Vector α m)
    (i : Fin n) : (xs.append ys).get (Fin.castAdd m i) = xs.get i :=
  Vector.getElem_append_left i.isLt

private theorem append_get_right {α : Type*} {n m : Nat} (xs : Vector α n) (ys : Vector α m)
    (i : Fin m) : (xs.append ys).get (Fin.natAdd n i) = ys.get i := by
  change (xs ++ ys)[n + i.val] = ys[i.val]
  rw [Vector.getElem_append_right (by omega) (by omega)]
  simp

private theorem flatten_get_position {α : Type*} {s : Shape} (p : Pos s) (x : Pos s → α) :
    (flatten s x).get ((indexEquiv s).symm p) = x p := by
  induction p with
  | atLeaf => rfl
  | left p ih =>
    change Vector.get (Vector.append _ _) (Fin.castAdd _ ((indexEquiv _).symm p)) = _
    rw [append_get_left]
    exact ih _
  | atNode =>
    change Vector.get (Vector.append _ (Vector.append _ _))
      (Fin.natAdd _ (Fin.castAdd _ (0 : Fin 1))) = _
    rw [append_get_right, append_get_left]
    rfl
  | right p ih =>
    change Vector.get (Vector.append _ (Vector.append _ _))
      (Fin.natAdd _ (Fin.natAdd 1 ((indexEquiv _).symm p))) = _
    rw [append_get_right, append_get_right]
    exact ih _

/-- Every entry in the materialized vector agrees with the direction chosen by the lens. -/
theorem flatten_get {α : Type*} (s : Shape) (x : Pos s → α) (i : Fin (size s)) :
    (flatten s x).get i = x (indexEquiv s i) := by
  simpa using flatten_get_position (indexEquiv s i) x

end Examples.TreeTensor
