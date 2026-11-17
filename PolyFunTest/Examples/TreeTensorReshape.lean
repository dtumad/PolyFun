/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.Tutorials.TreeTensorReshape
meta import Examples.Tutorials.TreeTensorReshape
meta import Mathlib.Algebra.Group.Int.Defs

/-!
# TensorType's five-entry tree

The left subtree has root 7 and leaves −42 and 46. The full tree has root 60 and right leaf 2.
Selecting 46 twice and 2 once sends the first two output weights back to the same leaf.
-/

public section

namespace Examples.TreeTensor.Test

private def sampleShape : Shape := .node (.node .leaf .leaf) .leaf

private def sampleValues : Pos sampleShape → Int
  | .left (.left .atLeaf) => -42
  | .left .atNode => 7
  | .left (.right .atLeaf) => 46
  | .atNode => 60
  | .right .atLeaf => 2

private def sampleSelection : Fin 3 → Fin (size sampleShape) :=
  (#v[2, 2, 4] : Vector (Fin 5) 3).get

/-- In-order values, selected values, returned weights, and weights for the empty selection. -/
def fiveEntryReshapes : Array (Array Int) :=
  let values := flatten sampleShape sampleValues
  let weights := returnWeights sampleShape sampleSelection #v[2, 3, 7]
  let emptyWeights := returnWeights sampleShape Fin.elim0 (#v[] : Vector Int 0)
  #[values.toArray, (gather sampleSelection values).toArray,
    (flatten sampleShape weights).toArray, (flatten sampleShape emptyWeights).toArray]

/-- info: #[#[-42, 7, 46, 60, 2], #[46, 46, 2], #[0, 0, 5, 0, 7], #[0, 0, 0, 0, 0]] -/
#guard_msgs in
#eval fiveEntryReshapes

end Examples.TreeTensor.Test
