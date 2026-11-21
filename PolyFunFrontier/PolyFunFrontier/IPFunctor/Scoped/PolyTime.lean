/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
-- frontier: CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString

public import PolyFun.Realizability.Scoped
public import PolyFunFrontier.Realizability.MultiTape
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Tactic.PolyTime

/-!
# Polynomial-time interpretations of scoped terms

The generic scoped-term admissibility theorem applies to the multi-tape step class. Here
the binary word language interprets a Boolean truth table pointwise on two words. Its XOR term
reads the two free variables of a pair, giving a machine certificate for the resulting word map.
-/

public section

namespace IPFunctor.ScopedSignature

open PFunctor Turing.MultiTapeTM

/-- Machine certificate for the XOR term of the binary word language. -/
theorem wordXor_polyTime :
    ComputableInPolyTime (fun p : List Bool × List Bool => p.1.zipWith Bool.xor p.2)
      (encPair encBits encBits) encBits :=
  Binary.denote_term_admissible (C := StepClass.multiTapePolyTime) (repr := encBits)
    (applyOp := fun op x y => List.zipWith op x y) (fun op => by
      change ComputableInPolyTime (fun p : List Bool × List Bool => p.1.zipWith op p.2)
        (encPair encBits encBits) encBits
      polytime) Bool.xor

end IPFunctor.ScopedSignature
