/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import PolyFunFrontier.IPFunctor.Scoped.PolyTime
public import PolyFunFrontier.PFunctor.Free.Realization
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Tactic.PPT

/-!
# Fair-word realization at variable input length

The source draws one bit for each input symbol. Replaying a two-bit tape checks the order
of the returned word. The realization uses the primitive fair-bit handler on both summands.
-/

public section

namespace PolyFunFrontierTest.Realization

open PFunctor Turing.MultiTapeTM

abbrev Coin := monomial Unit Bool

def flip : Coin.FreeM Bool := FreeM.lift ()

noncomputable def fair : Handler Cslib.ProbComp Coin := fun _ => Cslib.ProbComp.uniform Bool

private noncomputable def readBit : Handler (StateM (List Bool)) Coin :=
  fun _ tape => (tape.headD false, tape.tail)

private def secondBit : Handler (FreeM Coin) Coin := fun _ => do
  let _ ← flip
  flip

example : ((flip.liftM secondBit).liftM readBit).run [true, false] = (false, []) := rfl

example (program : List Bool → Coin.FreeM Bool)
    (h : FreeM.PPTProgram (fair.comp secondBit) encBits encBool program) :
    Cslib.Probability.IsPPTOn encBits encBool (fun w => ((program w).liftM secondBit).liftM fair) :=
  (FreeM.PPTProgram.substitute secondBit h).isPPTOn

example : ((FreeM.sampleBits flip 0).liftM readBit).run [true] = ([], [true]) := rfl

example : ((FreeM.sampleBits flip 2).liftM readBit).run [true, false] = ([true, false], []) := rfl

example : FreeM.sampleBits flip 1 ≠ pure [] := by
  intro h
  cases h

example : (IPFunctor.ScopedSignature.Binary.term ()).denote
    (IPFunctor.ScopedSignature.Binary.algebra (fun (_ : Unit) => Nat.sub))
    (IPFunctor.ScopedSignature.Binary.pairEnv (9, 4)) = 5 := rfl

theorem wordCertificate :
    FreeM.PPTProgram fair encBits encBits (fun word => FreeM.sampleBits flip word.length) := by
  apply FreeM.PPTProgram.sampleBits
  · exact FreeM.liftM_lift (P := Coin) fair ()
  · polytime

example : FreeM.PPTProgram fair encBits encBool (fun _ : List Bool => flip) := by
  have hfair : Cslib.Probability.IsPPTOn encBits encBool
      (fun _ : List Bool => Cslib.ProbComp.uniform Bool) := by ppt
  apply (FreeM.PPTProgram.call (H := fair) (query := fun _ : List Bool => ())
    (answer := fun _ => id) (by simpa only [id_map, fair] using hfair)).congr
  exact fun _ => id_map flip

example : Cslib.Probability.IsPPTOn encBits encBits (fun word =>
    ((FreeM.sampleBits flip word.length).mapLens (Lens.inl (Q := Coin))).liftM (fair.sum fair)) :=
  (wordCertificate.sumLeft fair).isPPTOn

example : Cslib.Probability.IsPPTOn encBits encBits (fun word =>
    ((FreeM.sampleBits flip word.length).mapLens (Lens.inr (P := Coin))).liftM (fair.sum fair)) :=
  (wordCertificate.sumRight fair).isPPTOn

end PolyFunFrontierTest.Realization
