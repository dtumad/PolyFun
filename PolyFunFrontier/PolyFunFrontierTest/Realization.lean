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

@[expose] def flip : Coin.FreeM Bool := FreeM.lift ()

noncomputable def fair : Handler Cslib.ProbComp Coin := fun _ => Cslib.ProbComp.uniform Bool

/-- Read the next bit of a concrete tape, with false as the exhausted-tape default. -/
@[expose] def readBit : Handler (StateM (List Bool)) Coin :=
  fun _ tape => (tape.headD false, tape.tail)

/-- Implement one request by consuming two target bits and returning the second. -/
@[expose] def secondBit : Handler (FreeM Coin) Coin := fun _ => do
  let _ ← flip
  flip

/-- A single open program branches on its first answer and may ask for another. -/
@[expose] def consecutive : Coin.FreeM Bool := do
  if ← flip then flip else pure false

/-- The one-bit handler stops on the first false and leaves the remaining tape untouched. -/
theorem consecutive_direct :
    (consecutive.liftM readBit).run [false, true, false, true] =
      (false, [true, false, true]) := rfl

/-- Installing the two-read implementation changes both the result and the consumed tape.
Running through the composite handler and folding the installed program agree. -/
theorem consecutive_installed :
    (consecutive.liftM (readBit.comp secondBit)).run [false, true, false, true] = (true, []) := by
  rw [Handler.liftM_comp]
  rfl

example (program : List Bool → Coin.FreeM Bool)
    (h : FreeM.PPTProgram (fair.comp secondBit) encBits encBool program) :
    Cslib.Probability.IsPPTOn encBits encBool (fun w => ((program w).liftM secondBit).liftM fair) :=
  (FreeM.PPTProgram.substitute secondBit h).isPPTOn

/-- Installing that same two-read handler over fair coins supplies a single machine family. -/
theorem secondBit_certificate :
    FreeM.PPTProgram fair encBits encBool (fun _ : List Bool => flip.liftM secondBit) := by
  apply FreeM.PPTProgram.substitute
  have h : Cslib.Probability.IsPPTOn encBits encBool
      (fun _ : List Bool => (fair.comp secondBit) ()) := by
    change Cslib.Probability.IsPPTOn encBits encBool (fun _ : List Bool => do
      let _ ← Cslib.ProbComp.uniform Bool
      Cslib.ProbComp.uniform Bool)
    exact (Cslib.Probability.isPPTOn_uniform_bool encBits).bind
      (Cslib.Probability.isPPTOn_uniform_bool encBool)
  apply (FreeM.PPTProgram.call (H := fair.comp secondBit) (query := fun _ : List Bool => ())
    (answer := fun _ => id) (by simpa only [id_map] using h)).congr
  exact fun _ => id_map flip

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
