/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
-- frontier: CslibFrontier.Computability.Probabilistic.Sampling

public import CslibFrontier.Computability.Probabilistic.Sampling
public import CslibFrontier.Computability.Probabilistic.PPT.Capture
public import PolyFun.PFunctor.Handler.Free
public import PolyFun.PFunctor.Handler.Sum

/-!
# Uniform machine realizations of typed free programs

`PPTProgram handler input output program` certifies a family of free programs at fixed input
and output encodings. A primitive request needs a certificate for its handler at the requested
arguments. A continuation that retains its input is certified on a pair of the input and the
first result. The same derivation can be used over a larger signature by relabelling its requests.

`PPTProgram.exists_halting_machine` supplies one finite fair-coin machine and one polynomial
clock for the whole family. Its encoded output law agrees with the fold of the source program
under the specified handler, and every supported run halts within the clock.
-/

@[expose] public section

namespace PFunctor.FreeM

open Turing.MultiTapeTM
open Cslib.Probability (IsPPTOn)

/-- Draw a word in sampling order, running the given bit program once per output bit. -/
def sampleBits {P : PFunctor} (coin : P.FreeM Bool) : Nat → P.FreeM (List Bool)
  | 0 => pure []
  | n + 1 => do
    let bit ← coin
    return bit :: (← sampleBits coin n)

/-- Handling a fair bit at each draw gives the frontier's fair-word program. -/
theorem liftM_sampleBits {P : PFunctor} {H : Handler Cslib.ProbComp P} {coin : P.FreeM Bool}
    (hcoin : coin.liftM H = Cslib.ProbComp.uniform Bool) (n : Nat) :
    (sampleBits coin n).liftM H = Cslib.BitString.sampleList n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sampleBits, Cslib.BitString.sampleList, liftM_bind, liftM_pure, hcoin, ih]

/-- A compositional certificate for an input-indexed free program and its probabilistic handler.
The encodings belong to the family and are fixed across all inputs. -/
inductive PPTProgram : {P : PFunctor.{0, 0}} → Handler Cslib.ProbComp P → {α β : Type} →
    (α ↪ List Bool) → (β ↪ List Bool) → (α → P.FreeM β) → Prop where
  /-- Return an efficiently computed value. -/
  | localMap {P : PFunctor} {H : Handler Cslib.ProbComp P} {α β : Type}
      {input : α ↪ List Bool} {output : β ↪ List Bool} {f : α → β}
      (hf : ComputableInPolyTime f input output) :
      PPTProgram H input output (fun a => pure (f a))
  /-- Make one request and read its dependent response at the chosen output type. -/
  | call {P : PFunctor} {H : Handler Cslib.ProbComp P} {α β : Type}
      {input : α ↪ List Bool} {output : β ↪ List Bool} {query : α → P.A}
      {answer : (a : α) → P.B (query a) → β}
      (h : IsPPTOn input output (fun a => answer a <$> H (query a))) :
      PPTProgram H input output (fun a => answer a <$> FreeM.lift (query a))
  /-- Retain the typed input across a probabilistic first stage. -/
  | bindWith {P : PFunctor} {H : Handler Cslib.ProbComp P} {α β γ : Type}
      {input : α ↪ List Bool} {middle : β ↪ List Bool} {output : γ ↪ List Bool}
      {first : α → P.FreeM β} {next : α → β → P.FreeM γ}
      (hfirst : PPTProgram H input middle first)
      (hnext : PPTProgram H (encPair input middle) output (fun p => next p.1 p.2)) :
      PPTProgram H input output (fun a => first a >>= next a)
  /-- Prepare an argument with an encoded polynomial-time function. -/
  | preprocess {P : PFunctor} {H : Handler Cslib.ProbComp P} {α β γ : Type}
      {input : α ↪ List Bool} {middle : β ↪ List Bool} {output : γ ↪ List Bool}
      {program : β → P.FreeM γ} {f : α → β}
      (h : PPTProgram H middle output program) (hf : ComputableInPolyTime f input middle) :
      PPTProgram H input output (fun a => program (f a))
  /-- Draw an efficiently computed unary number of fair bits. -/
  | sampleBits {P : PFunctor} {H : Handler Cslib.ProbComp P} {α : Type}
      {input : α ↪ List Bool} {count : α → Nat} {coin : P.FreeM Bool}
      (hcoin : coin.liftM H = Cslib.ProbComp.uniform Bool)
      (hcount : ComputableInPolyTime count input encUnary) :
      PPTProgram H input encBits (fun a => FreeM.sampleBits coin (count a))
  /-- Substitute a free program for each request. The original certificate reads requests
  through the composite of that implementation and the final handler. -/
  | substitute {P Q : PFunctor} {H : Handler Cslib.ProbComp Q} {α β : Type}
      {input : α ↪ List Bool} {output : β ↪ List Bool} {program : α → P.FreeM β}
      (impl : Handler (FreeM Q) P) (h : PPTProgram (H.comp impl) input output program) :
      PPTProgram H input output (fun a => (program a).liftM impl)

namespace PPTProgram

variable {P Q : PFunctor} {H : Handler Cslib.ProbComp P} {G : Handler Cslib.ProbComp Q}
  {α β γ : Type} {input : α ↪ List Bool} {middle : β ↪ List Bool} {output : γ ↪ List Bool}

/-- Transport a certificate along an equation of source programs at every input. -/
theorem congr {first second : α → P.FreeM β} (h : PPTProgram H input middle first)
    (heq : ∀ a, first a = second a) : PPTProgram H input middle second :=
  funext heq ▸ h

/-- Relabel the source interface along a lens, using its backward map on responses. -/
theorem mapLens {program : α → P.FreeM β} (l : Lens P Q)
    (h : PPTProgram (G.comapLens l) input middle program) :
    PPTProgram G input middle (fun a => (program a).mapLens l) := by
  have h' : PPTProgram (G.comp (Handler.ofLens l)) input middle program :=
    by simpa only [Handler.comp_ofLens] using h
  exact (substitute (Handler.ofLens l) h').congr (fun a => Handler.liftM_ofLens l (program a))

/-- Apply an efficient deterministic map to the original input and a sampled result. -/
theorem mapWith {program : α → P.FreeM β} {f : α → β → γ}
    (h : PPTProgram H input middle program)
    (hf : ComputableInPolyTime (fun p : α × β => f p.1 p.2) (encPair input middle) output) :
    PPTProgram H input output (fun a => f a <$> program a) := by
  apply (h.bindWith (next := fun a b => pure (f a b)) (.localMap hf)).congr
  exact fun a => bind_pure_comp (f a) (program a)

/-- Use a program over the left component of a sum handler. -/
theorem sumLeft {program : α → P.FreeM β} (h : PPTProgram H input middle program)
    (right : Handler Cslib.ProbComp Q) :
    PPTProgram (H.sum right) input middle (fun a => (program a).mapLens Lens.inl) :=
  .mapLens Lens.inl (by simpa only [Handler.sum_comapLens_inl] using h)

/-- Use a program over the right component of a sum handler. -/
theorem sumRight {program : α → Q.FreeM β} (h : PPTProgram G input middle program)
    (left : Handler Cslib.ProbComp P) :
    PPTProgram (left.sum G) input middle (fun a => (program a).mapLens Lens.inr) :=
  .mapLens Lens.inr (by simpa only [Handler.sum_comapLens_inr] using h)

/-- The handler fold of a certified source is strict uniform probabilistic polynomial time. -/
theorem isPPTOn {program : α → P.FreeM β} (h : PPTProgram H input middle program) :
    IsPPTOn input middle (fun a => (program a).liftM H) := by
  induction h with
  | localMap hf => simpa only [liftM_pure] using hf.isPPTOn
  | call h => simpa only [liftM_map, liftM_lift] using h
  | bindWith _ _ ihFirst ihNext =>
    simpa only [liftM_bind] using ihFirst.bind_with ihNext
  | preprocess _ hf ih => exact ih.preprocess hf
  | sampleBits hcoin hcount =>
    simpa only [liftM_sampleBits hcoin] using hcount.sampleList
  | substitute impl _ ih => simpa only [Handler.liftM_comp] using ih

/-- A single finite machine realizes every input and halts on every supported branch of every
input word within its polynomial clock. -/
theorem exists_halting_machine {program : α → P.FreeM β} (h : PPTProgram H input middle program) :
    ∃ (k : ℕ) (State : Type) (_ : Finite State) (machine : Turing.MultiTapePTM k Bool State)
      (c d : ℕ),
      (∀ a, (Cslib.ProbComp.eval ((program a).liftM H)).map middle =
        Cslib.ProbComp.eval (machine.runClosed (c * ((input a).length + 1) ^ d) (input a))) ∧
      ∀ word, ∀ final ∈ (Cslib.ProbComp.eval (machine.runConfigFrom (Cslib.ProbComp.uniform Bool)
        Empty.elim (c * (word.length + 1) ^ d) (machine.initialConfig word))).support,
        final.tapes.state = none :=
  h.isPPTOn.exists_halting_machine

end PPTProgram

end PFunctor.FreeM
