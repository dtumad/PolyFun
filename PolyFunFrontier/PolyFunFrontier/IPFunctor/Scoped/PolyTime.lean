/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
-- frontier: CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString

public import PolyFun.IPFunctor.Scoped.Interpretation
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Tactic.PolyTime

/-!
# Polynomial-time interpretations of scoped terms

An environment represents the input to a term by one encoded projection for each free variable.
Each constructor supplies one rule for its interpreter, using certificates for its arguments in
their extended scopes. Structural induction then certifies the denotation of any fixed term by
one polynomial-time multi-tape machine on all inputs.

The binary word language interprets a Boolean truth table pointwise on two words. Its XOR term
reads the two free variables of a pair, giving a machine certificate for the resulting word map.
-/

@[expose] public section

universe u v w

namespace IPFunctor.ScopedSignature

open Turing.MultiTapeTM

variable {S : Type u} {V : S → Type} {σ : ScopedSignature.{u, v, w} S}
  {ι : Type} {input : ι ↪ List Bool} {enc : (s : S) → V s ↪ List Bool} {Γ Δ : List S}

/-- Every typed variable in an environment is an efficiently computable function of the input. -/
def Env.PolyTime (enc : (s : S) → V s ↪ List Bool) (input : ι ↪ List Bool)
    (ρ : ι → Env V Γ) : Prop :=
  ∀ {s} (x : ScopedVar Γ s), ComputableInPolyTime (fun i => ρ i s x) input (enc s)

/-- The empty environment has no variables to represent. -/
theorem Env.PolyTime.empty : Env.PolyTime enc input (fun _ => Env.empty) :=
  fun x => nomatch x

/-- Extend an efficiently accessible environment with one efficiently computed value. -/
theorem Env.PolyTime.cons {s : S} {ρ : ι → Env V Γ} {value : ι → V s}
    (hρ : Env.PolyTime enc input ρ) (hv : ComputableInPolyTime value input (enc s)) :
    Env.PolyTime enc input (fun i => Env.cons (value i) (ρ i)) := by
  intro a x
  cases x with
  | zero => exact hv
  | succ x => exact hρ x

/-- Freshly bound variables retain their projections beside those of the outer context. -/
theorem Env.PolyTime.append {ξ : ι → Env V Δ} {ρ : ι → Env V Γ}
    (hξ : Env.PolyTime enc input ξ) (hρ : Env.PolyTime enc input ρ) :
    Env.PolyTime enc input (fun i => Env.append (ξ i) (ρ i)) := by
  induction Δ with
  | nil => exact hρ
  | cons s Δ ih =>
    exact Env.PolyTime.cons
      (ih (ξ := fun i a x => ξ i a (.succ x)) (fun x => hξ (.succ x))) (hξ .zero)

/-- A constructor's denotation is efficient if its argument meanings are efficient in every
efficiently supplied block of bound variables. The input type and encoding are shared by the
constructor and each of its arguments. -/
def Interpretation.PreservesPolyTime (alg : Interpretation σ V)
    (enc : (s : S) → V s ↪ List Bool) : Prop :=
  ∀ {ι : Type} (input : ι ↪ List Bool) {s} (op : σ.Op s)
    (args : (p : σ.Arg op) → ι → Env V (σ.binders op p) → V (σ.sort op p)),
    (∀ p (ξ : ι → Env V (σ.binders op p)), Env.PolyTime enc input ξ →
      ComputableInPolyTime (fun i => args p i (ξ i)) input (enc (σ.sort op p))) →
    ComputableInPolyTime (fun i => alg op (fun p η => args p i η)) input (enc s)

/-- A certified constructor algebra gives a machine certificate for the denotation of every
term, for all inputs represented by the variable projections. -/
theorem Term.computableInPolyTime {alg : Interpretation σ V} (h : alg.PreservesPolyTime enc)
    {s : S} (t : σ.Term Γ s) {ρ : ι → Env V Γ} (hρ : Env.PolyTime enc input ρ) :
    ComputableInPolyTime (fun i => t.denote alg (ρ i)) input (enc s) := by
  induction t using Term.inductionOn with
  | hvar Γ s x => exact hρ x
  | hnode Γ s op args ih =>
    apply h input op (fun p i η => (args p).denote alg (Env.append η (ρ i)))
    exact fun p ξ hξ => ih p (hξ.append hρ)

namespace Binary

/-- A binary operation tag has two arguments in the ambient scope. -/
@[reducible] def signature (Op : Type) : ScopedSignature Unit where
  Op _ := Op
  Arg _ := Bool
  binders _ _ := []
  sort _ _ := ()

/-- Interpret each binary tag by its operation on values. -/
def algebra {Op A : Type} (applyOp : Op → A → A → A) : Interpretation (signature Op) (fun _ => A) :=
  fun op args => applyOp op (args false Env.empty) (args true Env.empty)

/-- Apply the given operation to the two free variables in order. -/
def term {Op : Type} (op : Op) : (signature Op).Term [(), ()] () :=
  Term.node op fun right => if right then .var (.succ .zero) else .var .zero

/-- The two fields of an encoded pair provide the free variables of a binary term. -/
def pairEnv {A : Type} (p : A × A) : Env (fun _ : Unit => A) [(), ()] :=
  Env.cons p.1 (Env.single p.2)

@[simp] theorem denote_term {Op A : Type} (applyOp : Op → A → A → A) (op : Op) (p : A × A) :
    (term op).denote (algebra applyOp) (pairEnv p) = applyOp op p.1 p.2 := rfl

/-- Efficient primitive operations certify the binary algebra at every input encoding. -/
theorem preservesPolyTime {Op A : Type} {applyOp : Op → A → A → A} {e : A ↪ List Bool}
    (h : ∀ op, ComputableInPolyTime (fun p : A × A => applyOp op p.1 p.2) (encPair e e) e) :
    Interpretation.PreservesPolyTime (σ := signature Op) (algebra applyOp) (fun _ => e) := by
  intro ι input s op args hargs
  exact (h op).comp ((hargs false (fun _ => Env.empty) (fun x => nomatch x)).prod
    (hargs true (fun _ => Env.empty) (fun x => nomatch x)))

end Binary

/-- A binary scoped term projects both arguments from one encoded input. -/
theorem polyTime_binaryTerm {Op A : Type} {applyOp : Op → A → A → A} {e : A ↪ List Bool}
    (h : ∀ op, ComputableInPolyTime (fun p : A × A => applyOp op p.1 p.2) (encPair e e) e)
    (op : Op) :
    ComputableInPolyTime (fun p => (Binary.term op).denote (Binary.algebra applyOp)
      (Binary.pairEnv p)) (encPair e e) e := by
  apply Term.computableInPolyTime (Binary.preservesPolyTime h) (Binary.term op)
  intro s x
  cases x with
  | zero => exact ComputableInPolyTime.fst e e
  | succ x =>
    cases x with
    | zero => exact ComputableInPolyTime.snd e e
    | succ x => nomatch x

/-- Machine certificate for the XOR term of the binary word language. -/
theorem wordXor_polyTime :
    ComputableInPolyTime (fun p : List Bool × List Bool => p.1.zipWith Bool.xor p.2)
      (encPair encBits encBits) encBits :=
  polyTime_binaryTerm (applyOp := fun op x y => List.zipWith op x y) (e := encBits)
    (fun _ => by polytime) Bool.xor

end IPFunctor.ScopedSignature
