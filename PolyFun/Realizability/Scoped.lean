/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.IPFunctor.Scoped.Interpretation
public import PolyFun.Realizability.StepClass

/-!
# Admissible interpretations of scoped terms

Fix a representation for each semantic sort. An interpretation preserves admissibility when
each constructor acts admissibly on argument meanings, including meanings under fresh binders.
Then every fixed term denotes an admissible function of the input whenever its free variables do.
-/

public section

universe u v w z r

namespace IPFunctor.ScopedSignature

open PFunctor (StepClass)

variable {S : Type u} {σ : ScopedSignature.{u, v, w} S} {V : S → Type z}
  {C : StepClass.{z, r}} {repr : (s : S) → C.Str (V s)} {ι : Type z} {input : C.Str ι}
  {Γ Δ : List S}

/-- Every variable lookup is an admissible function of the input. -/
@[expose] def Env.Admissible (C : StepClass.{z, r}) (repr : (s : S) → C.Str (V s))
    (input : C.Str ι) (ρ : ι → Env V Γ) : Prop :=
  ∀ {s} (x : ScopedVar Γ s), C.Hom input (repr s) (fun i => ρ i s x)

theorem Env.Admissible.empty : Env.Admissible C repr input (fun _ => Env.empty) :=
  fun x => nomatch x

/-- A bound variable can read an admissible value computed from the input. -/
theorem Env.Admissible.cons {s : S} {ρ : ι → Env V Γ} {value : ι → V s}
    (hρ : Env.Admissible C repr input ρ) (hv : C.Hom input (repr s) value) :
    Env.Admissible C repr input (fun i => Env.cons (value i) (ρ i)) := by
  intro a x
  cases x with
  | zero => exact hv
  | succ x => exact hρ x

/-- Join the new block of bound variables to the enclosing environment. -/
theorem Env.Admissible.append {ξ : ι → Env V Δ} {ρ : ι → Env V Γ}
    (hξ : Env.Admissible C repr input ξ) (hρ : Env.Admissible C repr input ρ) :
    Env.Admissible C repr input (fun i => Env.append (ξ i) (ρ i)) := by
  induction Δ with
  | nil => exact hρ
  | cons s Δ ih =>
    exact Env.Admissible.cons
      (ih (ξ := fun i a x => ξ i a (.succ x)) (fun x => hξ (.succ x))) (hξ .zero)

/-- Each constructor preserves admissibility when its arguments can be evaluated at
every admissible assignment to their bound variables. -/
@[expose] def Interpretation.PreservesAdmissible (alg : Interpretation σ V)
    (C : StepClass.{z, r}) (repr : (s : S) → C.Str (V s)) : Prop :=
  ∀ {ι : Type z} (input : C.Str ι) {s} (op : σ.Op s)
    (args : (p : σ.Arg op) → ι → Env V (σ.binders op p) → V (σ.sort op p)),
    (∀ p (ξ : ι → Env V (σ.binders op p)), Env.Admissible C repr input ξ →
      C.Hom input (repr (σ.sort op p)) (fun i => args p i (ξ i))) →
    C.Hom input (repr s) (fun i => alg op (fun p η => args p i η))

/-- The meaning of a fixed term is admissible in every admissible environment. -/
theorem Term.denote_admissible {alg : Interpretation σ V} {s : S} (t : σ.Term Γ s)
    (h : alg.PreservesAdmissible C repr) {ρ : ι → Env V Γ} (hρ : Env.Admissible C repr input ρ) :
    C.Hom input (repr s) (fun i => t.denote alg (ρ i)) := by
  induction t using Term.inductionOn with
  | hvar Γ s x => exact hρ x
  | hnode Γ s op args ih =>
    apply h input op (fun p i η => (args p).denote alg (Env.append η (ρ i)))
    exact fun p ξ hξ => ih p (hξ.append hρ)

namespace Binary

/-- A one-sorted signature whose operations have two arguments in the ambient scope. -/
@[expose, reducible] def signature (Op : Type v) : ScopedSignature Unit where
  Op _ := Op
  Arg _ := Bool
  binders _ _ := []
  sort _ _ := ()

/-- Interpret a tag as a binary operation, with its left argument at position `false`. -/
@[expose] def algebra {Op : Type v} {A : Type z} (applyOp : Op → A → A → A) :
    Interpretation (signature Op) (fun _ => A) :=
  fun op args => applyOp op (args false Env.empty) (args true Env.empty)

/-- Apply an operation to the first two variables in their context order. -/
@[expose] def term {Op : Type v} (op : Op) : (signature Op).Term [(), ()] () :=
  Term.node op fun right => if right then .var (.succ .zero) else .var .zero

/-- The two variables receive the two fields of the input pair. -/
@[expose] def pairEnv {A : Type z} (p : A × A) : Env (fun _ : Unit => A) [(), ()] :=
  Env.cons p.1 (Env.single p.2)

@[simp] theorem denote_term {Op : Type v} {A : Type z} (applyOp : Op → A → A → A)
    (op : Op) (p : A × A) : (term op).denote (algebra applyOp) (pairEnv p) = applyOp op p.1 p.2 :=
  rfl

/-- Pair the two admissible arguments before applying their primitive operation. -/
theorem preservesAdmissible {Op : Type v} {A : Type z} {applyOp : Op → A → A → A}
    {repr : C.Str A} [P : C.HasProd]
    (h : ∀ op, C.Hom (P.prod repr repr) repr (fun p => applyOp op p.1 p.2)) :
    Interpretation.PreservesAdmissible (σ := signature Op) (algebra applyOp) C
      (fun _ => repr) := by
  intro ι input s op args hargs
  exact C.comp_mem (P.pair_mem (hargs false (fun _ => Env.empty) (fun x => nomatch x))
    (hargs true (fun _ => Env.empty) (fun x => nomatch x))) (h op)

/-- A binary term reads both of its variables from one represented product. -/
theorem denote_term_admissible {Op : Type v} {A : Type z} {applyOp : Op → A → A → A}
    {repr : C.Str A} [P : C.HasProd]
    (h : ∀ op, C.Hom (P.prod repr repr) repr (fun p => applyOp op p.1 p.2)) (op : Op) :
    C.Hom (P.prod repr repr) repr (fun p => (term op).denote (algebra applyOp) (pairEnv p)) := by
  apply (term op).denote_admissible (preservesAdmissible h)
  intro s x
  cases x with
  | zero => exact P.fst_mem repr repr
  | succ x =>
    cases x with
    | zero => exact P.snd_mem repr repr
    | succ x => nomatch x

end Binary

end IPFunctor.ScopedSignature
