/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.IPFunctor.Scoped.Basic

/-!
# Environments of typed contexts

`ScopedEnv V Γ` assigns a value of `V a` to every variable `x : ScopedVar Γ a`. It is the one
environment of scoped syntax: interpretations, domain interpretations and relations between
them all read it, and lookup is application, so evaluating a variable is definitional.

* `empty`, `cons`, `append`, `single` and `ofFin` build environments;
* `rename` reads an environment along a renaming, and `map` changes its values;
* `Forall₂ R η ζ` relates two environments of one context at every variable;
* `Pointwise η ζ` compares environments of different contexts at equal positions.
-/

public section

universe u v z z'

namespace IPFunctor

/-- A value for every variable of a typed context. -/
abbrev ScopedEnv {S : Type u} (V : S → Type z) (Γ : List S) := ∀ a, ScopedVar Γ a → V a

namespace ScopedEnv

variable {S : Type u} {V : S → Type z} {W : S → Type z'} {Γ Δ : List S}

/-- The unique environment of the empty context. -/
@[expose] def empty : ScopedEnv V [] := fun _ x => nomatch x

/-- Extend an environment by its nearest variable. -/
@[expose] def cons {a : S} (x : V a) (η : ScopedEnv V Γ) : ScopedEnv V (a :: Γ)
  | _, .zero => x
  | _, .succ v => η _ v

@[simp] theorem cons_zero {a : S} (x : V a) (η : ScopedEnv V Γ) : cons x η a .zero = x := rfl

@[simp] theorem cons_succ {a b : S} (x : V a) (η : ScopedEnv V Γ) (v : ScopedVar Γ b) :
    cons x η b v.succ = η b v := rfl

/-- An environment of a nonempty context is its nearest value and the rest. -/
theorem cons_head_tail {a : S} (η : ScopedEnv V (a :: Γ)) :
    cons (η a .zero) (fun b x => η b x.succ) = η := by
  funext b x
  cases x <;> rfl

/-- Values for new binders, followed by the surrounding environment. -/
@[expose] def append : {Ξ : List S} → ScopedEnv V Ξ → ScopedEnv V Γ → ScopedEnv V (Ξ ++ Γ)
  | [], _, η => η
  | _ :: _, ξ, η => cons (ξ _ .zero) (append (fun _ x => ξ _ x.succ) η)

@[simp] theorem append_nil (ξ : ScopedEnv V []) (η : ScopedEnv V Γ) : append ξ η = η := rfl

/-- The environment of a single variable. -/
@[expose] def single {a : S} (x : V a) : ScopedEnv V [a] := cons x empty

@[simp] theorem single_zero {a : S} (x : V a) : single x a .zero = x := rfl

/-- Assemble an environment from its values in context order. -/
@[expose] def ofFin : {Ξ : List S} → ((i : Fin Ξ.length) → V Ξ[i]) → ScopedEnv V Ξ
  | _ :: _, f, _, .zero => f 0
  | _ :: _, f, _, .succ x => ofFin (fun i => f i.succ) _ x

/-- Assembly separates the nearest position from the remaining positions. -/
theorem ofFin_cons {a : S} (xs : (i : Fin (a :: Γ).length) → V (a :: Γ)[i]) :
    ofFin xs = cons (xs 0) (ofFin (fun i => xs i.succ)) := by
  funext b x
  cases x <;> rfl

/-- Read an environment along a renaming. -/
@[expose] def rename (ρ : ScopedSignature.Renaming Γ Δ) (η : ScopedEnv V Δ) :
    ScopedEnv V Γ := fun _ x => η _ (ρ x)

@[simp] theorem rename_apply (ρ : ScopedSignature.Renaming Γ Δ) (η : ScopedEnv V Δ)
    {a : S} (x : ScopedVar Γ a) : rename ρ η a x = η a (ρ x) := rfl

@[simp] theorem rename_id (η : ScopedEnv V Γ) : rename (fun x => x) η = η := rfl

/-- Reading along two renamings reads along their composite. -/
theorem rename_rename {Θ : List S} (ρ : ScopedSignature.Renaming Γ Δ)
    (τ : ScopedSignature.Renaming Δ Θ) (η : ScopedEnv V Θ) :
    rename ρ (rename τ η) = rename (fun x => τ (ρ x)) η := rfl

/-- Renaming under one binder renames the rest of the environment. -/
theorem rename_cons (ρ : ScopedSignature.Renaming Γ Δ) {a : S} (x : V a)
    (η : ScopedEnv V Δ) : rename (ScopedSignature.Renaming.lift ρ a) (cons x η) =
      cons x (rename ρ η) := by
  funext b v
  cases v <;> rfl

/-- Renaming under several binders renames the surrounding environment. -/
theorem rename_append (ρ : ScopedSignature.Renaming Γ Δ) {Ξ : List S}
    (ξ : ScopedEnv V Ξ) (η : ScopedEnv V Δ) :
    rename (ScopedSignature.Renaming.liftMany ρ Ξ) (append ξ η) = append ξ (rename ρ η) := by
  induction Ξ with
  | nil => rfl
  | cons b Ξ ih =>
    funext a x
    cases x with
    | zero => rfl
    | succ x => exact congrFun (congrFun (ih (fun _ x => ξ _ x.succ)) a) x

/-- Transporting a context transports its variables. -/
theorem cast_apply (h : Γ = Δ) (η : ScopedEnv V Γ) {a : S} (x : ScopedVar Γ a) :
    (h ▸ η) a (h ▸ x) = η a x := by
  cases h
  rfl

/-- Change every value of an environment. -/
@[expose] def map (g : ∀ a, V a → W a) (η : ScopedEnv V Γ) : ScopedEnv W Γ :=
  fun a x => g a (η a x)

@[simp] theorem map_apply (g : ∀ a, V a → W a) (η : ScopedEnv V Γ) {a : S}
    (x : ScopedVar Γ a) : map g η a x = g a (η a x) := rfl

theorem map_cons (g : ∀ a, V a → W a) {a : S} (x : V a) (η : ScopedEnv V Γ) :
    map g (cons x η) = cons (g a x) (map g η) := by
  funext b v
  cases v <;> rfl

theorem map_append (g : ∀ a, V a → W a) {Ξ : List S} (ξ : ScopedEnv V Ξ)
    (η : ScopedEnv V Γ) : map g (append ξ η) = append (map g ξ) (map g η) := by
  induction Ξ with
  | nil => rfl
  | cons b Ξ ih =>
    rw [append, append, map_cons, ih]
    rfl

/-! ## Relations -/

/-- Two environments of one context are related at every variable. -/
@[expose] def Forall₂ (R : ∀ a, V a → W a → Prop) (η : ScopedEnv V Γ) (ζ : ScopedEnv W Γ) :
    Prop :=
  ∀ a (x : ScopedVar Γ a), R a (η a x) (ζ a x)

namespace Forall₂

variable {R : ∀ a, V a → W a → Prop}

/-- The empty environments are related. -/
theorem empty : Forall₂ R (ScopedEnv.empty : ScopedEnv V []) ScopedEnv.empty :=
  fun _ x => nomatch x

/-- Related nearest values extend related environments. -/
theorem cons {a : S} {x : V a} {y : W a} {η : ScopedEnv V Γ} {ζ : ScopedEnv W Γ}
    (hxy : R a x y) (h : Forall₂ R η ζ) : Forall₂ R (ScopedEnv.cons x η) (ScopedEnv.cons y ζ)
  | _, .zero => hxy
  | _, .succ v => h _ v

/-- Related single values give related environments. -/
theorem single {a : S} {x : V a} {y : W a} (hxy : R a x y) :
    Forall₂ R (ScopedEnv.single x) (ScopedEnv.single y) :=
  cons hxy empty

/-- Related blocks extend related environments. -/
theorem append {Ξ : List S} {ξ : ScopedEnv V Ξ} {ψ : ScopedEnv W Ξ} {η : ScopedEnv V Γ}
    {ζ : ScopedEnv W Γ} (hx : Forall₂ R ξ ψ) (h : Forall₂ R η ζ) :
    Forall₂ R (ScopedEnv.append ξ η) (ScopedEnv.append ψ ζ) := by
  induction Ξ with
  | nil => exact h
  | cons b Ξ ih => exact cons (hx _ .zero) (ih (fun _ x => hx _ x.succ))

end Forall₂

/-- Environments agree at every shared binding position, across different contexts and
carriers in one universe. -/
@[expose] def Pointwise {T : Type v} {E : T → Type z} {Θ : List T} (η : ScopedEnv V Γ)
    (ζ : ScopedEnv E Θ) : Prop :=
  ∀ {a b} (x : ScopedVar Γ a) (y : ScopedVar Θ b), x.index = y.index → HEq (η a x) (ζ b y)

namespace Pointwise

variable {T : Type v} {E : T → Type z} {Θ : List T}

/-- An environment agrees with itself at every binding position. -/
theorem refl (η : ScopedEnv V Γ) : Pointwise η η := by
  intro a b x y h
  have he := ScopedVar.sigma_eq_of_index_eq x y h
  cases he
  rfl

/-- Positional agreement is symmetric. -/
theorem symm {η : ScopedEnv V Γ} {ζ : ScopedEnv E Θ} (h : Pointwise η ζ) : Pointwise ζ η :=
  fun _ _ e => (h _ _ e.symm).symm

/-- Agreeing fresh values extend agreeing environments. -/
theorem cons {η : ScopedEnv V Γ} {ζ : ScopedEnv E Θ} (h : Pointwise η ζ) {a : S} {b : T}
    {x : V a} {y : E b} (hxy : HEq x y) :
    Pointwise (ScopedEnv.cons x η) (ScopedEnv.cons y ζ) := by
  intro c d v w he
  cases v <;> cases w
  · exact hxy
  · simp only [ScopedVar.index] at he; omega
  · simp only [ScopedVar.index] at he; omega
  · exact h _ _ (Nat.add_right_cancel he)

/-- Transporting a context retains agreement on the left. -/
theorem cast_left {Γ' : List S} (hc : Γ = Γ') {η : ScopedEnv V Γ} {ζ : ScopedEnv E Θ}
    (h : Pointwise η ζ) : Pointwise (hc ▸ η) ζ := by
  cases hc
  exact h

/-- Transporting a context retains agreement on the right. -/
theorem cast_right {Θ' : List T} (hc : Θ = Θ') {η : ScopedEnv V Γ} {ζ : ScopedEnv E Θ}
    (h : Pointwise η ζ) : Pointwise η (hc ▸ ζ) := by
  cases hc
  exact h

/-- Agreement in one context is equality. -/
theorem eq {η ζ : ScopedEnv V Γ} (h : Pointwise η ζ) : η = ζ := by
  funext a x
  exact eq_of_heq (h x x rfl)

/-- Appending agreeing blocks of equal length preserves agreement. -/
theorem append {Ξ : List S} {Ψ : List T} (hl : Ξ.length = Ψ.length) {ξ : ScopedEnv V Ξ}
    {ψ : ScopedEnv E Ψ} {η : ScopedEnv V Γ} {ζ : ScopedEnv E Θ}
    (hx : Pointwise ξ ψ) (he : Pointwise η ζ) :
    Pointwise (ScopedEnv.append ξ η) (ScopedEnv.append ψ ζ) := by
  induction Ξ generalizing Ψ with
  | nil =>
    cases Ψ with
    | nil => exact he
    | cons => simp only [List.length_cons, List.length_nil] at hl; omega
  | cons a Ξ ih =>
    cases Ψ with
    | nil => simp only [List.length_cons, List.length_nil] at hl; omega
    | cons b Ψ =>
      apply Pointwise.cons
      · apply ih (Nat.add_right_cancel hl)
        intro s t x y hi
        exact hx (.succ x) (.succ y) (congrArg (· + 1) hi)
      · exact hx .zero .zero rfl

/-- Agreeing values assemble into agreeing environments. -/
theorem ofFin {Ξ : List S} {Ψ : List T} (hl : Ξ.length = Ψ.length)
    (xs : (i : Fin Ξ.length) → V Ξ[i]) (ys : (j : Fin Ψ.length) → E Ψ[j])
    (h : ∀ i j, i.val = j.val → HEq (xs i) (ys j)) :
    Pointwise (ScopedEnv.ofFin xs) (ScopedEnv.ofFin ys) := by
  induction Ξ generalizing Ψ with
  | nil => intro a b x; exact nomatch x
  | cons a Ξ ih =>
    cases Ψ with
    | nil => simp only [List.length_cons, List.length_nil] at hl; omega
    | cons b Ψ =>
      rw [ofFin_cons, ofFin_cons]
      apply Pointwise.cons
      · exact ih (Nat.add_right_cancel hl) _ _
          (fun i j he => h i.succ j.succ (congrArg (· + 1) he))
      · exact h 0 0 rfl

end Pointwise

end ScopedEnv
end IPFunctor
