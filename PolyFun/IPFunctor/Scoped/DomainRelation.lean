/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.IPFunctor.Scoped.Domain

/-!
# Positional correspondence of semantic environments

`ScopedEnv.Pointwise` compares the values at equal de Bruijn positions, independently of the
syntax of their sorts. This file shows that it is preserved by domain transport, and by a
whole-group least fixed point when the group's unfolding preserves it.
-/

public section

open OmegaCompletePartialOrder

universe u v

namespace IPFunctor
namespace ScopedDomain.Env

variable {S : Type u} {T : Type v} {D : S → PointedDomain} {E : T → PointedDomain}
  {Γ : List S} {Δ : List T}

/-- Domain transport preserves the values at their binding positions. -/
theorem pointwise_reindex_right {U : Type*} {F : U → PointedDomain}
    {η : Env D Γ} {ζ : Env E Δ} (h : ScopedEnv.Pointwise η ζ)
    (f : T → U) (hf : ∀ a, F (f a) = E a) :
    ScopedEnv.Pointwise η (reindex F f hf ζ) := by
  intro a b x y he
  induction y using ScopedVar.map_inductionOn f with
  | h b y =>
    rw [reindex_map]
    exact (h x y (by simpa only [ScopedVar.index_map] using he)).trans
      (PointedDomain.cast_heq _ _).symm

/-- Domain transport of the source preserves positional correspondence. -/
theorem pointwise_reindex_left {U : Type*} {F : U → PointedDomain}
    {η : Env D Γ} {ζ : Env E Δ} (h : ScopedEnv.Pointwise η ζ)
    (f : S → U) (hf : ∀ a, F (f a) = D a) :
    ScopedEnv.Pointwise (reindex F f hf η) ζ :=
  ScopedEnv.Pointwise.symm (pointwise_reindex_right (ScopedEnv.Pointwise.symm h) f hf)

/-- Domain transport is the unique target environment with the corresponding values. -/
theorem pointwise_reindex_eq {f : S → T} (hf : ∀ a, E (f a) = D a)
    {η : Env D Γ} {ζ : Env E (Γ.map f)} (h : ScopedEnv.Pointwise η ζ) :
    reindex E f hf η = ζ := by
  funext b x
  induction x using ScopedVar.map_inductionOn f with
  | h a x =>
    rw [reindex_map, PointedDomain.cast_eq_iff]
    exact h x (x.map f) (ScopedVar.index_map f x).symm

/-- A whole-group unfolding that preserves correspondence preserves its least fixed point. -/
theorem fixGroup_pointwise (f : S → T) (hf : ∀ a, E (f a) = D a)
    {Ξ : List S} (rhs : (i : Fin Ξ.length) → Env D (Ξ ++ Γ) →𝒄 D Ξ[i])
    (rhs' : (j : Fin (Ξ.map f).length) → Env E (Ξ.map f ++ Δ) →𝒄 E (Ξ.map f)[j])
    (η : Env D Γ) (ζ : Env E Δ)
    (h : ∀ (ξ : Env D Ξ) (ψ : Env E (Ξ.map f)), ScopedEnv.Pointwise ξ ψ →
      ∀ i j, i.val = j.val →
        HEq (rhs i (ScopedEnv.append ξ η)) (rhs' j (ScopedEnv.append ψ ζ))) :
    ScopedEnv.Pointwise (fixGroup rhs η) (fixGroup rhs' ζ) := by
  have hfix := fixGroup_fusion E rhs rhs' η ζ (reindex E f hf)
    (reindex_bot E f hf) (fun ξ => pointwise_reindex_eq hf
      (ScopedEnv.Pointwise.ofFin (List.length_map f).symm _ _
        (h ξ _ (pointwise_reindex_right (ScopedEnv.Pointwise.refl ξ) f hf))))
  rw [← hfix]
  exact fun {_ _} x y he => pointwise_reindex_right
    (ScopedEnv.Pointwise.refl (fixGroup rhs η)) f hf x y he

end ScopedDomain.Env
end IPFunctor
