/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.IPFunctor.Scoped.Transport
public import PolyFun.IPFunctor.Scoped.Env
public import PolyFun.Control.Domain.Pointed

/-!
# Continuous environments for scoped syntax

`ScopedDomain.Env D Γ` is the `ScopedEnv` of the carriers of `D`, so its plain operations are
`ScopedEnv`'s. This file adds their continuous versions, transport between domains along a sort
map, and least fixed points of recursive groups. Lookup uses binding positions, so reindexing
permits distinct source sorts to become equal, as happens when substituting type parameters.
-/

public section

open OmegaCompletePartialOrder

namespace IPFunctor.ScopedDomain

variable {S T : Type*} {D : S → PointedDomain} {Γ Δ : List S}

/-- One suspended semantic value for each binding position: the scoped environment of the
domains' carriers. -/
abbrev Env (D : S → PointedDomain) (Γ : List S) := ScopedEnv (fun a => D a) Γ

namespace Env

/-- Reading an environment along a renaming is continuous. -/
@[expose] noncomputable def renameContinuous (ρ : ScopedSignature.Renaming Γ Δ) :
    Env D Δ →𝒄 Env D Γ := .ofFun (fun η a x => η a (ρ x)) (by fun_prop)

@[simp] theorem renameContinuous_apply (ρ : ScopedSignature.Renaming Γ Δ) (η : Env D Δ) :
    renameContinuous ρ η = ScopedEnv.rename ρ η := rfl

/-- Assembling environments is continuous in all their components. -/
@[expose] noncomputable def ofFinContinuous {Ξ : List S} :
    ((i : Fin Ξ.length) → D Ξ[i]) →𝒄 Env D Ξ := .ofFun (ScopedEnv.ofFin (V := fun a => D a)) (by
  apply ωScottContinuous.of_apply₂
  intro a
  apply ωScottContinuous.of_apply₂
  intro x
  induction x with
  | zero => exact ωScottContinuous.apply 0
  | succ x ih => exact ih.comp (by fun_prop))

/-- Adding one binding is jointly continuous. -/
@[expose] noncomputable def consContinuous {a : S} :
    (D a × Env D Γ) →𝒄 Env D (a :: Γ) :=
  .ofFun (fun p => ScopedEnv.cons (V := fun a => D a) p.1 p.2) (by
  apply ωScottContinuous.of_apply₂
  intro b
  apply ωScottContinuous.of_apply₂
  intro x
  cases x <;> simp only [ScopedEnv.cons] <;> fun_prop)

@[simp] theorem consContinuous_apply {a : S} (p : D a × Env D Γ) :
    consContinuous p = ScopedEnv.cons (V := fun a => D a) p.1 p.2 := rfl

/-- Adding a binding is continuous in the new value and the environment together. -/
@[fun_prop] theorem ωScottContinuous_cons {α : Type*} [OmegaCompletePartialOrder α] {a : S}
    {f : α → D a} {g : α → Env D Γ} (hf : ωScottContinuous f) (hg : ωScottContinuous g) :
    ωScottContinuous fun t => ScopedEnv.cons (V := fun a => D a) (f t) (g t) :=
  consContinuous.ωScottContinuous.comp (Prod.ωScottContinuous.prodMk hf hg)

/-- A one-variable environment, continuously in its value. -/
@[expose] noncomputable def singleContinuous {a : S} : D a →𝒄 Env D [a] :=
  .ofFun (ScopedEnv.single (V := fun a => D a)) (by
    change ωScottContinuous fun x : D a => ScopedEnv.cons (V := fun a => D a) x ScopedEnv.empty
    fun_prop)

@[simp] theorem singleContinuous_apply {a : S} (x : D a) :
    singleContinuous x = ScopedEnv.single (V := fun a => D a) x := rfl

/-- A meaning in a one-variable environment, as a continuous function of that variable. -/
@[expose] noncomputable def bindOne {a : S} {E : Type*} [OmegaCompletePartialOrder E] :
    (Env D [a] →𝒄 E) →𝒄 (D a →𝒄 E) :=
  .ofFun (fun f => f.comp singleContinuous) (by
    apply ContinuousHom.ωScottContinuous_of_apply
    intro x
    change ωScottContinuous fun f : Env D [a] →𝒄 E => f (singleContinuous x)
    fun_prop)

theorem bindOne_apply {a : S} {E : Type*} [OmegaCompletePartialOrder E]
    (f : Env D [a] →𝒄 E) (x : D a) :
    bindOne f x = f (ScopedEnv.single (V := fun a => D a) x) := rfl

/-- Appending a finite block of bindings is jointly continuous. -/
@[expose] noncomputable def appendContinuous {Ξ : List S} :
    (Env D Ξ × Env D Γ) →𝒄 Env D (Ξ ++ Γ) :=
  .ofFun (fun p => ScopedEnv.append (V := fun a => D a) p.1 p.2) (by
  induction Ξ with
  | nil => exact Prod.ωScottContinuous_snd
  | cons a Ξ ih =>
      change ωScottContinuous (fun p : Env D (a :: Ξ) × Env D Γ => consContinuous
        (p.1 a .zero, ScopedEnv.append (V := fun a => D a) (fun b v => p.1 b (.succ v)) p.2))
      apply (consContinuous).ωScottContinuous.comp
      apply Prod.ωScottContinuous.prodMk
      · fun_prop
      · have h : ωScottContinuous (fun p : Env D (a :: Ξ) × Env D Γ =>
            (((fun b v => p.1 b (.succ v)) : Env D Ξ), p.2)) := by fun_prop
        exact ih.comp h)

/-- Reindex binding positions while transporting their domains. -/
@[expose] noncomputable def reindex (E : T → PointedDomain) (f : S → T)
    (h : ∀ a, E (f a) = D a) : Env D Γ →𝒄 Env E (Γ.map f) :=
  .ofFun (fun η _ x => ScopedVar.mapLookup f (V := fun b => E b)
    (fun {a} v => PointedDomain.cast (h a).symm (η a v)) x) (by
      apply ωScottContinuous.of_apply₂
      intro b
      apply ωScottContinuous.of_apply₂
      intro x
      induction x using ScopedVar.map_inductionOn with
      | h a x =>
          simp only [ScopedVar.mapLookup_map]
          fun_prop)

@[simp] theorem reindex_map (E : T → PointedDomain) (f : S → T)
    (h : ∀ a, E (f a) = D a) (η : Env D Γ) {a : S} (x : ScopedVar Γ a) :
    reindex E f h η (f a) (x.map f) = PointedDomain.cast (h a).symm (η a x) :=
  ScopedVar.mapLookup_map f (V := fun b => E b) _ x

/-- Reindexing by identity performs only context normalization. -/
theorem reindex_id (η : Env D Γ) :
    reindex D id (fun _ => rfl) η = (List.map_id Γ).symm ▸ η := by
  funext a x
  induction x using ScopedVar.map_inductionOn id with
  | h a x =>
      rw [reindex_map, ScopedVar.map_id, ScopedEnv.cast_apply]
      rfl

/-- Transport retains the nearest binding and reindexes the older positions. -/
theorem reindex_cons (E : T → PointedDomain) (f : S → T)
    (h : ∀ a, E (f a) = D a) {a : S} (x : D a) (η : Env D Γ) :
    reindex E f h (ScopedEnv.cons x η) =
      ScopedEnv.cons (V := fun b => E b) (PointedDomain.cast (h a).symm x) (reindex E f h η) := by
  funext b v
  cases v <;> rfl

/-- Changing sorts commutes with changing binding positions, even for noninjective maps. -/
theorem reindex_rename (E : T → PointedDomain) (f : S → T)
    (h : ∀ a, E (f a) = D a) (ρ : ScopedSignature.Renaming Γ Δ) (η : Env D Δ) :
    reindex E f h (ScopedEnv.rename ρ η) =
      ScopedEnv.rename (ScopedSignature.Renaming.map f ρ) (reindex E f h η) := by
  funext b x
  induction x using ScopedVar.map_inductionOn f with
  | h a x => simp only [reindex_map, ScopedEnv.rename_apply, ScopedSignature.Renaming.map_apply]

/-- Consecutive environment transports compose, retaining each binding position. -/
theorem reindex_reindex {U : Type*} (E : T → PointedDomain) (F : U → PointedDomain)
    (f : S → T) (g : T → U) (h : ∀ a, E (f a) = D a) (k : ∀ a, F (g a) = E a)
    (η : Env D Γ) :
    (List.map_map ▸ reindex F g k (reindex E f h η)) =
      reindex F (g ∘ f) (fun a => (k (f a)).trans (h a)) η := by
  funext b x
  induction x using ScopedVar.map_inductionOn (g ∘ f) with
  | h a x =>
      rw [← ScopedVar.map_map f g x, ScopedEnv.cast_apply]
      simp only [ScopedVar.map_map, Function.comp_apply, reindex_map,
        PointedDomain.cast_cast]
      exact (reindex_map F (g ∘ f) _ η x).symm

/-- Environment transport maps the empty information state to itself. -/
@[simp] theorem reindex_bot (E : T → PointedDomain) (f : S → T)
    (h : ∀ a, E (f a) = D a) : reindex E f h (⊥ : Env D Γ) = ⊥ := by
  funext b x
  induction x using ScopedVar.map_inductionOn f with
  | h a x => simp only [reindex_map, Pi.bot_apply, PointedDomain.cast_bot]

/-- Tie a finite, possibly heterogeneous recursive group by one least fixed point.
Every right-hand side sees the entire group and the ambient environment. -/
@[expose] noncomputable def fixGroup {Ξ : List S}
    (rhs : (i : Fin Ξ.length) → Env D (Ξ ++ Γ) →𝒄 D Ξ[i]) :
    Env D Γ →𝒄 Env D Ξ :=
  ContinuousHom.fixContinuous.comp (.ofFun (fun η =>
    ContinuousHom.ofFun (fun ξ => ofFinContinuous
      (fun i => rhs i (appendContinuous (ξ, η))))))

/-- Unfold all declarations in a recursive group simultaneously. -/
theorem fixGroup_unfold {Ξ : List S}
    (rhs : (i : Fin Ξ.length) → Env D (Ξ ++ Γ) →𝒄 D Ξ[i]) (η : Env D Γ) :
    fixGroup rhs η =
      ScopedEnv.ofFin (V := fun a => D a) (fun i => rhs i (ScopedEnv.append (fixGroup rhs η) η)) :=
  (ContinuousHom.map_fix (ContinuousHom.ofFun (fun ξ => ofFinContinuous
    (fun i => rhs i (appendContinuous (ξ, η)))))).symm

/-- A group denotes the least simultaneous prefixed point. -/
theorem fixGroup_le {Ξ : List S}
    (rhs : (i : Fin Ξ.length) → Env D (Ξ ++ Γ) →𝒄 D Ξ[i]) (η : Env D Γ) (ξ : Env D Ξ)
    (h : ScopedEnv.ofFin (V := fun a => D a) (fun i => rhs i (ScopedEnv.append ξ η)) ≤ ξ) :
    fixGroup rhs η ≤ ξ :=
  ContinuousHom.fix_le _ h

/-- Equal group transformers have equal simultaneous least fixed points.
The ambient environments may differ; the whole recursive block is compared at once. -/
theorem fixGroup_congr {Θ Ξ : List S}
    (rhs : (i : Fin Ξ.length) → Env D (Ξ ++ Γ) →𝒄 D Ξ[i])
    (rhs' : (i : Fin Ξ.length) → Env D (Ξ ++ Θ) →𝒄 D Ξ[i])
    (η : Env D Γ) (η' : Env D Θ)
    (h : ∀ ξ i, rhs i (ScopedEnv.append ξ η) = rhs' i (ScopedEnv.append ξ η')) :
    fixGroup rhs η = fixGroup rhs' η' := by
  change ContinuousHom.fix _ = ContinuousHom.fix _
  congr 1
  apply ContinuousHom.ext
  intro ξ
  exact congrArg (ScopedEnv.ofFin (V := fun a => D a)) (funext (h ξ))

/-- Renaming the ambient variables commutes with tying a recursive group. -/
theorem fixGroup_rename {Ξ : List S}
    (rhs : (i : Fin Ξ.length) → Env D (Ξ ++ Γ) →𝒄 D Ξ[i])
    (ρ : ScopedSignature.Renaming Γ Δ) (η : Env D Δ) :
    fixGroup rhs (ScopedEnv.rename ρ η) =
      fixGroup (fun i => (rhs i).comp (renameContinuous (ρ.liftMany Ξ))) η := by
  apply fixGroup_congr
  intro ξ i
  simp only [ContinuousHom.comp_apply, renameContinuous_apply, ScopedEnv.rename_append]

/-- A strict continuous transport commuting with whole-group unfolding preserves
the simultaneous least fixed point. The target may use different sorts and bindings. -/
theorem fixGroup_fusion (E : T → PointedDomain) {Ξ : List S} {Ψ Λ : List T}
    (rhs : (i : Fin Ξ.length) → Env D (Ξ ++ Γ) →𝒄 D Ξ[i])
    (rhs' : (i : Fin Ψ.length) → Env E (Ψ ++ Λ) →𝒄 E Ψ[i])
    (η : Env D Γ) (η' : Env E Λ) (transport : Env D Ξ →𝒄 Env E Ψ)
    (hbot : transport ⊥ = ⊥)
    (hstep : ∀ ξ, transport (ScopedEnv.ofFin (V := fun a => D a)
        (fun i => rhs i (ScopedEnv.append ξ η))) =
      ScopedEnv.ofFin (V := fun b => E b) (fun i => rhs' i (ScopedEnv.append (transport ξ) η'))) :
    transport (fixGroup rhs η) = fixGroup rhs' η' :=
  ContinuousHom.fix_fusion _ _ transport hbot hstep

end Env
end IPFunctor.ScopedDomain
