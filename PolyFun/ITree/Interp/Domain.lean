/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.ITree.Interp.Stateful
public import PolyFun.ITree.DomainLaws

/-!
# Continuous interpretations of stateful handlers

A per-operation bound comparing interpretations passes to all clients of a stateful handler,
including clients and operation implementations which continue forever. The proof uses the
leastness of the target's interpretation of the handler loop. Silent guards are free.
-/

public section

open OmegaCompletePartialOrder
open PFunctor.Resumption (ContinuousAlgebra)

namespace ITree

universe u uQA uQB uD uE

variable {P : PFunctor.{u, u}} {Q : PFunctor.{uQA, uQB}} {S A : Type u}
  {D : Type uD} {E : Type uE} [OmegaCompletePartialOrder D] [OrderBot D]
  [OmegaCompletePartialOrder E] [OrderBot E]
  (h : PFunctor.Handler (StateT S (ITree Q)) P)
  (source : ContinuousAlgebra P E) (target : ContinuousAlgebra Q D)

/-- A local upper estimate for every operation bounds the operational stateful interpreter. -/
theorem denote_interp_run_le (observe : E → S → D)
    (localBound : ∀ a (k : P.B a → E) s,
      denote (fun out => observe (k out.1) out.2) target (h a s) ≤ observe (source a k) s)
    (ret : A → E) (tree : ITree P A) (s : S) :
    denote (fun out => observe (ret out.1) out.2) target ((interp h tree).run s) ≤
      observe (denote ret source tree) s := by
  rw [interp_run_eq_iter]
  refine denote_iter_le _ target (StateT.stateBody (interpStep h))
    (fun x : ITree P A × S => observe (denote ret source x.1) x.2) ?_ (tree, s)
  rintro ⟨t, state⟩
  rcases ht : shape' t with ⟨head, next⟩
  cases head with
  | pure a => obtain rfl := eq_pure_of_dest ht; simp [stateBody_interpStep_pure]
  | step => obtain rfl := eq_step_of_dest ht; simp [stateBody_interpStep_step]
  | query a =>
    obtain rfl := eq_query_of_dest ht
    simp only [stateBody_interpStep_query, bind_eq_bind, denote_bind, denote_pure, Sum.elim_inl,
      denote_query]
    exact localBound a (fun b => denote ret source (next b)) state

private theorem denote_mono_ret {X : Type*} (x : ITree Q X) {f g : X → D} (hfg : f ≤ g) :
    denote f target x ≤ denote g target x := by
  apply denote_le f target (denote g target)
  intro t
  rw [denote_eq g target t]
  change (match shape' t with
    | ⟨.pure a, _⟩ => f a
    | ⟨.step, k⟩ => denote g target (k PUnit.unit)
    | ⟨.query a, k⟩ => target a (fun b => denote g target (k b))) ≤ _
  rcases shape' t with ⟨head, k⟩
  cases head with
  | pure a => exact hfg a
  | step => rfl
  | query => rfl

/-- Exact local agreement extends to the complete operational interpreter when observation
preserves increasing suprema and takes divergence to bottom. -/
theorem denote_interp_run (observe : S → E →𝒄 D) (strict : ∀ s, observe s ⊥ = ⊥)
    (localEq : ∀ a (k : P.B a → E) s,
      denote (fun out => observe out.2 (k out.1)) target (h a s) = observe s (source a k))
    (ret : A → E) (tree : ITree P A) (s : S) :
    denote (fun out => observe out.2 (ret out.1)) target ((interp h tree).run s) =
      observe s (denote ret source tree) := by
  refine le_antisymm (denote_interp_run_le h source target (fun e s => observe s e)
    (fun a k s => (localEq a k s).le) _ _ _) ?_
  let actual (t : ITree P A) (s : S) :=
    denote (fun out => observe out.2 (ret out.1)) target ((interp h t).run s)
  change _ ≤ actual tree s
  rw [denote_eq_fix]
  change observe s (ωSup ((domainStep ret source).approximants.map (Pi.evalOrderHom tree))) ≤ _
  rw [(observe s).continuous]
  apply ωSup_le
  intro n
  change observe s ((domainStep ret source).approximants n tree) ≤ actual tree s
  induction n generalizing tree s with
  | zero => simpa only [ContinuousHom.approximants_zero, Pi.bot_apply, strict] using
      (bot_le : ⊥ ≤ actual tree s)
  | succ n ih =>
    rw [ContinuousHom.approximants_succ]
    rcases ht : shape' tree with ⟨head, next⟩
    cases head with
    | pure a =>
      obtain rfl := eq_pure_of_dest ht
      simp [domainStep, actual, interp_run_pure]
    | step =>
      obtain rfl := eq_step_of_dest ht
      simpa only [domainStep, ContinuousHom.ofFun_apply, shape'_step, actual, interp_run_step,
        denote_step] using ih (tree := next PUnit.unit) (s := s)
    | query a =>
      obtain rfl := eq_query_of_dest ht
      simp only [domainStep, ContinuousHom.ofFun_apply, shape'_query, actual, interp_run_query,
        bind_eq_bind, denote_bind, denote_step]
      rw [← localEq]
      exact denote_mono_ret target _ fun z => ih (tree := next z.1) (s := z.2)

end ITree
