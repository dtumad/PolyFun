/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Free.Cost
public import PolyFun.PFunctor.Handler.Free
public import PolyFun.PFunctor.Handler.Sum

/-!
# Charges through handlers

A handler implements the calls of an interface `P`. This module relates the charge bounds and
costs of `PolyFun.PFunctor.Free.Cost` to the runs of programs through handlers.

## Handlers implemented by free programs

`h.WithinCharge d c` says that the implementation `h a` of each call at `a` stays within `c a`
under the target charge `d`. Simulating a program within budget through such a handler stays
within the same budget (`FreeM.IsChargeBound.liftM`), also for stateful handlers whose step
bound holds from every state (`FreeM.IsChargeBound.run_liftM`). Identity, lens and sum handlers
are within their obvious charges, and certificates compose (`WithinCharge.comp`). In value form,
`handlerCost d h` is the worst-case cost of each implementation, with equations for identity, lens
and sum handlers and the bound `handlerCost_comp_le` for composites.

## Running in any monad

`h.withCharge c` runs `h` while keeping the amount spent as state: a call at `a` adds `c a`
before it runs. Forgetting the state recovers the handler (`fst_map_run_liftM_withCharge`), and on
every possible result of a run of a program within budget `B`, the amount spent is at most `B`
(`FreeM.IsChargeBound.le_of_canReturn_run_liftM_withCharge`). This is an instance of resource
growth (`FreeM.IsChargeBound.le_of_canReturn_run_liftM`): if each call at `a` raises a measure `f`
of the handler state by at most `c a`, then a program within budget `B` raises it by at most `B`.

`h.withBudget c B` refuses a call that would spend more than `B`. On a program within budget it
never refuses (`run_liftM_withBudget_of_isChargeBound`).
-/

@[expose] public section

universe uA uB uA₂ uA₃ v w

namespace PFunctor

namespace Handler

variable {P : PFunctor.{uA, uB}} {Q : PFunctor.{uA₂, uB}} {R : PFunctor.{uA₃, uB}}

/-! ## Charge certificates for free handlers -/

section Certificate

/-- The implementation of each call at `a` stays within `c a` under the target charge `d`. -/
def WithinCharge {ω : Type w} [Add ω] [LE ω] [Zero ω] (h : Handler (FreeM Q) P) (d : Q.A → ω)
    (c : P.A → ω) : Prop :=
  ∀ a, (h a).IsChargeBound d (c a)

theorem WithinCharge.sum {ω : Type w} [Add ω] [LE ω] [Zero ω] {f : Handler (FreeM R) P}
    {g : Handler (FreeM R) Q} {d : R.A → ω} {c₁ : P.A → ω} {c₂ : Q.A → ω}
    (hf : f.WithinCharge d c₁) (hg : g.WithinCharge d c₂) :
    (sum f g).WithinCharge d (Sum.elim c₁ c₂) := by
  rintro (a | a)
  · exact hf a
  · exact hg a

variable {ω : Type w} [AddCommMonoid ω] [PartialOrder ω]

theorem withinCharge_id (d : Q.A → ω) : (Handler.id Q).WithinCharge d d :=
  fun a => (FreeM.isChargeBound_lift_iff a).2 (by rw [zero_add])

theorem withinCharge_ofLens (l : Lens P Q) (d : Q.A → ω) :
    (ofLens l).WithinCharge d (d ∘ l.toFunA) :=
  fun a => ⟨by rw [zero_add]; rfl, fun _ => by rw [zero_add]; exact le_rfl⟩

theorem WithinCharge.comp [IsOrderedAddMonoid ω] {second : Handler (FreeM R) Q}
    {first : Handler (FreeM Q) P} {e : R.A → ω} {d : Q.A → ω} {c : P.A → ω}
    (hs : second.WithinCharge e d) (hf : first.WithinCharge d c) :
    (second.comp first).WithinCharge e c :=
  fun a => (hf a).liftM second fun b => hs b

end Certificate

/-! ## Instrumentation -/

section Instrumentation

variable {m : Type uB → Type v} {ω : Type uB}

/-- Instrument a handler with a charge: a call at `a` adds `c a` to the amount spent, kept as
state, and then runs the handler. -/
def withCharge [Functor m] [Add ω] (h : Handler m P) (c : P.A → ω) : Handler (StateT ω m) P :=
  fun a s => (fun b => (b, s + c a)) <$> h a

@[simp]
theorem run_withCharge [Functor m] [Add ω] (h : Handler m P) (c : P.A → ω) (a : P.A) (s : ω) :
    (h.withCharge c a).run s = (fun b => (b, s + c a)) <$> h a :=
  rfl

/-- Forgetting the amount spent recovers the uninstrumented run. -/
theorem fst_map_run_liftM_withCharge [Monad m] [LawfulMonad m] [Add ω] (h : Handler m P)
    (c : P.A → ω) {α : Type uB} (x : FreeM P α) (s : ω) :
    Prod.fst <$> (x.liftM (h.withCharge c)).run s = x.liftM h := by
  induction x using FreeM.rec generalizing s with
  | pure a => simp [FreeM.liftM]
  | liftBind a r ih =>
    change Prod.fst <$> (h.withCharge c a >>= fun b => (r b).liftM (h.withCharge c)).run s =
      h a >>= fun b => (r b).liftM h
    simp [StateT.run_bind, bind_map_left, map_bind, ih]

/-- Run a handler under a budget: a call at `a` that would bring the amount spent above `B`
fails; any other call is charged and run. -/
def withBudget [Monad m] [Add ω] [LE ω] [DecidableLE ω] (h : Handler m P) (c : P.A → ω)
    (B : ω) : Handler (StateT ω (OptionT m)) P :=
  fun a s => if s + c a ≤ B then OptionT.lift ((fun b => (b, s + c a)) <$> h a) else failure

/-- A program within budget never meets the budget gate: running it under `withBudget` is running
it under `withCharge`. -/
theorem run_liftM_withBudget_of_isChargeBound [Monad m] [LawfulMonad m] [AddCommMonoid ω]
    [PartialOrder ω] [DecidableLE ω] (h : Handler m P) (c : P.A → ω) {α : Type uB}
    {x : FreeM P α} {B s : ω} (hx : x.IsChargeBound c B s) :
    ((x.liftM (h.withBudget c B)).run s).run = some <$> (x.liftM (h.withCharge c)).run s := by
  induction x using FreeM.rec generalizing s with
  | pure a => simp [FreeM.liftM]
  | liftBind a r ih =>
    change ((h.withBudget c B a >>= fun b => (r b).liftM (h.withBudget c B)).run s).run =
      some <$> (h.withCharge c a >>= fun b => (r b).liftM (h.withCharge c)).run s
    have hs : s + c a ≤ B := hx.1
    simp only [StateT.run_bind, run_withCharge, bind_map_left, map_bind]
    simp only [withBudget, StateT.run, hs, ite_true, OptionT.run_bind_lift, bind_map_left]
    exact bind_congr fun b => ih b (hx.2 b)

end Instrumentation

/-! ## Value form -/

section Cost

variable {ω : Type w} [AddCommMonoid ω] [CompleteLattice ω] [CanonicallyOrderedAdd ω]

@[simp]
theorem handlerCost_id (d : Q.A → ω) : FreeM.handlerCost d (Handler.id Q) = d :=
  funext fun a => FreeM.cost_lift a

@[simp]
theorem handlerCost_ofLens (l : Lens P Q) (d : Q.A → ω) :
    FreeM.handlerCost d (ofLens l) = d ∘ l.toFunA :=
  funext fun a => by
    change d (l.toFunA a) + ⨆ _ : Q.B (l.toFunA a), (0 : ω) = d (l.toFunA a)
    rw [FreeM.iSup_zero_eq_zero, add_zero]

omit [CanonicallyOrderedAdd ω] in
@[simp]
theorem handlerCost_sum (f : Handler (FreeM R) P) (g : Handler (FreeM R) Q) (d : R.A → ω) :
    FreeM.handlerCost d (sum f g) = Sum.elim (FreeM.handlerCost d f) (FreeM.handlerCost d g) :=
  funext fun | .inl _ => rfl | .inr _ => rfl

omit [CanonicallyOrderedAdd ω] in
/-- A composite handler costs at most its first stage, charged by the cost of the second. -/
theorem handlerCost_comp_le [IsOrderedAddMonoid ω] (second : Handler (FreeM R) Q)
    (first : Handler (FreeM Q) P) (e : R.A → ω) :
    FreeM.handlerCost e (second.comp first) ≤
      FreeM.handlerCost (FreeM.handlerCost e second) first :=
  fun a => FreeM.cost_liftM_le e second (first a)

end Cost

end Handler

namespace FreeM

variable {P : PFunctor.{uA, uB}} {Q : PFunctor.{uA₂, uB}} {α : Type uB}

/-! ## Stateful handlers implemented by free programs -/

section Stateful

variable {ω : Type w} [AddCommMonoid ω] [PartialOrder ω] [IsOrderedAddMonoid ω] {B s : ω}

/-- **Stateful-handler transfer.** If, from every state, the implementation of each call at `a`
stays within `c a` under the target charge `d`, then from every state the simulation of a
program within budget `B` under `c` stays within `B` under `d`. -/
theorem IsChargeBound.run_liftM {σ : Type uB} (h : Handler (StateT σ (FreeM Q)) P)
    {c : P.A → ω} {d : Q.A → ω} (hstep : ∀ a σ₁, ((h a).run σ₁).IsChargeBound d (c a))
    {x : FreeM P α} (hx : x.IsChargeBound c B s) (σ₀ : σ) :
    ((x.liftM h).run σ₀).IsChargeBound d B s := by
  induction x using FreeM.rec generalizing s σ₀ with
  | pure a => exact hx
  | liftBind a r ih =>
    change ((h a >>= fun b => (r b).liftM h).run σ₀).IsChargeBound d B s
    rw [StateT.run_bind]
    have hh := (hstep a σ₀).add_left s
    rw [add_zero] at hh
    exact hh.bind_of_le hx.1 fun p s' hs' => (ih p.1 (hx.2 p.1) p.2).mono_spent hs'

end Stateful

/-! ## Resource growth in any monad -/

section Growth

variable {m : Type uB → Type v} [Monad m] [LawfulMonad m] [MonadAttach m] [LawfulMonadAttach m]
  {ω : Type w} [AddCommMonoid ω] [PartialOrder ω] [IsOrderedAddMonoid ω] {B s : ω}

/-- **Resource growth.** If each call at `a` raises a measure `f` of the handler state by at most
`c a`, then on every possible result of running a program within budget `B` from a state whose
measure is at most the amount already spent, the measure is at most `B`. -/
theorem IsChargeBound.le_of_canReturn_run_liftM {σ : Type uB} (h : Handler (StateT σ m) P)
    (f : σ → ω) {c : P.A → ω}
    (hstep : ∀ a σ₁ z, MonadAttach.CanReturn ((h a).run σ₁) z → f z.2 ≤ f σ₁ + c a)
    {x : FreeM P α} (hx : x.IsChargeBound c B s) {σ₀ : σ} (hσ : f σ₀ ≤ s) {z : α × σ}
    (hz : MonadAttach.CanReturn ((x.liftM h).run σ₀) z) : f z.2 ≤ B := by
  induction x using FreeM.rec generalizing s σ₀ with
  | pure a =>
    have := LawfulMonadAttach.eq_of_canReturn_pure (m := m) hz
    subst this
    exact hσ.trans hx
  | liftBind a r ih =>
    change MonadAttach.CanReturn ((h a >>= fun b => (r b).liftM h).run σ₀) z at hz
    rw [StateT.run_bind] at hz
    obtain ⟨p, hp, hz⟩ := LawfulMonadAttach.canReturn_bind_imp' hz
    exact ih p.1 (hx.2 p.1) ((hstep a σ₀ p hp).trans (add_le_add hσ le_rfl)) hz

/-- On every possible result of an instrumented run of a program within budget `B`, the amount
spent is at most `B`. -/
theorem IsChargeBound.le_of_canReturn_run_liftM_withCharge {ω : Type uB} [AddCommMonoid ω]
    [PartialOrder ω] [IsOrderedAddMonoid ω] {B s : ω} (h : Handler m P) {c : P.A → ω}
    {x : FreeM P α} (hx : x.IsChargeBound c B s) {z : α × ω}
    (hz : MonadAttach.CanReturn ((x.liftM (h.withCharge c)).run s) z) : z.2 ≤ B := by
  refine hx.le_of_canReturn_run_liftM (h.withCharge c) id (fun a σ₁ z hz => ?_) le_rfl hz
  obtain ⟨b, -, rfl⟩ := LawfulMonadAttach.canReturn_map_imp' hz
  exact le_rfl

end Growth

end FreeM

end PFunctor
