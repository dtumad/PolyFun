/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.PFunctor.Charge
public import PolyFun.PFunctor.Free.Cost
public import PolyFun.PFunctor.Free.Path.Execution

/-!
# Charges along completed paths

`Path.charge c x p` is the total charge of the calls along the completed path `p` through `x`: the
cost of one run, once every answer is fixed. It is the additive valuation of the path's event
trace (`charge_eq_traceList_charge`).

A structural bound bounds every completed path (`charge_le_of_isChargeBound`). The converse needs
every reachable call to have an answer (`isChargeBound_of_forall_charge_le`, under
`ProgramProgress`): a call with no answers ends no completed path, but `IsChargeBound` still
charges it. The worst-case cost is at least the charge of every completed path
(`charge_le_cost`).
-/

@[expose] public section

universe uA uB v w

namespace PFunctor.FreeM

variable {P : PFunctor.{uA, uB}} {α : Type v} {ω : Type w}

/-- A program in which every reachable call has an answer has a completed path. -/
theorem ProgramProgress.nonempty_path {x : FreeM P α} (hx : x.ProgramProgress) :
    Nonempty (Path x) := by
  induction x using FreeM.rec with
  | pure a => exact ⟨PUnit.unit⟩
  | liftBind a r ih =>
    obtain ⟨⟨b⟩, hr⟩ := hx
    obtain ⟨p⟩ := ih b (hr b)
    exact ⟨⟨b, p⟩⟩

namespace Path

/-- The total charge of the calls along a completed path. -/
def charge [Add ω] [Zero ω] (c : P.A → ω) : (x : FreeM P α) → Path x → ω
  | .pure _, _ => 0
  | .liftBind a next, ⟨answer, tail⟩ => c a + charge c (next answer) tail

variable {c : P.A → ω}

@[simp]
theorem charge_pure [Add ω] [Zero ω] (a : α) (p : Path (pure a : FreeM P α)) :
    charge c (pure a) p = 0 :=
  rfl

theorem charge_liftBind [Add ω] [Zero ω] (a : P.A) (next : P.B a → FreeM P α) (answer : P.B a)
    (tail : Path (next answer)) :
    charge c (FreeM.liftBind a next) ⟨answer, tail⟩ = c a + charge c (next answer) tail :=
  rfl

/-- The charge of a path is the valuation of its event trace by the charge of each call. -/
theorem charge_eq_traceList_charge [AddMonoid ω] (x : FreeM P α) (p : Path x) :
    charge c x p = TraceList.charge (fun i => c i.1) (trace x p) := by
  induction x using FreeM.rec with
  | pure a => rfl
  | liftBind a r ih =>
    rcases p with ⟨b, p⟩
    exact congrArg (c a + ·) (ih b p)

/-- The number of calls along a path is its unit charge. -/
theorem length_eq_charge_one (x : FreeM P α) (p : Path x) :
    length x p = charge (fun _ => 1) x p := by
  induction x using FreeM.rec with
  | pure a => rfl
  | liftBind a r ih =>
    rcases p with ⟨b, p⟩
    rw [length_liftBind, charge_liftBind, ih, add_comm]

section Ordered

variable [AddCommMonoid ω] [PartialOrder ω] {B s : ω}

/-- A structural bound bounds the charge of every completed path. -/
theorem charge_le_of_isChargeBound {x : FreeM P α} (h : x.IsChargeBound c B s) (p : Path x) :
    s + charge c x p ≤ B := by
  induction x using FreeM.rec generalizing s with
  | pure a => simpa using h
  | liftBind a r ih =>
    rcases p with ⟨b, p⟩
    rw [charge_liftBind, ← add_assoc]
    exact ih b (h.2 b) p

/-- When every reachable call has an answer, bounding the completed paths bounds the program. -/
theorem isChargeBound_of_forall_charge_le [CanonicallyOrderedAdd ω]
    {x : FreeM P α} (hx : x.ProgramProgress) (h : ∀ p : Path x, s + charge c x p ≤ B) :
    x.IsChargeBound c B s := by
  induction x using FreeM.rec generalizing s with
  | pure a => simpa using h PUnit.unit
  | liftBind a r ih =>
    obtain ⟨⟨b₀⟩, hr⟩ := hx
    obtain ⟨p₀⟩ := (hr b₀).nonempty_path
    have hpath : ∀ b (p : Path (r b)), (s + c a) + charge c (r b) p ≤ B := fun b p => by
      rw [add_assoc]; exact h ⟨b, p⟩
    exact ⟨le_self_add.trans (hpath b₀ p₀), fun b => ih b (hr b) (hpath b)⟩

end Ordered

/-- The worst-case cost is at least the charge of every completed path. -/
theorem charge_le_cost [AddCommMonoid ω] [CompleteLattice ω] [IsOrderedAddMonoid ω]
    (x : FreeM P α) (p : Path x) : charge c x p ≤ cost c x := by
  induction x using FreeM.rec with
  | pure a => exact le_rfl
  | liftBind a r ih =>
    rcases p with ⟨b, p⟩
    rw [charge_liftBind, cost_liftBind]
    exact add_le_add le_rfl ((ih b p).trans (le_iSup (fun b => cost c (r b)) b))

end Path

end PFunctor.FreeM
