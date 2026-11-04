/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Free.Cost.Tactic

/-!
# Charge bounds and worst-case costs on concrete programs

Checks for `PolyFun.PFunctor.Free.Cost`.
-/

public section

open PFunctor PFunctor.FreeM

namespace PolyFunTest.Charge

/-- Two kinds of call, each with three answers. -/
abbrev Pq : PFunctor := ⟨Bool, fun _ => Fin 3⟩

noncomputable def chg : Pq.A → ℕ∞ := fun a => cond a 2 1

def chgN : Pq.A → ℕ := fun a => cond a 2 1

def prog : FreeM Pq Nat := do
  let x ← FreeM.lift (P := Pq) true
  let y ← FreeM.lift (P := Pq) false
  if x.val = 0 then
    let _ ← FreeM.lift (P := Pq) true
    pure y.val
  else pure (x.val + y.val)

example : cost chg prog = 5 := by
  cost_bound [prog, chg]

example : IsChargeBound prog chgN 5 := by
  cost_bound [prog, chgN]

example : ¬ IsChargeBound prog chgN 4 := by
  cost_bound [prog, chgN]

example : IsChargeBound prog chgN 5 := by
  simp [prog, chgN]

example : ¬ IsChargeBound prog chgN 4 := by
  simp [prog, chgN]

end PolyFunTest.Charge
