/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Free.Cost.Tactic
public import PolyFun.PFunctor.Free.Cost.Loops
public import PolyFun.PFunctor.Free.Path.Charge
public import PolyFun.PFunctor.Handler.Charge

/-!
# Charge bounds through loops, paths and handlers

Checks for the cost API on the shapes that downstream query accounting uses:

* an adversary making `q` hash queries in a loop and one group operation has the per-kind vector
  budget `q • hash + group`, and pushing it forward along a weighting gives the weighted budget;
* a call with no answers is charged by the structural bound but ends no completed path;
* simulating through a handler that doubles every call doubles a unit budget, statelessly and
  through a counting state;
* instrumented runs stay within budget, and the budget gate is transparent within budget and
  refuses beyond it.
-/

public section

open PFunctor PFunctor.FreeM

namespace PolyFunTest.ChargeHandlers

/-! ## Per-kind budgets -/

/-- Two kinds of query. -/
inductive Op
  | hash
  | group
  deriving DecidableEq

/-- An interface with hash and group queries, each with four answers. -/
abbrev Iface : PFunctor := ⟨Op, fun _ => Fin 4⟩

/-- Count each kind of query separately. -/
def kind (o : Iface.A) : Op → ℕ := Pi.single o 1

/-- `q` hash queries in a loop, then one group operation. -/
def adv (q : ℕ) : FreeM Iface PUnit := do
  forM (List.range q) fun _ => do
    let _ ← FreeM.lift (P := Iface) Op.hash
    pure ()
  let _ ← FreeM.lift (P := Iface) Op.group
  pure ()

/-- The body of the hash loop. -/
def hashOnce : FreeM Iface PUnit := do
  let _ ← FreeM.lift (P := Iface) Op.hash
  pure ()

theorem adv_isChargeBound (q : ℕ) :
    (adv q).IsChargeBound kind (q • kind Op.hash + kind Op.group) := by
  refine IsChargeBound.bind (B₁ := q • kind Op.hash) ?_ fun _ => ?_
  · have h := isChargeBound_forM_const (xs := List.range q) (f := fun _ => hashOnce)
      (c := kind) (B := kind Op.hash) fun _ _ => by simp [hashOnce]
    simpa [hashOnce] using h
  · simp

/-- Weigh a hash query 3 and a group operation 5. -/
def weigh : (Op → ℕ) →+o ℕ where
  toFun v := 3 * v Op.hash + 5 * v Op.group
  map_zero' := by simp
  map_add' v w := by simp only [Pi.add_apply]; omega
  monotone' v w h := by
    have h₁ : v Op.hash ≤ w Op.hash := h Op.hash
    have h₂ : v Op.group ≤ w Op.group := h Op.group
    dsimp only
    omega

/-- The per-kind budget pushes forward to the weighted budget `3 q + 5`. -/
example (q : ℕ) : (adv q).IsChargeBound (weigh ∘ kind) (3 * q + 5) := by
  have := (adv_isChargeBound q).map weigh
  simp only [map_zero, map_add, map_nsmul] at this
  convert this using 1
  simp [weigh, kind, mul_comm]

/-! ## Calls with no answer -/

/-- One call that can never be answered. -/
abbrev Dead : PFunctor := ⟨Unit, fun _ => PEmpty⟩

def stuck : FreeM Dead PEmpty := FreeM.lift ()

/-- The structural bound charges the call. -/
example : ¬ stuck.IsChargeBound (fun _ => (1 : ℕ)) 0 := by
  simp [stuck]

/-- The worst-case cost charges the call. -/
example : cost (fun _ => (1 : ℕ∞)) stuck = 1 := by
  simp [stuck]

/-- No completed path ends, so every completed path is within budget `0`. -/
example (p : Path stuck) : Path.charge (fun _ => (1 : ℕ)) stuck p ≤ 0 :=
  p.1.elim

/-! ## Handlers -/

/-- A single interface with two answers. -/
abbrev Coin : PFunctor := ⟨Unit, fun _ => Bool⟩

/-- Implement each call by two calls, returning the second answer. -/
def doubled : Handler (FreeM Coin) Coin := fun _ => do
  let _ ← FreeM.lift (P := Coin) ()
  FreeM.lift (P := Coin) ()

example : doubled.WithinCharge (fun _ => (1 : ℕ)) (fun _ => 2) := fun _ => by
  cost_bound [doubled]

/-- Doubling a natural-number budget. -/
def double : ℕ →+o ℕ where
  toFun n := 2 * n
  map_zero' := rfl
  map_add' a b := by omega
  monotone' a b h := by dsimp only; omega

example {α : Type} (x : FreeM Coin α) (n : ℕ) (hx : x.IsChargeBound (fun _ => 1) n) :
    (x.liftM doubled).IsChargeBound (fun _ => 1) (2 * n) := by
  have h2 : x.IsChargeBound (fun _ => 2) (2 * n) := hx.map double
  exact h2.liftM doubled fun _ => by cost_bound [doubled]

/-- The doubled handler costs two per call in value form. -/
example : handlerCost (fun _ => (1 : ℕ∞)) doubled = fun _ => 2 := by
  funext a
  cost_bound [handlerCost, doubled]

/-- A counting handler: each call increments a counter and makes two calls. -/
def counted : Handler (StateT ℕ (FreeM Coin)) Coin := fun a => do
  modify (· + 1)
  StateT.lift (doubled a)

example {α : Type} (x : FreeM Coin α) (n : ℕ) (hx : x.IsChargeBound (fun _ => 2) n) (k : ℕ) :
    ((x.liftM counted).run k).IsChargeBound (fun _ => 1) n :=
  hx.run_liftM counted (fun _ σ => by cost_bound [counted, doubled]) k

/-! ## Instrumented runs -/

def chgN : Coin.A → ℕ := fun _ => 2

/-- Always answer `true`. -/
def answer : Handler Id Coin := fun _ => true

def flips : FreeM Coin Bool := do
  let b ← FreeM.lift (P := Coin) ()
  if b then FreeM.lift (P := Coin) () else pure false

example : flips.IsChargeBound chgN 4 := by
  cost_bound [flips, chgN]

/-- The instrumented run spends `4`, within the budget. -/
example : ((flips.liftM (answer.withCharge chgN)).run 0).2 = 4 := rfl

example : ((flips.liftM (answer.withCharge chgN)).run 0).2 ≤ 4 :=
  (show flips.IsChargeBound chgN 4 by cost_bound [flips, chgN]).le_of_canReturn_run_liftM_withCharge
    answer rfl

/-- Within budget the gate is transparent; with budget `3` the second call is refused. -/
example : ((flips.liftM (answer.withBudget chgN 4)).run 0).run =
    some <$> (flips.liftM (answer.withCharge chgN)).run 0 :=
  Handler.run_liftM_withBudget_of_isChargeBound answer chgN (by cost_bound [flips, chgN])

example : ((flips.liftM (answer.withBudget chgN 3)).run 0).run = none := rfl

end PolyFunTest.ChargeHandlers
