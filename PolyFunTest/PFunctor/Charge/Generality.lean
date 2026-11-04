/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Free.Cost.Tactic
public import PolyFun.PFunctor.Free.Cost.Support
public import PolyFun.PFunctor.Free.Path.Charge
public import PolyFun.PFunctor.Handler.Charge

/-!
# Generality checks for the cost API

Shapes taken from downstream special cases:

* signed weights, for which a prefix overspends a budget every completed path respects, so the
  completed-path reading is not derived from the structural bound;
* completed-path transfer through a free handler, keeping the output;
* deterministic runs and subsingleton answers, where the worst case is the actual cost;
* relabelling with a change of cost monoid;
* sequencing on reachable results only, and charges and handlers that matter only on the calls
  a program makes.
-/

public section

open PFunctor PFunctor.FreeM

namespace PolyFunTest.ChargeGenerality

/-! ## Signed weights -/

/-- Two operations with a single answer each. -/
abbrev Two : PFunctor := ⟨Bool, fun _ => PUnit⟩

/-- `true` costs `1` and `false` refunds `1`. -/
def signed (b : Two.A) : ℤ := if b then 1 else -1

/-- Spend one, then refund it. -/
def upDown : FreeM Two PUnit := do
  let _ ← FreeM.lift (P := Two) true
  FreeM.lift (P := Two) false

/-- Every completed path nets to zero. -/
example : ∀ p : Path upDown, Path.charge signed upDown p ≤ 0 := by
  rw [Path.forall_charge_le_iff_ofHandler (fun _ => PUnit.unit)]
  decide

/-- The first call already overspends a zero budget. -/
example : ¬ upDown.IsChargeBound signed 0 := by
  simp [upDown, signed]

/-! ## Completed-path transfer -/

abbrev Coin : PFunctor := ⟨Unit, fun _ => Bool⟩

/-- Implement each call by two calls. -/
def doubled : (a : Coin.A) → FreeM Coin (Coin.B a) := fun _ => do
  let _ ← FreeM.lift (P := Coin) ()
  FreeM.lift (P := Coin) ()

theorem doubled_path (a : Coin.A) (r : Path (doubled a)) :
    Path.charge (fun _ => (1 : ℤ)) (doubled a) r ≤ 2 := by
  rcases r with ⟨b, b', ⟨⟩⟩
  change (1 : ℤ) + (1 + 0) ≤ 2
  decide

example {α : Type} (x : FreeM Coin α) (n : ℤ)
    (hx : ∀ p : Path x, Path.charge (fun _ => (2 : ℤ)) x p ≤ n) (q : Path (x.liftM doubled)) :
    Path.charge (fun _ => (1 : ℤ)) (x.liftM doubled) q ≤ n :=
  Path.charge_liftM_le_of_forall doubled doubled_path hx q

/-! ## Deterministic runs -/

def answerTrue : Handler Id Coin := fun _ => true

def flips : FreeM Coin Bool := do
  let b ← FreeM.lift (P := Coin) ()
  if b then FreeM.lift (P := Coin) () else pure false

/-- The instrumented deterministic run is the output and charge of the path it picks. -/
example : ((flips.liftM (answerTrue.withCharge fun _ => (3 : ℕ))).run 0).run =
    (output flips (Path.ofHandler (fun _ => true) flips),
      Path.charge (fun _ => (3 : ℕ)) flips (Path.ofHandler (fun _ => true) flips)) := by
  rw [Handler.run_liftM_withCharge_id, zero_add]
  rfl

/-! ## Relabelling with a change of cost monoid -/

/-- Relabel into the left summand of a sum interface, charging the right summand nothing. -/
example {α : Type} (x : FreeM Coin α) (q : Path (x.mapLens (Lens.inl (Q := Two)))) :
    Path.charge (Sum.elim (fun _ => (1 : ℤ)) fun _ => 0) (x.mapLens Lens.inl) q =
      Path.charge (fun _ => (1 : ℤ)) x (Path.pullMapLens Lens.inl x q) :=
  Path.charge_mapLens_eq_map (AddMonoidHom.id ℤ) Lens.inl (fun _ => rfl) x q

/-! ## Reachable results and provenance -/

/-- A continuation that is expensive only on a result `pure 0` never returns. -/
def pricey (n : ℕ) : FreeM Coin Bool :=
  if n = 0 then FreeM.lift (P := Coin) () else do
    let _ ← FreeM.lift (P := Coin) ()
    let _ ← FreeM.lift (P := Coin) ()
    FreeM.lift (P := Coin) ()

example : (FreeM.bind (pure 0 : FreeM Coin ℕ) pricey).IsChargeBound (fun _ => (1 : ℕ)) 1 := by
  have := (isChargeBound_pure (c := fun _ : Coin.A => (1 : ℕ)) (B := 0) (0 : ℕ)).bind_supp
    (f := pricey) (B₂ := 1) fun a ha => by
      obtain rfl : a = 0 := ha
      cost_bound [pricey]
  simpa using this

/-- A program that only calls `true` sees only the charge and handler at `true`. -/
example (x : FreeM Two PUnit) (hS : x.CallsIn {true}) (B s : ℕ) :
    x.IsChargeBound (fun b => if b then 1 else 7) B s ↔ x.IsChargeBound (fun _ => 1) B s :=
  IsChargeBound.congr_charge hS fun a ha => by simp_all

end PolyFunTest.ChargeGenerality
