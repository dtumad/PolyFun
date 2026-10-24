/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import PolyFun.ITree.Transition
public import Cslib.Computability.URM.Execution

/-!
# CSLib's register machines as deterministic transitions

CSLib states URM execution as a deterministic step relation, with halted states as its normal
forms. `urm p` is that relation as a `Control.Transition` returning the halted state, and
`Transition.Follows` identifies its executions with CSLib's paths. CSLib's halting judgements
then follow from finite transition budgets:
* an addition program computes `2 + 3` by `rfl`;
* a self-jump diverges, proved by showing every budget leaves it running.

The same transition runs as an interaction tree and as a machine through PolyFun's adapters.
-/

@[expose] public section

namespace PolyFunTest.CslibURM

open Cslib URM Control

/-- One URM step as a transition: a halted state returns itself. -/
def urm (p : Program) : Transition State State := fun s =>
  match p[s.pc]? with
  | none => .inl s
  | some (.Z n) => .inr ⟨s.pc + 1, s.regs.write n 0⟩
  | some (.S n) => .inr ⟨s.pc + 1, s.regs.write n (s.regs.read n + 1)⟩
  | some (.T m n) => .inr ⟨s.pc + 1, s.regs.write n (s.regs.read m)⟩
  | some (.J m n q) =>
      .inr (if s.regs.read m = s.regs.read n then ⟨q, s.regs⟩ else ⟨s.pc + 1, s.regs⟩)

/-- The transition is CSLib's step relation, halting exactly at CSLib's halted states. -/
theorem follows (p : Program) : Transition.Follows (urm p) (Step p) (·.isHalted p) where
  halt s hs := by
    simp only [urm, List.getElem?_eq_none (show p.length ≤ s.pc from hs)]
  advance s hs := by
    obtain ⟨i, hi⟩ := Option.ne_none_iff_exists'.mp
      (mt List.getElem?_eq_none_iff.mp (show ¬p.length ≤ s.pc from hs))
    cases i with
    | Z n => exact ⟨_, by simp [urm, hi], .zero hi⟩
    | S n => exact ⟨_, by simp [urm, hi], .succ hi⟩
    | T m n => exact ⟨_, by simp [urm, hi], .transfer hi⟩
    | J m n q =>
        by_cases heq : s.regs.read m = s.regs.read n
        · exact ⟨_, by simp [urm, hi, heq], .jump_eq hi heq⟩
        · exact ⟨_, by simp [urm, hi, heq], .jump_ne hi heq⟩
  normal _ _ hs := Step.no_step_of_halted hs
  unique hl hr := Step.deterministic hl hr

/-- CSLib's halting with a result is termination of the transition at a state with that
output. -/
theorem haltsWithResult_iff (p : Program) (inputs : List ℕ) (result : ℕ) :
    p ↓ inputs ≫ result ↔
      ∃ final, Transition.Terminates (urm p) (State.init inputs) final ∧
        final.regs.output = result := by
  simp only [HaltsWithResult, (follows p).terminates_iff, and_assoc]

/-- CSLib's halting is termination of the transition. -/
theorem halts_iff (p : Program) (inputs : List ℕ) :
    p ↓ inputs ↔ ∃ final, Transition.Terminates (urm p) (State.init inputs) final := by
  simp only [Halts, (follows p).terminates_iff]

/-- Determinism of the transition recovers CSLib's uniqueness of halted states. -/
example (p : Program) {init s₁ s₂ : State}
    (h₁ : Steps p init s₁) (hh₁ : s₁.isHalted p) (h₂ : Steps p init s₂) (hh₂ : s₂.isHalted p) :
    s₁ = s₂ :=
  Transition.Executes.unique (urm p) ((follows p).executes_iff.2 ⟨h₁, hh₁⟩)
    ((follows p).executes_iff.2 ⟨h₂, hh₂⟩)

/-! ## Running programs -/

/-- Add register 1 into register 0, counting in register 2. -/
def add : Program := [.J 1 2 4, .S 0, .S 2, .J 0 0 0]

/-- Twenty transitions add the inputs. -/
example : (Transition.run (urm add) 20 (State.init [2, 3])).elim (·.regs.output) (fun _ => 0) =
    5 := rfl

/-- The computed run is CSLib's halting judgement. -/
example : add ↓ [2, 3] ≫ 5 := (haltsWithResult_iff add [2, 3] 5).2 ⟨_, ⟨20, rfl⟩, rfl⟩

/-- A self-jump never leaves its first instruction. -/
def spin : Program := [.J 0 0 0]

/-- Every budget leaves the self-jump running at its first instruction. -/
theorem run_spin (fuel : ℕ) (regs : Regs) :
    Transition.run (urm spin) fuel ⟨0, regs⟩ = .inr ⟨0, regs⟩ := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simpa [Transition.run, urm, spin] using ih

/-- The self-jump diverges on every input, in CSLib's sense. -/
theorem spin_diverges (inputs : List ℕ) : spin ↑ inputs := by
  rintro hh
  obtain ⟨_, fuel, h⟩ := (halts_iff spin inputs).1 hh
  rw [State.init, run_spin] at h
  cases h

/-! ## Adapters -/

/-- The machine's chunk runner agrees with the transition budget. -/
example (fuel : ℕ) (inputs : List ℕ) :
    (Transition.toMachine (urm add)).runChunk Transition.tickHandler fuel
      (.inr (State.init inputs)) =
        Transition.toChunk (Transition.run (urm add) fuel (State.init inputs)) :=
  Transition.runChunk_toMachine _ _ _

end PolyFunTest.CslibURM
