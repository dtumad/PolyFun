/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Mathlib.Data.Sum.Basic
public import Mathlib.Logic.Relation

/-!
# Deterministic transitions with exact residual states

One transition either returns a result or supplies the next state. Each call to
the transition function consumes one unit of fuel, including the call reporting
termination. Exhausted fuel retains the exact state and is not an error or a
claim of divergence. Result types, including any language-specific errors, are
parameters of this interface.

`Transition.Follows next step halted` says that `next` is the function form of a
deterministic small-step relation `step` whose normal forms are the `halted` states,
the way CSLib states small-step semantics. Its executions are then exactly the
`step`-paths to a halted state (`Follows.executes_iff`).
-/

public section

namespace Control

/-- A total deterministic transition with a terminating result branch. -/
abbrev Transition (S R : Type*) := S → R ⊕ S

namespace Transition

variable {S R : Type*} (next : Transition S R)

/-- Execute a finite number of transitions, retaining any residual state. -/
@[expose] def run : Nat → S → R ⊕ S
  | 0, state => .inr state
  | n + 1, state => match next state with
      | .inl result => .inl result
      | .inr state' => run n state'

/-- Resume a residual; a returned result is already final. -/
@[expose] def continueRun (fuel : Nat) : R ⊕ S → R ⊕ S
  | .inl result => .inl result
  | .inr state => run next fuel state

/-- Splitting the fuel budget preserves results and exact residual states. -/
theorem run_add (n m : Nat) (state : S) :
    run next (n + m) state = continueRun next m (run next n state) := by
  induction n generalizing state with
  | zero => simp [run, continueRun]
  | succ n ih =>
      simp only [Nat.succ_add, run]
      cases next state with
      | inl result => rfl
      | inr state' => exact ih state'

/-- A finite derivation of terminating execution. -/
inductive Executes : S → R → Prop where
  | done {state result} (h : next state = .inl result) : Executes state result
  | next {state state' result} (h : next state = .inr state')
      (tail : Executes state' result) : Executes state result

/-- Some finite transition budget returns the specified result. -/
@[expose] def Terminates (state : S) (result : R) : Prop :=
  ∃ fuel, run next fuel state = .inl result

/-- Inductive execution and finite successful chunks describe the same behavior. -/
theorem executes_iff_terminates (state : S) (result : R) :
    Executes next state result ↔ Terminates next state result := by
  constructor
  · intro h
    induction h with
    | done hs => exact ⟨1, by simp [run, hs]⟩
    | next hs _ ih =>
        obtain ⟨n, hn⟩ := ih
        exact ⟨n + 1, by simp [run, hs, hn]⟩
  · rintro ⟨n, hn⟩
    induction n generalizing state with
    | zero => cases hn
    | succ n ih =>
        cases hs : next state with
        | inl out =>
            have : out = result := by simpa [run, hs] using hn
            exact .done (this ▸ hs)
        | inr state' => exact .next hs (ih state' (by simpa [run, hs] using hn))

/-- Deterministic execution has a unique terminating result. -/
theorem Executes.unique {state : S} {left right : R}
    (hl : Executes next state left) (hr : Executes next state right) : left = right := by
  induction hl with
  | done h =>
      cases hr with
      | done h' => exact Sum.inl.inj (h.symm.trans h')
      | next h' _ => cases h.symm.trans h'
  | next h _ ih =>
      cases hr with
      | done h' => cases h.symm.trans h'
      | next h' tail =>
          have heq := Sum.inr.inj (h.symm.trans h')
          subst heq
          exact ih tail

/-- Equal next transitions have the same terminating executions. -/
theorem Executes.of_step_eq {state state' : S} {result : R}
    (h : next state = next state') (hr : Executes next state' result) :
    Executes next state result := by
  cases hr with
  | done h' => exact .done (h.trans h')
  | next h' tail => exact .next (h.trans h') tail

/-- A preserved state interpretation computes the meaning of every returned result. -/
theorem Executes.meaning {D : Type*} (stateMeaning : S → D) (resultMeaning : R → D)
    (preserve : ∀ state, stateMeaning state =
      Sum.elim resultMeaning stateMeaning (next state))
    {state : S} {result : R} (h : Executes next state result) :
    stateMeaning state = resultMeaning result := by
  induction h with
  | @done state result hs => simpa [hs] using preserve state
  | @next state state' result hs _ ih =>
      have he : stateMeaning state = stateMeaning state' := by
        simpa [hs] using preserve state
      exact he.trans ih

/-! ## Small-step relations -/

/-- `next` is the function form of the deterministic relation `step`. A halted state returns
itself, and is a normal form of `step`; any other state continues to its unique successor. -/
structure Follows (next : Transition S S) (step : S → S → Prop) (halted : S → Prop) : Prop where
  /-- A halted state returns itself. -/
  halt : ∀ state, halted state → next state = .inl state
  /-- Any other state continues to a successor under `step`. -/
  advance : ∀ state, ¬ halted state → ∃ state', next state = .inr state' ∧ step state state'
  /-- Halted states have no successor. -/
  normal : ∀ state state', halted state → ¬ step state state'
  /-- Successors are unique. -/
  unique : ∀ {state left right}, step state left → step state right → left = right

namespace Follows

variable {next : Transition S S} {step : S → S → Prop} {halted : S → Prop}

/-- A returned state is the halted state itself. -/
theorem halted_of_eq_inl (h : Follows next step halted) {state result : S}
    (hs : next state = .inl result) : halted state ∧ result = state := by
  by_cases hh : halted state
  · exact ⟨hh, Sum.inl.inj (hs.symm.trans (h.halt state hh))⟩
  · obtain ⟨_, hs', _⟩ := h.advance state hh
    cases hs.symm.trans hs'

/-- A continuing transition is a `step`. -/
theorem step_of_eq_inr (h : Follows next step halted) {state state' : S}
    (hs : next state = .inr state') : step state state' := by
  by_cases hh : halted state
  · cases hs.symm.trans (h.halt state hh)
  · obtain ⟨_, hs', hstep⟩ := h.advance state hh
    exact Sum.inr.inj (hs'.symm.trans hs) ▸ hstep

/-- Executions are exactly the `step`-paths that end in a halted state. -/
theorem executes_iff (h : Follows next step halted) {state result : S} :
    Executes next state result ↔ Relation.ReflTransGen step state result ∧ halted result := by
  constructor
  · intro hex
    induction hex with
    | done hs =>
        obtain ⟨hh, rfl⟩ := h.halted_of_eq_inl hs
        exact ⟨.refl, hh⟩
    | next hs _ ih => exact ⟨.head (h.step_of_eq_inr hs) ih.1, ih.2⟩
  · rintro ⟨hpath, hh⟩
    induction hpath using Relation.ReflTransGen.head_induction_on with
    | refl => exact .done (h.halt _ hh)
    | head hstep _ ih =>
        have hnot : ¬ halted _ := fun hh' => h.normal _ _ hh' hstep
        obtain ⟨_, hs, hstep'⟩ := h.advance _ hnot
        exact .next hs (h.unique hstep' hstep ▸ ih)

/-- A `step`-path to a halted state is found by some finite transition budget. -/
theorem terminates_iff (h : Follows next step halted) {state result : S} :
    Terminates next state result ↔ Relation.ReflTransGen step state result ∧ halted result := by
  rw [← executes_iff_terminates, h.executes_iff]

end Follows

end Transition
end Control
