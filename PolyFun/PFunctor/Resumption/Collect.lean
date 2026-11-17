/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Resumption.Truncate

/-!
# Adaptive collectors

Each successful stage chooses the next stage's input. Unbounded stages retry the same request
until it succeeds. A bounded stage returns `none` if it runs out of attempts.
-/

public section

namespace PFunctor.Resumption.Collect

variable {P : PFunctor} {X : Type*}

private def retryStep (a : P.A) (accept : P.B a → Option X) :
    Option X → X ⊕ P.Obj (Option X)
  | none => .inr ⟨a, accept⟩
  | some x => .inl x

/-- Repeat a request until its answer yields a payload. -/
def retry (a : P.A) (accept : P.B a → Option X) : Resumption P X :=
  corec (retryStep a accept) none

private theorem retry_some (a : P.A) (accept : P.B a → Option X) (x : X) :
    corec (retryStep a accept) (some x) = pure x := by
  apply eq_of_dest_eq
  simp [retryStep]

theorem retry_eq_query (a : P.A) (accept : P.B a → Option X) :
    retry a accept = query a (fun b => (accept b).elim (retry a accept) pure) := by
  apply eq_of_dest_eq
  simp only [retry, dest_corec, retryStep, Sum.map_inr, dest_query, Sum.inr.injEq]
  change Obj.mk (P := P) a (fun b => corec (retryStep a accept) (accept b)) = Obj.mk a _
  congr 1
  funext b
  cases h : accept b <;> simp [retry_some]

/-- The guarded retry equation determines its implementation uniquely. -/
theorem retry_unique (a : P.A) (accept : P.B a → Option X) (t : Resumption P X)
    (ht : t = query a (fun b => (accept b).elim t pure)) : retry a accept = t := by
  let f (o : Option X) : Resumption P X := o.elim t pure
  have h := corec_unique (retryStep a accept) f (by
    intro o
    cases o with
    | none =>
      change dest t = _
      conv_lhs => rw [ht, dest_query]
      rfl
    | some x => simp [f, retryStep])
  exact (congrFun h none).symm

/-- Run the remaining stages in descending order, passing each accepted payload to the next. -/
@[expose] def collect (act : ℕ → X → P.A)
    (accept : (i : ℕ) → (x : X) → P.B (act i x) → Option X) : ℕ → X → Resumption P X
  | 0, x => pure x
  | i + 1, x => bind (retry (act i x) (accept i x)) (collect act accept i)

@[simp] theorem collect_zero (act : ℕ → X → P.A)
    (accept : (i : ℕ) → (x : X) → P.B (act i x) → Option X) (x : X) :
    collect act accept 0 x = pure x := rfl

theorem collect_succ (act : ℕ → X → P.A)
    (accept : (i : ℕ) → (x : X) → P.B (act i x) → Option X) (i : ℕ) (x : X) :
    collect act accept (i + 1) x = bind (retry (act i x) (accept i x)) (collect act accept i) := rfl

/-- Try a request until its answer advances the state or its per-stage fuel is exhausted. -/
@[expose] def retryWithin (a : P.A) (accept : P.B a → Option X) : ℕ → FreeM P (Option X)
  | 0 => Pure.pure none
  | n + 1 => FreeM.liftBind a fun b =>
    match accept b with
    | none => retryWithin a accept n
    | some y => Pure.pure (some y)

@[simp] theorem retryWithin_zero (a : P.A) (accept : P.B a → Option X) :
    retryWithin a accept 0 = Pure.pure none := rfl

theorem retryWithin_succ (a : P.A) (accept : P.B a → Option X) (n : ℕ) :
    retryWithin a accept (n + 1) =
      FreeM.liftBind a (fun b =>
        (accept b).elim (retryWithin a accept n) (fun y => Pure.pure (some y))) := by
  simp only [retryWithin]
  congr 1
  funext b
  cases accept b <;> rfl

/-- A stage with finite fuel is exactly the corresponding prefix of its unbounded retry. -/
theorem retryWithin_eq_truncate (a : P.A) (accept : P.B a → Option X) (n : ℕ) :
    retryWithin a accept n = truncate n (retry a accept) := by
  induction n with
  | zero =>
    rw [retryWithin_zero, retry_eq_query, truncate_query_zero]
    rfl
  | succ n ih =>
    rw [retryWithin_succ, retry_eq_query, truncate_query_succ]
    congr 1
    funext b
    cases e : accept b <;> simp [ih]

/-- Run successive stages with fresh fuel. The request and acceptance decision can depend on
the current stage and on all payloads already stored in the accumulator. -/
@[expose] def collectWithin (act : ℕ → X → P.A) (accept : (i : ℕ) → (x : X) →
    P.B (act i x) → Option X) (fuel : ℕ) : ℕ → X → FreeM P (Option X)
  | 0, x => Pure.pure (some x)
  | k + 1, x => FreeM.bind (retryWithin (act k x) (accept k x) fuel) fun r =>
    r.elim (Pure.pure none) (collectWithin act accept fuel k)

@[simp] theorem collectWithin_zero (act : ℕ → X → P.A) (accept : (i : ℕ) → (x : X) →
    P.B (act i x) → Option X) (fuel : ℕ) (x : X) :
    collectWithin act accept fuel 0 x = Pure.pure (some x) := rfl

theorem collectWithin_succ (act : ℕ → X → P.A) (accept : (i : ℕ) → (x : X) →
    P.B (act i x) → Option X) (fuel k : ℕ) (x : X) :
    collectWithin act accept fuel (k + 1) x =
      FreeM.bind (retryWithin (act k x) (accept k x) fuel)
        (fun r => r.elim (Pure.pure none) (collectWithin act accept fuel k)) := rfl

end PFunctor.Resumption.Collect
