# Interaction cost

This guide covers how PolyFun accounts for the use of an interface: how many calls a program
makes, of which kinds, and at what price. It is about interaction with an interface, not about
the running time of a machine; [realizability](realizability.md) covers backend-relative time.

## Charges

A **charge** prices the calls of an interface `P` in a cost type `ω`: a call at position `a`
costs `c a`. A charge is a plain function `c : P.A → ω`, paid when the call is made, before the
answer arrives. Cost types are Mathlib's ordered additive monoids, so the same API covers:

- call counts in `ℕ`;
- per-kind counts in `K → ℕ` or `K →₀ ℕ`;
- weights in `ℕ∞` or `ℝ≥0∞`;
- records of counters such as `ExecutionCost`.

As a polynomial map, a charge is a lens into the constant polynomial `C ω`
(`PolyFun/PFunctor/Charge.lean`). Pulling a charge back along a lens is lens composition, and the
charge on a sum of interfaces is the copairing `Sum.elim c d`. Intrinsic costs such as ticks need
no new construction: a tick is a call to `PFunctor.linear ω` charged by `id`.

## Two readings on free programs

`PolyFun/PFunctor/Free/Cost.lean` defines two readings of a charge on `x : FreeM P α`.

| Reading | Definition | Cost types |
|---|---|---|
| Budget | `x.IsChargeBound c B s`: starting with `s` spent, every call keeps the amount spent at most `B` | any ordered additive monoid |
| Worst-case cost | `cost c x`, the fold of `OpSpec.charge c`; `costWith c x k` adds a leaf cost `k` | complete lattices such as `ℕ∞` |

The budget carries the amount spent so far, so a call at `a` asks `s + c a ≤ B`. No subtraction
or existential is involved, and natural-number and vector budgets reduce to linear arithmetic.

The two readings agree in canonically ordered monoids:

- `isChargeBound_of_cost_le` holds in general;
- `cost_le_of_isChargeBound` needs addition to distribute over nonempty suprema (`AddSupDistrib`,
  which holds for `ℕ∞` and pointwise);
- `isChargeBound_iff_cost_natCast_le` reads a natural-number budget as a bound in `ℕ∞`.

The budget is an instance of the general roll bound `IsRollBound`
(`isChargeBound_iff_isRollBound`). With natural-number charges it is the subtractive roll bound
that VCVio's `IsQueryBound` family uses (`isChargeBound_iff_isRollBound_nat`). Unit charges give
`IsTotalRollBound` (`isChargeBound_one_iff_isTotalRollBound`).

### Calls that cannot be answered

Both readings charge a call whose answer type is empty. A run that reaches such a call never
completes, but the call is still made.

Completed paths give a third reading, `Path.charge c x p` (`PolyFun/PFunctor/Free/Path/Charge.lean`):

- a budget bounds every completed path (`charge_le_of_isChargeBound`);
- the converse needs every reachable call to have an answer (`isChargeBound_of_forall_charge_le`,
  under `ProgramProgress`);
- a path's charge is the additive valuation of its event trace (`charge_eq_traceList_charge`).

## Laws

**Sequencing.** The exact form is `cost c (x >>= f) = costWith c x fun a => cost c (f a)` and
`isChargeBound_bind_iff`. The additive forms are `IsChargeBound.bind` and `cost_bind_le`.

**Monotonicity.** `IsChargeBound.mono`, `.mono_charge` and `.mono_spent`; `cost_mono_charge` is
tagged `@[gcongr]`.

**Changing the cost type.**

- Bounds push forward along monotone additive maps (`IsChargeBound.map`). A per-kind vector bound
  weighted by a linear form is a weighted bound.
- Bounds transfer both ways along additive order embeddings (`isChargeBound_comp_iff`).
- Pairs and families split componentwise (`isChargeBound_prod_iff`, `isChargeBound_pi_iff`).

**Loops** (`PolyFun/PFunctor/Free/Cost/Loops.lean`). `forM`, `mapM`, `foldlM` and `forIn` stay
within the sum of their per-iteration budgets, or `xs.length • B` for a uniform budget `B`.
`cost_forM_le` and `cost_forIn_le` are the value forms.

## Lenses and handlers

**Lenses.** A bound with the pulled-back charge bounds the relabelled program
(`IsChargeBound.mapLens`, `cost_mapLens_le`). The two are equal when the lens reaches every
answer.

**Free handlers.** `Handler.WithinCharge h d c` (`PolyFun/PFunctor/Handler/Charge.lean`) says that
each implementation `h a` stays within `c a` under the target charge `d`. Simulating a program
within budget through such a handler stays within the same budget (`IsChargeBound.liftM`).
Certificates hold for identity, lens and sum handlers, and they compose (`WithinCharge.comp`). In
value form, a simulated program costs at most the original with each call charged by
`handlerCost` (`cost_liftM_le`).

**Stateful handlers.** For handlers into `StateT σ (FreeM Q)`, a step bound that holds from every
state gives the same transfer (`IsChargeBound.run_liftM`).

**Handlers into any monad.**

- `h.withCharge c` keeps the amount spent as `StateT` state, and forgetting it recovers the
  handler.
- On every possible result of a run of a program within budget `B`, the amount spent is at most
  `B` (`IsChargeBound.le_of_canReturn_run_liftM_withCharge`).
- That is an instance of resource growth (`IsChargeBound.le_of_canReturn_run_liftM`): if each call
  at `a` raises a measure of the handler state by at most `c a`, a program within budget `B`
  raises it by at most `B`. Counters, logs, caches and tables are such measures.
- `h.withBudget c B` refuses any call that would overspend, and on a program within budget it
  never refuses (`run_liftM_withBudget_of_isChargeBound`).

## Other models

The other models of computation inherit the notion through their finite truncations, which are
free programs.

| Model | Bound | Agreement |
|---|---|---|
| `Resumption p β` | `IsChargeBound`: every `truncate k r` within budget (safety reading) | `isChargeBound_toResumption_iff`, `isChargeBound_query_iff` |
| `DynComputation p α β` | every `unroll k state` within budget | `isChargeBound_iff_behavior`, `isChargeBound_ofFreeM_iff`, `IsChargeBound.wrap` |
| `ITree F α` | visible calls charged by `c`, silent steps by `tau` (default `0`) | `isChargeBound_step_iff` (free silent steps are invisible), `isChargeBound_iff_toDynComputation` |
| `IFreeM P X s` | the bound of the Σ-erasure | `isChargeBound_iff_toSigmaFreeM` |
| `TypeTree` | a `FreeM` over move types; a unit charge counts rounds | definitional |

The safety reading allows runs that never return: such a run is within budget when all of its
finite prefixes are.

## Proving bounds

- **Concrete programs.** `cost_bound [defs]` (`PolyFun/PFunctor/Free/Cost/Tactic.lean`) unfolds
  the definitions and runs `simp` with the cost equations and with finite-supremum unfolding
  (`Fin.iSup_succ`, `iSup_bool_eq`, `iSup_option`, `iSup_sum`). Then `norm_num` and `omega` handle
  the arithmetic. It decides budgets and computes worst-case costs of `do` programs over finite
  answer types.
- **Loops with a symbolic number of iterations.** Use the loop lemmas.
- **Bounds stated as triples.** `triple_liftM_of_isChargeBound` (`PolyFun/PFunctor/Free/WP/Charge.lean`)
  indexes ranks by the amount spent, so `vcgen` decomposes a simulated program call by call.
  `PolyFunTest/Do/Charge.lean` bounds the state of a counting handler this way.

## Boundaries

Expected cost needs a measure on answers, and it belongs downstream. In VCVio it is a valuation
of `Path.charge` under the path measure. Costs that are not additive under sequencing, such as
the number of distinct queries, are monotone valuations of event traces (`TraceList`) rather than
charges.
