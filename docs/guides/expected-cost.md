# Stateful expected cost

A retry service can answer its first call by tossing a fair coin and then cache that answer. A
client that repeats until success has a one-half chance of retrying forever. Tossing a fresh coin
on every call instead costs two calls on average. The client and the first answer distribution
are identical in these examples. The difference is the joint law of the answer and the state
available to the next call.

## Charge one call, then interpret a client

Give a request `a` in state `s` a nonnegative extended-real charge `c a s` and a kernel `K a s`
on answers and successor states. A continuation `k` makes the request worth

```text
c(a, s) + ∫ k(answer, nextState) dK(a, s).
```

An empty answer law gives zero continuation value. The call has still incurred its charge.
A postexpectation at a leaf can inspect the returned value and the final state together.

For a well-founded client, `FreeM.wpFold_expectedCharge_run` identifies this fold with the
target cost of running its stateful handler. Supply the joint kernel and the inferred expected
cost of each implementation as measurable functions of incoming state. The source of the kernel
and charge is the same target program, so a request may make several target calls and may
correlate its answer with its private state. The pointwise inequality accepts a per-state
allowance. `wpFold_expectedCharge_run_link` threads both private states through a linked pair
of handlers. The kernel and transfer equations use countable answer spaces with measurable
singletons where they form a measurable continuation from its answer-indexed family. The target operation answers for handler transfer carry the
discrete measurable structure. State itself can have a general measurable space. [Finite transfer](../../PolyFun/PFunctor/Free/Measure/StatefulExpectedCharge.lean)

A potential `V` lets several calls share an allowance. With actual charge `d` and budget `c`,
prove the following inequality in each state satisfying the invariant.

```text
d(a, s) + ∫ V(nextState) dK(a, s) ≤ c(a, s) + V(s).
```

The kernel must preserve the invariant almost surely. At any valid starting state the client's
actual expected cost, including the potential still present on return, is bounded by its budgeted
cost plus its initial potential. A one-time setup charge is a simple example. Finite nonnegative
linear combinations of resource prices commute with the stateful fold, including its terminal
postcost. This computes the expected price of a resource vector. Recovering its joint distribution
requires a richer observation. [Finite pricing](../../PolyFun/PFunctor/Free/Measure/StatefulExpectedChargePrice.lean)

## Unbounded executions and terminal observations

Truncate a resumption after at most `n` visible calls, charge each reached call, and assign zero
terminal credit at the cutoff. `Resumption.expectedCharge` takes the supremum over these
observations. With measurable prices and postcosts the continuous algebra on measurable
state-indexed expectations gives the query and bind equations. The same definition recovers the
well-founded fold even when terminating paths have no common depth bound. The potential inequality
passes to the limit because nonnegative potential at an unfinished prefix can be discarded.
[Resumption cost](../../PolyFun/PFunctor/Resumption/Measure/ExpectedCharge.lean)

For a measurable observation `f` of result and final state, the value is

```text
expected incurred charge + ∫ f(result, finalState) d(returnedKernel).
```

The terminal kernel sums the joint laws of returns at each exact query depth. Subprobability
operations give a subprobability terminal kernel. The decomposition continues to hold when the
charge is infinite. At finite charge, probing with zero and with measurable event indicators
recovers both the charge and the terminal law. At infinite charge, every scalar probe reads
infinity. `expectedCharge_ext_iff` characterizes both cases, and the kernel remains independently
available even then. Its pure, query and bind equations compose these joint laws. Bind requires
joint measurability of the continuation kernel in the intermediate result and state. Two programs can even return opposite Booleans almost surely and pay a finite price
at every step. A doubling price on fresh fair-coin retries gives both infinite expected cost,
and every scalar observation agrees. [Terminal kernel and decomposition](../../PolyFun/PFunctor/Resumption/Measure.lean)

An interaction tree makes silent steps explicit. `ITree.expectedCharge_interp_run_unbounded`
equates the cost of the executed client with its cost under the induced one-call kernel and price.
Both the client and the handler implementation may diverge. The kernel retains the handler's
private state and the target service's state. Supply measurability of the derived law and price
in these states. A handler that pays four and then silently diverges has cost four and returns
zero mass, even when a successful return would earn infinite credit.

The interpreter transfer uses free silent guards. The observation itself permits any nonnegative
silent-step price. At zero price weakly bisimilar trees have the same cost. An infinite sequence
of positive-price silent steps costs infinity. The terminal-law decomposition applies
at either price. [Interaction-tree interpretation](../../PolyFun/ITree/Measure.lean)

## Conditional retry bounds

For a Markov trial, suppose every state in a retry invariant has success probability at least
`p > 0` and per-trial expected charge at most `C`. Each retry must return to the invariant
almost surely. The chance of still retrying after `n` calls is at most `(1 − p)^n`, the first
`n` trials cost at most `C · ∑_{i < n} (1 − p)^i`, and the full expected cost is at most `C / p`.
Success has total mass one. The local condition allows dependence between rounds. A service that
caches its first failure violates the condition in the reached failure state.

The bound on cost also follows directly from a bound on the retry mass of a subprobabilistic
trial. Missing mass can represent abort, so the same argument alone gives no lower bound on the
mass of successful returns. Counting a cutoff as a successful return would obscure this
distinction. Even a fresh fair coin with success mass one has infinite expected total charge
if attempt `i` costs `2^i`: it is reached with probability `2^(-i)` and contributes one in
expectation. [Compiled examples](../../Examples/Tutorials/ExpectedRetry.lean). [Retry equations and bounds](../../PolyFun/PFunctor/Resumption/Measure/Retry.lean)

## Collecting several results

Use `Collect.collect act accept k initial` when the next request depends on earlier successes.
At a stage with `i + 1` successes still needed, `act i x` chooses the request.
`accept i x answer` either asks for another attempt or yields the accumulator for stage `i`.
A list accumulator can record the payloads in discovery order. The service kernel threads its
own state through every attempt, including rejected ones.

To prove a bound, give an invariant `I j x s` relating the outstanding successes, accumulator
and service state. Show that rejection preserves this stage and acceptance enters the next one.
With a positive floor `pᵢ` on the acceptance mass throughout each reached stage, unit-mass
trials give a final result of mass one. A per-attempt charge of at most `Cᵢ` gives the cost
bound `∑ i < k, Cᵢ / pᵢ` with zero terminal credit. The upper bound also holds for
subprobability trials. Supply the acceptance estimate directly to
`expectedCharge_collect_le_of_accept`, or use an upper bound on the rejection mass.
For exact costs on unit-mass trials, `expectedCharge_collect_eq_of_accept` takes the measured
acceptance mass and price at each stage.

A potential can depend on the stage and payload as well as on service state. Compare the actual
charge plus expected outgoing potential with the stage allowance plus incoming potential. On
rejection use the current stage's potential, and on success use the next stage's. For example,
a service that spends five units to initialize and one unit per fair trial needs at most
`2k + 5` from cold start. Both outcomes leave it warm. [Collector rules](../../PolyFun/PFunctor/Resumption/Measure/Collect.lean)
and [setup proof](../../PolyFunTest/Probability/CollectPotential.lean).

For `N` uniform coupon types, keep a list of distinct discoveries. If `j` types are missing,
exactly `j` of the `N` possible answers advance the stage. The exact stage-cost rule with
success probability `j / N` gives `N · ∑_{j=1}^N 1/j` expected draws. The final list is almost
surely a permutation of the population. For `N = 0` it returns the empty list immediately.
With two types, a service that samples once and replays its first coupon forever has zero
completion mass and infinite expected draw count. [Compiled coupon collector](../../Examples/Tutorials/CouponCollector.lean)

There are two useful bounds on attempts. `Collect.collectWithin` resets the attempt budget at
each success and returns `none` when any stage exhausts its fuel. Give exhaustion zero terminal
credit. The costs then increase with the per-stage fuel, and their supremum is the unbounded
cost, including on nonterminating paths. This limit holds for arbitrary kernels and measurable
nonnegative prices and postcosts. [Fuel-limit theorem](../../PolyFun/PFunctor/Resumption/Measure/CollectLimit.lean)

A single global budget uses `truncate n` on the unbounded program. Assume each reached trial has total mass at most one and a
success probability of at least `p` in its incoming state. The unfinished mass still present
at the cutoff is at most the probability of fewer than `k` successes in `n` independent
Bernoulli trials of bias `p`. Aborted runs have zero mass in the cutoff event. The bound allows
dependence between the service's attempts. Constant conditional success
probability and unit mass give equality. [Global cutoff and binomial bound](../../PolyFun/PFunctor/Resumption/Measure/CollectCutoff.lean)

## Normalizing a finite client

A finite `do` program can use the existing upper-bound interpretation and `vcgen`.
After exposing the fold, use `simp only [expected_cost]` for a symbolic calculation or
`norm_num [expected_cost, ...]` with the concrete program and kernel definitions. The named
simp set expands a weighted mixture into its weighted continuation values. A fair coin that
triggers a second unit-priced call only on heads costs `1 + 1/2`. The direct client proof is

```lean
example : wpFold charge flipAgain (fun _ _ => 0) () = 1 + 2⁻¹ := by
  simp only [flipAgain, charge, fair, expected_cost]
  norm_num [expected_cost]
```

An unspecified kernel leaves a joint integral in the goal. For an explicitly linked handler, rewrite the outer `run_link`
equation and then use `handler_nf` on the resulting runs. [Finite-kernel rules](../../PolyFun/PFunctor/Free/Measure/FiniteKernel.lean)
and [worked client proofs](../../PolyFunTest/Do/ExpectedCost.lean).

An interaction-tree client can use `returnedKernel_interp_run` to transport its full joint
return law across a stateful implementation, including at infinite incurred charge. The
`pure`, silent-step and divergence equations simplify terminal kernels directly. For an upper
bound on a potentially divergent implementation, give `expectedCharge_interp_run_unbounded_le`
a measurable allowance, its one-call bound and a measurable joint return law.
[Interaction-tree equations](../../PolyFun/ITree/Measure.lean)

## Connections to other cost models

Azevedo de Amorim separates the joint cost/result distribution of successful runs from the expected
cost incurred during execution. The lossless fragment is a point of agreement. PolyFun's terminal
decomposition offers a second way to test which observations survive that separation, including the
infinite-cost case. The affine map in §5.3 sends a cost/law pair to the function
`f ↦ cost + ∫ f dlaw`. For ordinary extended nonnegative reals, its finite-cost restriction
is injective. Two distinct laws at infinite cost have the same image. The componentwise
order-reflection conclusion of Corollary 5.10 therefore cannot be applied to this concrete
scalar map on the entire product. [Checked counterexample](../../PolyFunTest/Probability/ReturnedKernel.lean)

Kaminski, Katoen, Matheja and Olmedo give an expected-runtime transformer and
loop rules for a language with a specified step cost. Here the local obligation is expressed on an
operation implementation and the result concerns the client's chosen request prices.
[Expected-cost references](../../REFERENCES.md#expected-cost-citations)

In the Tachis coupon collector, the implementation keeps an array of seen coupons and a
counter. Its proof frames credits for later stages while paying for the current draw. In the
PolyFun example the client supplies the distinct-list invariant and the count of unseen answers.
The collector theorem handles the geometric waiting time and composition across stages.
Both calculations price a random draw. An implementation that also prices scans of the list
would have a different local charge. [Tachis, §5.1](https://arxiv.org/html/2405.20083v3#S5.SS1)

Tachis and ExpIris distribute credit across sampled branches and support ownership assertions
for imperative programs. The inequality above captures the expected-potential calculation on an
explicit state space. Its proof uses induction on finite prefixes and monotonicity. Applying a
signed potential or obtaining a stopped equality would require further hypotheses of the kind
analyzed by Wang, Hoffmann and Reps. For effect handlers, the interaction-tree semantics supplies
the operational object of the transfer theorem. A concrete language still needs to justify its
handler and its price, as the adequacy arguments in *Program Logics à la Carte* illustrate.
[Expected-cost references](../../REFERENCES.md#expected-cost-citations)

CatCrypt-core's `CostComp` records a natural cost beside a returned value, and `ecost` averages
that cost over returned results and heaps. Its exact bind equation assumes lossless continuations.
For a lossless round, project its returned outcome to the success bit and final heap and price the
round by its expected recorded cost. Then CatCrypt's `ecost (retryN body n)` satisfies the same
recurrence as PolyFun's `Retry.observe` with zero success and cutoff costs. On exhaustion CatCrypt
returns an ordinary `none` with zero additional charge. Taking the supremum therefore gives the
PolyFun resumption cost. With arbitrary lossy rounds, the finite CatCrypt cost is bounded above
by the same PolyFun observation priced by the one-round CatCrypt cost. On an aborting round,
a charge collected only upon return can vanish.
[CatCrypt's cost and retry definitions](https://github.com/spitters/CatCrypt-core/blob/76c5ee820139587d12dc7b5d9e19f65e0a310c74/CatCryptCore/Unary/ExpectedCost.lean)

CatCrypt's `collectN body fuel k` resets the fuel at each stage and fails the whole computation
on an exhausted stage. Giving exhausted outputs zero terminal value gives the same observations
of ordered lists and final heaps. For countable payload types this also identifies the concrete
measures after removing exhausted outputs. For the same fair unit-priced trial, one allowed attempt to
collect one payload costs one unit on reaching the request. CatCrypt's terminal writer records
one unit only on the half of runs that succeed, giving expected cost one half. Lossless rounds
with zero probability of exhausting the stage's fuel from every starting heap yield equality
of the two costs.
[CatCrypt collector definition](https://github.com/spitters/CatCrypt-core/blob/76c5ee820139587d12dc7b5d9e19f65e0a310c74/CatCryptCore/Container/ExpectedDNOp.lean)
