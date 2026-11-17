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
