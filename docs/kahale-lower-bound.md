# Kahale lower bound

This work concerns minimum binary-comparator sorting-network depth `D(n)`.
All logarithms in the coefficient are base two. The target is the published
Kahale–Leighton–Ma–Plaxton–Suel–Szemerédi lower bound

\[
\liminf_{n\to\infty}\frac{D(n)}{\log_2 n}
\ge c=\frac1{1-\log_2\varphi},\qquad
\varphi=\frac{1+\sqrt5}{2}.
\]

The numerical value is approximately `3.270559454`. This is the user's formula
with `a = (3 + sqrt(5))/2`, since `a - 1 = phi`.

Source: *Improved Lower Bounds for Sorting Networks*, STOC 1995, §5,
especially Lemmas 5.1–5.3 and Theorem 6. The supplied scan is
[`225058.225178.pdf`](225058.225178.pdf); an
[author-hosted copy](https://research.engineering.nyu.edu/~suel/papers/size.pdf)
has clearer equations. The formalization reconstructs the combinatorial
arguments locally. No published theorem is introduced as an axiom.

## Endpoints

The entry point is [`AKS/Kahale.lean`](../AKS/Kahale.lean). The finite bounds
are in [`Bounds/Kahale.lean`](../AKS/Bounds/Kahale.lean), and the limiting
statements are in
[`Bounds/KahaleAsymptotic.lean`](../AKS/Bounds/KahaleAsymptotic.lean).

For every `n`, with `d = D(n)`, the finite result is

\[
nF_{d+1}\le 2^{d+1}(d+1)^2.
\]

It implies the logarithmic inequality, for `n > 0`,

\[
\log_2 n\le(1-\log_2\varphi)d
 +2\log_2(d+1)+1+\log_2\varphi.
\]

The asymptotic endpoints are

```lean
SortingDepth.liminf_minimum_div_logb_ge_kahale
SortingDepth.eventually_minimum_depth_ge_kahale_logb
```

The second says that for every positive real `epsilon`, eventually
`D(n) >= (c - epsilon) * log_2 n`. It does **not** assert the exact
coefficient `c` as a finite inequality for every `n`.

## Proof map

| Module under `AKS/Kahale/` | Checked obligation |
| --- | --- |
| `RankInterval` | Attainable ranks on one wire form an interval, using adjacent rank swaps and monotonicity. |
| `ApproxSelection` | A small attainable-rank cover implies small rank displacement and approximate selection. |
| `Certificates` | Each wire has a zero certificate of size at most `2^height`; min takes the smaller height, max takes the larger height plus one. |
| `BinomialPotential` | A decreasing convex deficit potential propagates across min/max updates. |
| `LayerPotential` | One parallel stage changes the potential by a factor of at most two. |
| `SelectionCounting` | Approximate selection forces sufficiently large certificate heights outside the first `2^(s+1)` wires; derives the binomial inequality. |
| `Fanout` | A suffix of `s` stages gives a rank cover of size at most `2^s`. |
| `RankInputs` | Bridges actual sorting, rank permutations, and Boolean approximate selection. |
| `LayeredBound` | Combines a prefix of length `d-s` and suffix of length `s`. |
| `FibonacciBound` | Sums binomial inequalities and compares Fibonacci numbers to powers of the golden ratio. |
| `TimedExecution`, `GreedyLayers` | Greedy depth scheduling preserves comparator execution and gives exactly `net.depth` parallel stages. |
| `NetworkBound` | Removes all separate layering hypotheses from the finite sorting-network bound. |
| `LogRemainder` | The logarithmic error divided by depth tends to zero. |

### Fibonacci reconstruction

The paper uses weighted binomial sums and an asymptotic optimization. Our
reconstruction needs only one term from each prefix/suffix inequality:

\[
n\binom{d-s}{s}\le2^{d+1}(s+1),\qquad 0\le s\le d.
\]

Summing and using
`sum_s choose(d-s,s) = fib(d+1)` gives the finite Fibonacci bound above.
The resulting polynomial factor affects only a logarithmic error. Thus this
reconstruction gives the same published leading coefficient without importing
the paper's omitted optimization.

All comparator execution and depth arguments are proved in Lean. Definitions
of certificates, potentials, and scheduling are computable. The real analytic
constant and the existing mathematical minimum use classical definitions.

Verification: `lake build AKS.Kahale` succeeds, including guarded dependency
checks in `AKS/Kahale/Axioms.lean`. The audited endpoints depend only on
`propext`, `Classical.choice`, and `Quot.sound`. The focused source gate also
passes. No new proof axioms, incomplete proofs, or external decision procedures
are used. This verification covers the lower-bound target and its dependencies;
it does not claim a build of the concurrent Chvátal work.

## Improving the lower bound

[The method-barrier analysis](kahale-method-barrier.md) now exhibits populations
compatible with all current binomial constraints at the existing exponential
rate. Integral histogram rounding preserves the necessary prefix counts.
This narrows the next target to positional or certificate compatibility.
The [positional follow-up](kahale-positional-barrier.md) supplies an explicit
schedule satisfying the zero-height boundary requirements too. It can still
fail sorting, so actual certificate families and multiple threshold requirements
are the next target.

The Fibonacci step already extracts the full `3.270559454...` coefficient from
these particular binomial constraints. Reducing the polynomial factor improves
the finite error, but does not improve the leading coefficient.

A stronger leading bound needs a stronger combinatorial constraint. Concrete
places to investigate are:

1. Replace the suffix fanout estimate `2^s` with a bound that also accounts for
   sorting's simultaneous requirements on many wires.
2. Track zero and one certificates together, rather than counting only zero
   certificates near one boundary.
3. Retain distributions of certificate sizes or overlaps that the scalar height
   update discards, and seek a stronger potential inequality.

These are research directions, not proved improvements. The present result
reproduces the published lower bound.
