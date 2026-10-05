# Can coalition congestion improve the leading coefficient?

## Current conclusion

**No increased asymptotic coefficient has been proved.** The coalition
inequality is valid, and its finite obstruction is genuinely collective, but
we do not yet have a quantitative loss that persists across logarithmically
many layers.

This follow-up establishes a limitation of the reachability relaxation,
quantifies the gain needed for a stronger bound, and attempts symbolic
searches at the critical suffix scale. The searches are inconclusive, not
negative results.

## The required quantitative gain

Write

\[
\alpha=1-\log_2\varphi=0.305758086369\ldots.
\]

The existing proof has the form

\[
nF_{d+1}\le2^{d+1}(d+1)^2,
\]

which gives `log_2 n <= alpha*d + O(log d)` and coefficient `1/alpha`.
One sufficient strengthening would be

\[
nF_{d+1}\le2^{(1-\delta)d}\operatorname{poly}(d)
\]

for a universal fixed `delta>0`. It would give coefficient
`1/(alpha-delta)`. This is a sufficient proof target, not a necessary form
that every improved proof must take.

| Target coefficient | Required `delta = alpha - 1/C` |
|---|---:|
| 3.3 | 0.002727783339 |
| 3.5 | 0.020043800655 |
| 4 | 0.055758086369 |

For example, if a valid strengthened counting argument accumulated a factor
`r>1` over `theta*d` stages, its gain would be
`delta=theta*log_2(r)`. At `theta=0.1`, the target `3.3` requires approximately
`r=1.01908743`, while `3.5` requires approximately `r=1.14904716`.
These parameters are illustrative arithmetic, not established stage losses.

A Hall deficit of one for a single input does not supply such a factor.
Neither does observing related deficits at several cuts: those may be repeated
manifestations of the same obstruction. A proof needs an appropriate weighted
count and a conditional or otherwise justified accumulation of loss.

## A proved limitation of reachability capacity

If every source wire reaches every output, all coalition inequalities become
automatic: for any target set `B` and source coalition `A` with
`|A| <= |B|`,

\[
|A|\le| (\bigcup_{i\in A}R(i))\cap B |.
\]

The empty coalition is trivial; for every nonempty coalition the union is the
whole output universe. This generic statement and zero Hall deficit are
formalized in
[CongestionBarrier.lean](../AKS/Kahale/CongestionBarrier.lean).

The focused build of that module and
[its separate axiom audit](../AKS/Kahale/CongestionBarrierAxioms.lean) passed.
Both new theorems depend only on `propext`, `Classical.choice`, and `Quot.sound`.

Such reachability is inexpensive. On `n=2^m` wires indexed by binary strings,
compare pairs differing in bit `r` at layer `r`, for `r=0,...,m-1`.
After these `m` layers, a value can reach any wire: inductively, each layer
adds the choice of one more coordinate. The layer comparators have disjoint
endpoints and use the standard ascending orientation.

Therefore any cut whose suffix contains this full mixing block has complete
reachability, and its Hall conditions impose no restriction beyond total
zero/one counts, for **all** inputs and **all** rank slices. A preceding suffix
segment does not change this conclusion, since every wire has some path into
the full mixing block.

This construction is not asserted to sort, and does not provide a sorting
network near coefficient `3.27`. It also does **not** exclude an improvement
from cuts inside the final `log_2 n` layers. The critical Kahale suffix scale
is about `0.904 log_2 n`, which lies inside that range. The limitation narrows
where a reachability-only argument must find its quantitative gain.

The general binary-coordinate construction and its induction are mathematical
arguments here; the new Lean module proves the complete-cover implication,
not a formal construction of the binary-coordinate network.

## A deeper issue: independent slices versus coherent rank routing

Complete reachability permits a matching for each rank slice separately. It
does not ensure that those matchings can come from one set of comparator
decisions for a full rank permutation.

For one input rank permutation, its threshold inputs yield a nested chain
of zero sets of sizes `0,1,...,n`. The prefix preserves that nesting and those
sizes. Their routes through the suffix must all agree with the same routing
of the distinct rank values. Independent Hall checks discard that agreement.

The mixing block above makes this loss explicit. As an unrestricted switching
network, it has `nm/2` switches, hence at most `2^(nm/2)` routing permutations,
despite its complete source-to-output reachability. For `n=4` this is at most
16 routes, fewer than the 24 rank permutations that sorting must accommodate.
Each fixed routing permutation can send at most one input rank permutation
to the identity output. No enumeration assumption is needed for this count.

Counting compatible switch decisions alone recovers only the familiar
comparison-count argument

\[
d\ge\frac{2\log_2(n!)}n=2\log_2 n-O(1).
\]

It is weaker than the existing coefficient. A useful improvement must couple
this global compatibility with the certificate-growth restrictions, rather
than merely take the maximum of the two existing lower bounds. One possible
target is to bound the number of compatible rank chains a suffix can handle
when its preceding certificate profiles are near the scalar extremizer.
No such quantitative bound has been proved in this work.

## Symbolic search at longer suffix depths

[kahale_congestion_search.py](../scripts/kahale_congestion_search.py) encodes
the actual 161-wire prefix with exactly 88 input zeros. It requires:

- a valid individual destination for every prefix zero and one;
- correct zero capacity in every connected suffix component;
- a collective zero-routing Hall deficit.

The unrestricted mode chooses both the source coalition and a destination
set symbolically. A second mode restricts destination cuts to unions of one
or two neighborhoods and neighborhoods of contiguous source intervals.
This second mode is incomplete as a search for Hall witnesses.

With Z3 `4.13.4` and a 15-second solver timeout per case:

| Remaining layers | Full symbolic search | Restricted destination cuts | Number of restricted cuts |
|---|---|---|---:|
| 5 | Timeout / unknown | Timeout / unknown | 634 |
| 6 | Timeout / unknown | Timeout / unknown | 633 |
| 7 | Timeout / unknown | Timeout / unknown | 580 |

The restricted search at four remaining layers also timed out, despite the
independently established seeded witness at that depth. This illustrates why
these timeouts cannot be interpreted as absence of obstructions.

The script re-evaluates any SAT witness by direct Boolean execution and exact
matching. An UNSAT answer would be solver evidence only, not a Lean proof;
in restricted mode it would cover only the selected destination-cut family.
All recorded outcomes here are `unknown` with reason `timeout`.

Results:
[full search](kahale-congestion-search-161.json),
[restricted search](kahale-congestion-cuts-161.json),
[four-layer search](kahale-congestion-cuts-control.json).

## What remains unproved

The central missing statement is a universal exponential restriction on
**compatible rank chains**, conditional on shallow prefix certificate growth.
The full-cover lemma shows why independently summing slice reachability
constraints can lose crucial information. It does not prove that every
possible coalition-based argument fails.

The user has subsequently set **4** as the research target. The
[rank-information follow-up](kahale-target-four.md) formulates an amortized
certificate/information bank with controlled endpoints and rules out two
pointwise entropy penalties. Its central inequality remains unproved; neither
`3.3` nor `4` is a claimed improvement or an evidence-based forecast.

## Reproduction

```sh
python -B scripts/kahale_congestion_search.py --output docs/kahale-congestion-search-161.json
python -B scripts/kahale_congestion_search.py --mode cuts --output docs/kahale-congestion-cuts-161.json
python -B scripts/kahale_congestion_search.py --mode cuts --suffix 4 --output docs/kahale-congestion-cuts-control.json
lake build AKS.Kahale.CongestionBarrier AKS.Kahale.CongestionBarrierAxioms
```
