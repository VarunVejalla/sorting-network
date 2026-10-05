# Global rank congestion at a suffix cut

## Result and limits

We now have a kernel-checked **coalition capacity inequality**, rather than
another weighted pair-cost experiment. It requires simultaneous rank routing
and can detect obstructions that singleton reachability and suffix-component
zero counts miss.

In the 161-wire scalar barrier schedule, a coalition of 12 prefix zeros has
only 11 admissible output destinations with four layers remaining. Every
proper subset of this coalition can be routed to admissible destinations.
Thus singleton and pairwise routing tests on that coalition miss the failure.

**There is still no improved asymptotic coefficient.** These finite examples
occur near the end of the network. An obstruction to one bad schedule, or a
bounded number of terminal layers, does not establish a loss in the leading
coefficient for arbitrary sorting networks.

## The global necessary condition

At a cut, write `pre` for the prefix and `suffix` for the remaining parallel
layers. Let `R(i)` be the set of output positions reachable from prefix wire
`i` by paths through the suffix. Paths can follow either endpoint of a
comparator, respecting layer order. This permits more routing choices than
the actual comparator values, so it is a necessary-condition relaxation.

Suppose a Boolean input has `k` zeros, and `A` is any set of zero-valued prefix
wires. In a sorting completion their values must occupy distinct positions
among the first `k` outputs. Consequently

\[
|A|\le\left|\left(\bigcup_{i\in A}R(i)\right)\cap\{0,\ldots,k-1\}\right|.
\]

This must hold for **every** coalition `A`, not merely singletons. There is a
dual condition for one-valued wires and the last `n-k` output positions.
For the reachability relaxation, all these inequalities together characterize
the existence of a matching. A matching itself does not guarantee a sorting
completion: paths may compete at intermediate layers, and comparator decisions
are determined by the values.

The certificate version is particularly useful. If one input set `S` is a
zero certificate for every wire in `A`, set exactly `S` to zero. Then

\[
|A|\le\left|\left(\bigcup_{i\in A}R(i)\right)\cap\{0,\ldots,|S|-1\}\right|.
\]

For separately chosen certificates `S_i`, apply this to their union. Unlike
separate size estimates, this keeps the capacity demanded by the coalition.

Define `rho(A)` as the least `k` for which `A` can be matched to the first `k`
output positions. Every common zero certificate for `A` in a prefix admitting
this sorting suffix must then have size at least `rho(A)`. The inequality
formalized here applies to every subset of `A`, which supplies the matching
conditions. `rho` and this matching equivalence are explained mathematically;
they are not additional Lean definitions or equivalence theorems.

## Formal proof

[RankCongestion.lean](../AKS/Kahale/RankCongestion.lean) contains:

- `rank_cover_hall`: distinct prefix rank values cannot fit into a smaller
  union of allowed output ranks;
- `sorted_suffix_zero_hall`: the Boolean coalition inequality above;
- `sorted_suffix_certificate_hall`: its common-certificate specialization.

The proof embeds a Boolean input into a rank permutation, uses monotonicity
to bound the ranks of its zero-valued wires, and uses the existing suffix
rank-cover theorem. Injectivity of prefix rank execution supplies the capacity
constraint. This implements zero-count conservation through distinct ranks.

The formal theorem uses `A.biUnion (fun i => suffixReach suffix {i})`, exactly
the union of individually time-ordered reachability sets used by the script.
It assumes the concatenated network sorts and proves a necessary condition;
it does not assume that the bad schedule sorts.

The dual one-valued inequality is used in the Python investigation and follows
by the corresponding upper-rank argument. This new module formalizes the
zero-valued and zero-certificate versions only.

The focused build `lake build AKS.Kahale.RankCongestion AKS.Kahale.Axioms`
passed. Guarded checks for the three new theorems report only `propext`,
`Classical.choice`, and `Quot.sound`. No additional axioms or trust extensions
were introduced.

## A collective obstruction missed by smaller coalitions

The depth-40 schedule has 161 wires and passes the scalar positional height
constraints. With seed `0`, input trial `17` has 88 zeros. After 36 layers,
the following wires all contain zero (indices are zero-based):

```text
58, 59, 67, 68, 69, 77, 78, 79, 80, 88, 89, 90.
```

Their reachable output positions below 88 have union

```text
43, 50, 58, 59, 67, 68, 69, 77, 78, 79, 80.
```

There are 12 source wires and only 11 destinations. Among this coalition:

| Routing requirement | Least output-prefix size sufficient |
|---|---:|
| Worst singleton | 60 |
| Worst pair | 69 |
| All 12 wires together | 89 |

Every proper subset of these 12 wires can be matched within the first 88
outputs. This claim concerns subsets of this particular witness, not every
small coalition elsewhere in the network.

For this input and cut, every prefix zero and one individually has a correctly
colored reachable output. Moreover, each connected suffix component already
has the required number of zeros for its final wire positions. The deficit
therefore comes from time-ordered reachability inside components, rather than
their total capacity. The exact input, prefix values, and witness sets are in
the [results file](kahale-rank-congestion-results.json).

This is an exact Python computation. The general implication from a capacity
deficit to failure of sorting is kernel checked; the 161-wire instance has
not itself been evaluated inside Lean.

## Scaling probe

Sampling 64 independent-bit inputs for each scalar barrier schedule gives:

| Depth | Wires | Largest remaining depth with a witnessed Hall failure passing singleton and component-capacity checks |
|---|---:|---:|
| 32 | 36 | None found |
| 36 | 76 | 5 |
| 40 | 161 | 4 |
| 44 | 344 | 4 |
| 48 | 738 | 4 |

Separate fixed-zero-count samples examine 16 inputs at each of
`k=4,8,16,32,64,128` on 161 and 738 wires. In this sample, additional failures
passing both simpler checks occur only with two or three layers remaining.
The [rank-slice results](kahale-rank-congestion-slices.json) record all cases.

Absence of a sampled witness is not evidence that a universal Hall condition
holds. Nevertheless, these findings currently support finite structural
pruning, not an asymptotic improvement. In particular, we have not exhibited
congestion persisting at a positive fraction of `log_2 n` remaining layers.

## Relation to published structure

Suffix-component restrictions are already part of the literature:
Codish, Cruz-Filipe, and Schneider-Kamp analyze suffix blocks and constrain
their mixtures and the comparators joining them in
[Sorting Networks: the End Game](https://imada.sdu.dk/~lcf/pubs/paper18.pdf),
Lemma 8 and Theorem 11. The current probe retains time-ordered reachability
inside those components. No historical novelty claim is made for the Hall
condition or the routing formulation.

## Next proof obligation

The useful next question is whether **many rank slices at many cuts** must
create a quantitative capacity loss, rather than whether one schedule has a
late Hall deficit. A possible formulation counts how many prefix zero sets
can simultaneously satisfy the suffix matching conditions for each rank
slice, and compares that restriction with what a shallow prefix can produce.

We need a universal quantitative inequality for this restriction. Merely
counting a late witness or summing observed matching deficiencies cannot
justify a stronger coefficient. Intermediate-layer capacities are also a
possible refinement if reachability alone remains too permissive.

## Reproduction

```sh
python -B scripts/kahale_rank_congestion.py --depth 32 36 40 44 48 --output docs/kahale-rank-congestion-results.json
python -B scripts/kahale_rank_congestion.py --depth 40 48 --zeros 4 8 16 32 64 128 --trials 16 --output docs/kahale-rank-congestion-slices.json
lake build AKS.Kahale.RankCongestion AKS.Kahale.Axioms
```
