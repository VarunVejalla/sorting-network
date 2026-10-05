# Coupling certificate union costs through the shared input universe

## Checked result

For a standard comparator after an arbitrary prefix network on `n` inputs,
suppose it is active: some Boolean input supplies `1` to its smaller-index
input and `0` to its larger-index input. Then

\[
z_{\max}+o_{\min}\le n+2,
\]

where `z_max` is the minimum zero-certificate size on the max output, and
`o_min` is the minimum one-certificate size on the min output.

The Lean theorem states the stronger concrete witness form: there are a zero
certificate `S` on the max output and a one certificate `T` on the min output
with `|S|+|T| <= n+2`. Therefore the sum of the two minima has this bound.

This inequality couples the two union costs that the separate input minimum
sizes do not determine. It is sharp: compare the ORs of two disjoint nonempty
input groups covering all `n` inputs. The max output has minimum zero size
`n` and the min output has minimum one size `2`.

The result is a local certificate constraint. No new asymptotic coefficient,
historical novelty, or uniform overlap loss at every gate is claimed.

## Rank-crossing proof

1. A Boolean inversion supplies a rank permutation for which the two incoming
   wires have inverted ranks. This uses a sorting permutation for the Boolean
   input and commutation with monotone relabeling.
2. On the identity rank input, the ranks at those wires are in the opposite
   order: a standard comparator network fixes sorted inputs.
3. Adjacent input-rank transpositions generate every permutation. Each such
   transposition changes each output rank by at most one, and output ranks
   remain distinct. Therefore relative order cannot change without a permutation
   that puts consecutive ranks `r,r+1` on the two wires.
4. Under that permutation, fixing the `r+2` lowest-rank inputs to zero forces
   both wires to zero. Fixing the `n-r` highest-rank inputs to one forces both
   wires to one. The two sets have total size `n+2`.
5. The first set is consequently a zero certificate on the comparator's max
   output; the second is a one certificate on its min output.

The proof uses neither a sorting assumption on the prefix nor a published theorem
as an axiom. Activity and standard comparator orientation are essential. A
redundant comparator need not satisfy this bound; comparing already sorted
global minimum and maximum can have the two costs sum to `2n`.

## Structural consequence

If the comparator is the final operation and the resulting network sorts,
sorting imposes

```text
z_max >= j+1,       o_min >= n-i,
```

for its endpoints `i<j`. Combining these with the coupling inequality forces
`j=i+1`. Thus an active final comparator must join adjacent wires.

This recovers an existing structural restriction: the nonredundant last-layer
adjacency lemma in [Codish, Cruz-Filipe, and Schneider-Kamp,
*Sorting Networks: the End Game*, Lemma 3](https://imada.sdu.dk/~lcf/pubs/paper18.pdf).
Our certificate argument provides a checked interface to that restriction;
it does not improve the published result.

## Formal endpoints

`lake build AKS.Kahale` passes, including guarded dependency checks for the
coupling and width theorems. Their dependencies are only `propext`,
`Classical.choice`, and `Quot.sound`. The focused source gate passes as well.

[`AKS/Kahale/RankCrossing.lean`](../AKS/Kahale/RankCrossing.lean):

```lean
Kahale.boolean_inversion_rank_witness
Kahale.inverted_ranks_have_adjacent_witness
```

[`AKS/Kahale/UnionCoupling.lean`](../AKS/Kahale/UnionCoupling.lean):

```lean
Kahale.rank_threshold_certificate_pair
Kahale.active_comparator_union_cost_coupling
Kahale.active_final_comparator_adjacent
```

## Next quantitative obligation

### Suffix-depth consequence, now checked

The rank-crossing argument also combines directly with the existing suffix
rank covers. If `s` parallel stages remain after an active comparator `(i,j)`
in a sorting network, then

\[
j-i\le2^{s+1}-1.
\]

An adjacent-rank input makes the comparator's two output ranks consecutive,
say `r,r+1`. The suffix fanout/rank-interval bound places each rank less than
`2^s` away from its wire index. Hence the endpoint separation is at most
`(2^s-1)+1+(2^s-1)`. This is formalized as
`Kahale.active_comparator_width_le` in
[`AKS/Kahale/ActiveWidth.lean`](../AKS/Kahale/ActiveWidth.lean).
It gives widths `1,3,7,...` for suffix lengths `0,1,2,...`.

This is a structural restriction consistent with the known last-layer and
block results. Activity is essential: a wide comparator whose inputs are
already ordered on every input can remain redundant and need not obey it.
We have not shown that this restriction alone excludes the positional
height witness at its exponential rate.

### Remaining quantitative step

To improve the depth coefficient, a local shared-universe constraint must be
combined with requirements on the remaining suffix and on many output ranks.
The final-comparator consequence only constrains the last operation; by itself
it contributes no logarithmic coefficient improvement.

The next step is a depth-dependent potential combining the union-cost coupling,
the suffix width restriction, and the simultaneous threshold requirements
on many wires. The known block restrictions provide a reference point for
distinguishing a new asymptotic argument from a rederivation of existing
structural lemmas. Uniform monomial growth alone has the barrier proved in
the joint-potential analysis.
