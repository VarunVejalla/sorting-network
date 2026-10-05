# Boundary transfer, localization, and the charging obligation

## Status

The [two-block transition update](kahale-rankset-transition.md) derives the
signed innovation/residual ledger, proves a fresh-history budget, and identifies
redundancy among static linear block potentials.

The base-two lower-bound coefficient remains `3.270559...`. The goal preferably
exceeds 4. This tranche completes the exact boundary-transfer formalization,
adds entropy monotonicity, and identifies a structural restriction on coupling
creation. It does not prove a stronger sorting-depth bound.

## Checked boundary identity

`BoundaryTransfer` proves

```text
delta H(relative block order | block rank set)
  = delta H(insertion position | block rank set)
    - delta boundaryCoupling.
```

The untouched vector is fixed, and the moved rank is distinct from its ranks
before and after the update. Both side conditions are explicit.
`InsertionFibers` proves that the block rank set and insertion ordinal have
exactly the same fibers as the remaining rank set and the moved rank.
Consequently their finite entropies agree even when the prefix image is not
uniform. `ComparatorTransfer` discharges the distinctness conditions for an
actual comparator using injectivity preservation.

`EntropyMonotonicity` proves that deterministic coarsening cannot increase
`finiteEntropy`, and that conditional entropy is nonnegative. It does **not**
yet prove conditional mutual-information nonnegativity or data processing.

All new focused builds and guarded axiom audits succeeded using only
`propext`, `Classical.choice`, and `Quot.sound`.

## Whole outside blocks prevent apparent information duplication

For a fixed block `A`, use

```text
K_A = I(P_A ; Y_(outside A) | R_A).
```

Here `R_A` is its rank set and `P_A` its relative ordering. Unlike a single
outside coordinate, the whole outside vector does not hide how information
is redistributed among outside wires.

Conditional data processing gives this classification:

| Comparator endpoints | What happens to `K_A` |
|---|---|
| both in `A` | cannot increase: `R_A` is preserved and `P_A` is processed deterministically |
| both outside `A` | cannot increase: the inside variables are fixed and the outside vector is processed deterministically |
| one in each | can increase: membership of the rank set changes |

This is a derived information-theoretic statement, **not yet a Lean theorem**.
Ordinary entropy monotonicity alone does not prove conditional data processing.

For a disjoint partition, a gate therefore creates coupling only in the two
blocks it crosses. A gate internal to one block cannot create it in any block.
`LocalizedCharging.positive_creation_localized` proves the support accounting
under an explicit stability hypothesis; it does not silently assume the
information-theoretic classification.

## Exhaustive finite evidence

[The finite probe](kahale-transfer-localization-results.json) covers all 7101
five-wire rank distributions, single comparators, and blocks of sizes 2 and 3:

- 284040 internal instances;
- 284040 outside instances;
- 852120 crossing instances.

The largest observed stable-block increase is `1.8e-15`, numerical roundoff.
Crossing gates can increase coupling by about `0.324511` bits.

A single-outside observer has an actual increase of about `0.275489` under a
gate wholly outside the block, while whole-outside coupling is unchanged:

```text
prefix: (0,1), (0,2), (1,2), (2,3), (2,4)
gate: (3,4)
block: {0,2}, observed outside wire: 3
single coupling: 0.0490225 -> 0.324511
whole coupling:  0.324511  -> 0.324511
```

That rise redistributes existing information; it is not new coupling with
the entire outside block. Counts are exact integers; entropies are numerical.

## A tempting local charge fails

The proposed inequality

```text
max(delta K_A, 0) <= C*(1 - gate_information_gain)
```

cannot hold universally for any fixed `C`: coupling can be created at a fully
efficient comparison. The finite probe records positive creation at gates
whose every output has two equal-weight predecessor fibers. This integer
certificate gives information gain exactly one bit. One recorded example
has every wire already appearing in the prefix's comparisons; that fact does
not assert that every possible first-use credit is exhausted.

There is also a simple derived four-wire construction. Begin with uniform
rank permutations and compare positions `0,2`, taking `A={0,1}`. Conditional
on the resulting inside rank set `{0,2}`, the three equally likely inside/
outside orientation cells are

```text
(inside low first, outside low first),
(inside low first, outside high first),
(inside high first, outside high first).
```

Their mutual information is `log_2(3)-4/3 > 0`, since `3^3>2^4`. This rank-set
event has probability `1/4`; its contribution is `(log_2(3)-4/3)/4`.
Initially the conditional coupling is zero, and the comparator gains exactly
one bit. Nonnegativity of the other conditional contributions makes the full
coupling increase positive. This argument is derived, not kernel checked.

### A scalable version, with its limitation

Repeat that gadget on `r` disjoint four-wire blocks, conditioning each local
diagnostic additionally on its gadget's complete rank set. Conditional local
orders are uniform, so each copy has the same entropy calculation. One
parallel layer gains `r` bits, wastes none of its `r` actual comparison slots,
and creates at least `r*(log_2(3)-4/3)/4` of summed local coupling.

This disproves an own-comparison-loss charge at arbitrarily large widths.
It does **not** refute the desired asymptotic bound: the creation is only
`O(n)`, which an explicit boundary reserve may cover. It also does not identify
the block-conditioned diagnostic with the unconditioned global subset average.
A full sorting completion can be appended to this prefix; the calculation
concerns its initial layer.

## The precise charging target

Use a bank based on whole-block dependence and an explicitly accounted
rank-set progress term. Seek

```text
gain_t + B_(t+1) - B_t <= (1-rho)*floor(n/2) + error_t,
B_0 - B_d = o(n*log n),
sum_t error_t = o(n*log n).
```

For a coefficient above 4, require `rho>1/2`. Above `0.388483827...` would
already improve the current coefficient. These are open targets.

The main new restriction is that positive whole-block coupling changes must
be assigned to actual boundary-crossing events. The per-block identities and
the partition classification must be combined; creation cannot be paid for
only from that same gate's loss.

`LocalizedCharging.positive_variation_balance` proves exactly

```text
sum positive bank increments - sum positive bank decrements = B_d - B_0.
```

Equal endpoints therefore equate creation and consumption; they do not bound
either total. Any coupling unit consumed and later recreated needs a new
charge. This accounting prevents counting the same stored unit repeatedly
as independent slack, while leaving the quantitative creation bound open.

For a full partition rank-set vector `R` and joint relative-order vector `P`,
the original rank vector is reconstructed by `(R,P)`, so

```text
H(Y) = H(R) + H(P|R).
```

Crossing gates change both terms. A proof cannot discard the rank-set term or
replace joint relative orders by independent block entropies.

Nor is a merge-based exception automatically subleading: merging singleton
blocks into one block has interleaving budgets whose binomial coefficients
multiply to `n!`. Their entropy sum is `log_2(n!)`, a leading-order cost, even
though there are only `n-1` merges. A merge ledger must charge that cost in the
main inequality rather than hide it in an `O(n)` exception.

## Next obligations

1. Prove conditional mutual-information nonnegativity and conditional data
   processing for `finiteEntropy`.
2. Formalize whole-block localization for internal, outside, and crossing
   comparators.
3. Derive the coupled rank-set/order update for the two touched blocks and
   retain its signed terms.
4. Prove a uniform bound on creation/consumption or a controlled exception
   budget. This is the substantive missing lower-bound lemma.

## Reproduction

```text
lake build AKS.Kahale.InsertionFibers AKS.Kahale.BoundaryTransfer AKS.Kahale.BoundaryTransferAxioms AKS.Kahale.ComparatorTransfer AKS.Kahale.ComparatorTransferAxioms AKS.Kahale.EntropyMonotonicity AKS.Kahale.EntropyMonotonicityAxioms AKS.Kahale.LocalizedCharging AKS.Kahale.LocalizedChargingAxioms
python -B scripts/kahale_transfer_localization.py --output docs/kahale-transfer-localization-results.json
```
