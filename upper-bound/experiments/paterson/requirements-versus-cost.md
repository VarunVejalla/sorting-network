# Requirements versus cost

All logarithmic sorting coefficients below use log base 2.
Source links refer to the completed implementation in `alternatives/legacy`.

## Existing cost decomposition

The [forest depth recursion](../../alternatives/legacy/AKS/Separator/PatersonForestDepth.lean)
charges at most 989 per comparison round, 561 per root split, and 561 for a
terminal sort. Children execute in parallel: root splits cost once per level
on the deepest path, rather than once per tree node.

The [stage certificate](../../alternatives/legacy/AKS/Paterson/Accounting.lean)
uses `S(k) = 13 * ceil(k/2)` for `2^k` wires. The final
[known-permutation correction](../../alternatives/legacy/AKS/Separator/PatersonForestSorts.lean)
costs at most `k`. Consequently the checked coefficient is

    (13/2) * 989 + 561 + 1 = 6990.5.

The separator depth is
`263 + 155 + 167 + 187 + 217 = 989`; the latter four levels total 726.
See [stage construction](../../alternatives/legacy/AKS/Separator/PatersonConstruction.lean)
and [partial-bag refinement](../../alternatives/legacy/AKS/Separator/PatersonRefinement.lean).
The initial level simultaneously satisfies the supported rare-rank and
large-cohort splitting contracts. Its cost is a maximum of the two certified
requirements, not the sum of two successive full stages.

## Primitive contracts actually consumed

| Requirement | Current instance | Proof consumer / replacement obligation |
|---|---|---|
| Two-sided supported extreme ranks | Every integer rank `j <= .02 m`; at most `e j` escape the appropriate fringe; full-bag fringe `m/32` | [Supported separator definition](../../alternatives/legacy/AKS/Separator/PatersonDefs.lean), [old-stranger filtering](../../alternatives/legacy/AKS/Paterson/BagSeparator.lean). A total error bound proportional to `m` is insufficient. |
| Large-cohort half split | Support `alpha = 81773/89250`, split error `beta = 1/62` | [Fresh strangers](../../alternatives/legacy/AKS/Paterson/Fresh.lean). Needed in addition to the rare-rank contract. |
| Partial and padded bags | Actual support `mu * capacity / actualCard`, with error `beta + refinementError` | [Scheduled partial contract](../../alternatives/legacy/AKS/Paterson/ScheduledContract.lean). The support may exceed .02; a full-bag certificate alone does not cover this case. |
| Fringe and allocation compatibility | Rounded multiples of 32, actual scheduled fringe covers the primitive's fringe, both half-block padding and routing fit | [Scheduled contract](../../alternatives/legacy/AKS/Paterson/ScheduledContract.lean). Reducing primitive depth must preserve these inequalities. |
| Root rebuild | Exact native-half separation and bounds for nested bins and rebuilt bags, while deep bags remain unchanged | [Root bin errors](../../alternatives/legacy/AKS/Paterson/RootSortedBins.lean), [rebuild invariant](../../alternatives/legacy/AKS/Paterson/RootRebuildInvariant.lean). |

These contracts apply to oblivious comparator networks for every admissible
input, not an input-dependent selection algorithm. For small ranks `e j < 1`,
the integer escape count must be zero. Losing these small-rank guarantees would
break the filtering argument.

## Error headroom at the existing parameters

The [generic interior inequalities](../../alternatives/legacy/AKS/Paterson/BagParams.lean)
are instantiated by [fastParams](../../alternatives/legacy/AKS/Paterson/FastParams.lean):

    A = 4.75, mu = .0199, delta = 1/57, nu = .707,
    lambda = 3811/59500, minimum capacity = 300000, rounding allowance = 10.

Exact arithmetic in `audit_budget.py` gives:

| Quantity | Current value | Admissible ceiling / slack at fixed geometry |
|---|---:|---:|
| Full-bag tail error `e` | 0.04383542002 | strictly below 0.04502777778 |
| First split error `beta` | 0.01612903226 | strictly below 0.01873696345 from the unrounded first inequality |
| Partial-bag filtering error | 0.05493932665 | requires its own scheduled-source proof; not interchangeable with `e` |
| Rounded first-stranger inequality | — | residual slack 0.00001934291168 |

The rounded inequality couples `alpha`, `beta`, and `e`, so the two ceilings
cannot be independently saturated. There is little room to relax the current
errors without modifying the geometry or rounding proof. A dramatically
cheaper primitive must meet essentially these contracts, or come with new
global invariant parameters and their proofs.

## Root repair: opportunity and limitation

The current [root budget](../../alternatives/legacy/AKS/Paterson/Root.lean)
sorts an upper region of fewer than `2^33` registers, costing
`33 * 34 / 2 = 561` bitonic layers. It contains cold storage and shallow bags.
Deep level-six stranger counts vanish at the root ceiling; this supports
exact separation into native halves.

Full sorting is a sufficient implementation of the required postconditions.
A replacement could instead perform hierarchical partitioning. To reuse the
present rebuild proof, it must provide the native-half purity and the
`upper_sorted_subset_errors` bounds for the ancestor bins consumed when
rebuilding levels 2 and 4. Merely partitioning into two halves does not prove
the level-2 and level-4 stranger bounds. A useful adapter theorem would state
these postconditions without mentioning bitonic sorting.

The constant-size terminal sort contributes only an additive constant.
The repeated root repair contributes 561 to the asymptotic coefficient.
Cheaper leaves alone cannot remove that contribution.

## Recommended next step

Extract two abstract adapters in this experiment: a scheduled comparison
contract covering full and partial bags, and a root-rebuild contract covering
the exact consumed bin bounds. Then investigate a restricted, hierarchical
root partitioner alongside a cheaper supported separator. Evaluate candidates
with the conditional budget before undertaking their full global proofs.

A hybrid with Chvatal is possible only after its primitive is shown to satisfy
these contracts (or the scheduler is changed). Existing correctness of a
different separator does not supply that adapter automatically. No current
construction in this audit establishes coefficient 200.
