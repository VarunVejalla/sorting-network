# Paterson global cost audit

All coefficients use `log_2`. This note audits the completed legacy scheduler;
it does not claim a new sorter.

## What the global recursion actually charges

**Kernel checked.** Along one recursive path, a comparison phase costs `989`,
a root split costs `561`, and the two child calls run in parallel. The initial
fuel is `13 * ceil(k/2)` and the final known-rank permutation costs at most
`k`. Thus the checked coefficient is

```
(13/2) * 989 + 561 + 1 = 6990.5.
```

The recurrence and depth proof are in
[`PatersonForestDepth.lean`](../../alternatives/legacy/AKS/Separator/PatersonForestDepth.lean),
the fuel certificate in
[`Accounting.lean`](../../alternatives/legacy/AKS/Paterson/Accounting.lean),
and the final theorem in
[`PatersonTight.lean`](../../alternatives/legacy/AKS/Bounds/PatersonTight.lean).
Local bags within a phase are disjoint and execute in parallel, so the useful
target is one uniformly cheaper local network, not a saving summed over bags.
The terminal `561` is additive; the root-split `561` is paid once per binary
scale and contributes to the coefficient.

## The drop-in separator contract

A replacement used by the current scheduler must be an oblivious comparator
network family for every scheduled full and partial bag, with a uniform depth
bound `s`, and must provide all of the following.

1. **Relative two-sided tail filtering.** For every supported extreme cohort,
   at most `e` times its actual cardinality may remain in the middle. The full
   instance uses support `mu = 199/10000`, fringe `m/32`, and
   `e = 9978053/227625354` (about `.0438354`). The consumer is
   [`BagSeparator.lean`](../../alternatives/legacy/AKS/Paterson/BagSeparator.lean).
   A bound proportional only to bag size is too weak, particularly when
   `e*j < 1`, where integrality forces zero survivors.
2. **The simultaneous first split.** The same first-level network must also
   split the large cohort with support `81773/89250` and error `1/62`; separate
   networks would add their depths. This feeds fresh-stranger control, not just
   old-stranger filtering.
3. **Partial bags and padding.** On a partial bag the required support is
   `mu * capacity / actualCard`, and the checked error is the first-level error
   plus refinement error. This support can exceed `.02`. The exact consumer is
   [`ScheduledContract.lean`](../../alternatives/legacy/AKS/Paterson/ScheduledContract.lean).
4. **Geometry compatibility.** The construction must work with even actual
   arity, virtual half padding, the 32-lattice fringe target, and the existing
   routed left/right output sets. It must preserve the execution equalities
   used by the stored allocation, not merely prove an abstract halving claim.

The present `989` is `263 + 155 + 167 + 187 + 217`; the last four refinement
levels total `726` ([`PatersonConstruction.lean`](../../alternatives/legacy/AKS/Separator/PatersonConstruction.lean)).
This explains the leverage, but deleting refinements is valid only if the new
network still supplies items 1--4. In particular, the experimental sparse or
extreme-core halver does **not** replace the separator: its small core and error
contract do not imply the scheduled fringe, partial support, or large-cohort
first split (see
[`extreme-core-construction-and-forecast.md`](../paterson/extreme-core-construction-and-forecast.md)).

## A complete conditional budget below 1000

**Derived, not formalized.** Keep the checked parameters, fuel certificate,
allocation, root rebuild, terminal cases, and final permutation. If one proves
a scheduler-compatible family satisfying items 1--4 with uniform depth
`s <= 67`, and threads it through the existing comparison-phase proofs, then

```
limsup D(n)/log_2(n) <= 6.5*s + 561 + 1 <= 997.5.
```

This is a complete cost budget: no cheaper root operation is needed for the
sub-1000 target. The concrete missing obligations are:

- construct the full and partial networks at every scheduled arity with depth
  at most `67`;
- prove the relative two-tail guarantee and simultaneous large-cohort split
  for the same first-level execution;
- prove the padding, fringe coverage, and routed execution adapters used by
  `scheduledLocalNetwork`;
- parameterize the current phase/depth modules by that contract (they presently
  name the Paterson networks), then rerun the forest correctness and depth
  induction.

The scalar error margins are already narrow at the current geometry, so merely
weakening error to obtain depth `67` is not justified. Changing errors requires
new feasible `A, mu, delta, nu`, fresh-stranger inequalities, allocation and
rounding proofs, and a new stage ratio. The relevant conditional arithmetic is
summarized in [`conditional-bound.md`](../paterson/conditional-bound.md).

## Feasibility of the target near 200

**Conditional arithmetic.** With this scheduler the general coefficient is
`6.5*s + r + 1`, where `r` is the repeated root-rebuild depth. Keeping the
checked `r = 561` makes `200` impossible even at `s = 0`. Exact coefficient
`200` would require, for example, `(s,r) = (30,4)` or `(24,43)`; a strict bound
below `200` requires `6.5*s + r < 199`.

The root operation need not fully sort, but a replacement must give exact
native-half purity plus the level-2 and level-4 rebuilt-bin stranger budgets,
while leaving deeper bags local. That source-level interface is extracted in
[`root-repair-interface.md`](../paterson/root-repair-interface.md); no such
low-depth network is currently proved. Avoiding repeated core sorting is
therefore actionable only as a joint separator/root-partitioner design with
explicit `(s,r)` and the full scheduler adapters. Existing core concentration
alone has no global coefficient consequence.

## Status

- **Checked:** the `6990.5` endpoint, `6.5` fuel slope, `989` comparison depth,
  `561` repeated root cost, and all current separator/scheduler contracts.
- **Derived but unaudited in Lean:** the parameterized formula
  `6.5*s + r + 1`, the depth-67/sub-1000 substitution, and the extracted root
  adapter.
- **Open research:** a depth-67 complete scheduled separator; and, for a target
  near `200`, both a roughly depth-30-or-less separator and a root partitioner
  costing only a few dozen layers while satisfying the rebuild interface.
