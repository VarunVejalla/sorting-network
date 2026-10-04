# Root splitting: proposed completion argument

Status: **formalized**. The actual rebuild and child invariant are checked in
`RootRebuildInvariant` and `ChildInvariant`; the terminating forest and final
rank correction establish full sorting in `PatersonForestSorts`. The final
bound is `limsup D(n)/log_2 n <= 6990.5`, with endpoints in
[PatersonTight](../AKS/Bounds/PatersonTight.lean). The argument below records
the design that guided these proofs.

## Rebuild the upper allocation after sorting

At an active-root stage, sort the union of cold storage and levels 0, 2, and 4.
Every deeper register belongs to one of the 64 level-6 subtrees. Their actual
contents have the same cardinality `T6`, by the allocation invariant, so the
sorted region has cardinality `U = N - 64*T6`.

For `N >= 64`, `U` is divisible by 64. Partition its sorted positions into 16
equal consecutive bins. A bin corresponds to one old level-4 native interval.
Within each bin allocate:

- `n4` positions to that level-4 bag;
- `n2/4` positions to its level-2 ancestor;
- the remaining positions to the new cold storage.

These sizes fit because
`U/16 = n4 + n2/4 + (oldCold + oldRoot)/16`.
The 32-lattice makes each displayed division integral. After removing the old
root level, the level-2 and level-4 bags become levels 1 and 3 in the new trees.
The deeper bags are retained, with their labels shifted by one level. Each new
root is empty. Each child tree has `N/2` registers.

## Bound errors in sorted bins

For a coarse native partition at old level `L <= 4`, count all deep elements
whose values lie outside the coarse interval assigned to their bag. The old
stranger invariant should give

```
E_L <= 64 * mu * delta^(6-L) * cap6 / (1 - 4*delta^2*A^2).
```

Actual deep prefix counts differ from the expected prefix counts by at most
`E_L`. Since each level-6 subtree has the same actual size, the expected upper
prefix boundary is exactly the corresponding fraction of `U`. Sorting the
upper region therefore leaves at most `2*E_L` wrong-interval values in any
selected bin or union of bins contained in a native coarse interval.

With the chosen parameters, `A*delta = 1/12`. For rebuilt old level-4 bags,
the error multiplier is at most `32/35 < 1` times the required stranger bound.
For rebuilt old level-2 bags it is at most `2/315 < 1`. The same estimates,
with an extra power of `delta`, cover higher-order strangers. Deep bags retain
their old bounds. Deep wrong-half counts are zero at the root threshold;
this supplies exact rank separation between the two new trees.

The global deep-error sum, prefix discrepancy, sorted-bin estimate, rebuilt
ownership/cardinality proof, and child rank translation are all checked.

## Final physical wire order

The independent subtrees can occupy noncontiguous wire sets. Their exact final
sorts give a fixed permutation of global ranks, determined by the allocation
and independent of the original input. The checked correction network sorts
that known permutation in at most `log_2 N` rounds: match misplaced ranks across
the two physical halves, then recurse independently in the halves. Each match
compares an inverted pair, so an ordinary comparator performs the required
swap. `exists_known_permutation_correction` formalizes this lemma, and
`correctedForest_sorts` uses it in the final sorting network.

This adds coefficient 1: `989*6.5 + 561 + 1 = 6990.5`.
Terminal exact sorting and startup contribute the checked additive allowance:
`2*depth <= 13981*k + 13979`. Restriction to arbitrary arities and removal of
the additive allowance give the minimum-depth and limsup endpoints.
