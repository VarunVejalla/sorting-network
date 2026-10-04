# Root splitting: proposed completion argument

Status: research design, **not a formal sorting theorem**. The one-tree mixed
stage and repeated comparison run are now kernel checked. The following is the
mathematical argument being developed for the remaining forest transition.

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

Outstanding formal obligations include the global deep-error sum, prefix-count
discrepancy, the sorted-bin estimate, the rebuilt ownership/cardinality proof,
and translation of rank intervals into the two smaller trees.

## Final physical wire order

The independent subtrees can occupy noncontiguous wire sets. Their exact final
sorts give a fixed permutation of global ranks, determined by the allocation
and independent of the original input. A proposed correction network sorts
that known permutation in at most `log_2 N` rounds: match misplaced ranks across
the two physical halves, then recurse independently in the halves. Each match
compares an inverted pair, so an ordinary comparator performs the required
swap. This lemma and its use in the final network still need formal proof.

If successful, this adds coefficient 1: `989*6.5 + 561 + 1 = 6990.5`.
Terminal exact sorting and rounding contribute a bounded additive term, which
must be included in the eventual 7000 statement. No claim about `D(n)` follows
until the forest, termination, correction, and complete accounting are proved.
