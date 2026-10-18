# High-risk gate audit for the tapered 945 candidate

Status: conditional analysis of the current experiment, October 12. This is not a theorem about the sorting network.

## Constants correction

The current candidate constants are defined in `SignedReserve.lean`:

```text
mu = 17/71565312
 delta = 1/2^25
 epsB = 1/2^21
```

The prior version of this note accidentally used legacy Chvatal constants (`1023/2^40`, `1/5.3e9`). Its comparison of the descendant spill against the final residual margin was consequently wrong. The calculation below is redone with the current candidate values.

## Conditional complete-child-subtree spill

At a complete sibling-prefix cut, suppose active ownership is unique, only the required parity levels are populated, and every descendant `z` at distance `r` below child `w` satisfies

```text
strangers_(r+1)(z, regs(z)) <= mu * delta^r * C(z,t),
C(l+1,t)=64*C(l,t).
```

A nonnative key of `w` held at distance `r` below it is an order-`r+1` stranger of that owner. With the parity restriction, only odd `r >= 1` contribute. There are `64^r` such bags, each with capacity `64^r*C(w,t)`, so the normalized spill across at most 64 children of `u` is

```text
4096*mu * sum_{r odd >= 1} (4096*delta)^r.
```

For the current `delta`, `x=4096*delta=1/8192`, and the coefficient is approximately `1.1877e-7`. This exceeds the final residual margin `2.54e-8`, but that does not itself fail the screen: `SignedReserve.siblingFactor` charges this term explicitly before computing the residual margin. The physical rank/cut proof must still deliver the charged sibling bound.

This calculation covers selected descendant subtrees at complete child-prefix cuts. It does not bound ancestor or moving-frontier storage, which must be handled separately.

## Actual high-risk gates

1. **Physical ordinary routing:** build an address-indexed placement whose next register set is covered by the parent-send set and the 64 child-up sets chosen by the integer flows. Existing ownership lemmas establish generic partitions; local flow/count lemmas do not yet connect those partitions to a coherent all-stage placement.
2. **Parent send and fringe rank bounds:** translate the padded/restricted two-round separator's B2 and F2 guarantees into the debt-corrected native-subtree bounds needed at every ordinary bag. Bootstrap rank-window results are local and conditional; the global transition interface is absent.
3. **Recurring frontier transitions:** top advance/retreat, bottom expand/contract, and meeting cases have real mass identities, but no corresponding all-order key/rank transition bounds. These recur and cannot be treated as a finite initialization cost.
4. **Recursive partial-prefix cancellation:** complete-child debt corrections cancel, but a cut inside one child leaves a recursive boundary residual. Prove it is already inside `reserve`; do not charge a fresh absolute debt at each level.

The detailed field matrix is in [`OUTSIDER-TRANSITION-AUDIT.md`](OUTSIDER-TRANSITION-AUDIT.md). The ordinary child-send estimate is conditionally `65536*delta = 1/512` of its target budget under current constants. No global outsider induction or sub-1000 theorem follows yet.