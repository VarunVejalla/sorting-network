# UB-28 joint-pattern state: research sketch

Status: unreviewed salvage idea; no probability bound is claimed.

The width-2 example in `UB28-TOP-HEAVY-SCHEDULE.md` rules out a Markov state
consisting only of block counts. The schedule may still admit a bounded-width
joint state for a fixed terminal inversion: its backward dependency cone has
only finitely many blocks at each dyadic scale, even though each block's width
grows.

For a tuple of `k` supported blocks, write the wire-column type at position `t`
as `v_t in {0,1}^k`, and let `H_v` count positions of each type. The candidate
state is the histogram `H=(H_v)`, together with the exact ordered block labels
and finite pairing/edge phase. A fresh uniform cross-matching is equivariant
under a common permutation of all coordinate slots: conjugating each matching
permutation by the common relabeling preserves its uniform law. Thus equal
histograms in the same labeled geometry have the same next-histogram law.
Conditional on `H`, common exchangeability makes the type sequence uniform over
its orbit.

At a physical half split, retain the **joint allocation** of every row type to
the first and second halves. Conditional on parent histogram `H`, these
allocations have the multivariate-hypergeometric law; the pair of child
histograms remains coupled through the shared allocation. This distinguishes
the width-2 counterexample: aligned singleton blocks have histogram `{00,11}`,
while independent singleton blocks have `{01,10}`. Replacing either by two
separate block counts loses the relevant information.

This state is plausible for a fixed, phase-tagged support geometry, but a
complete strong-lumpability proof is still needed for each sequence of matching
layers, splits, and support updates. Erasing block labels/offset phase is
unsafe. The backward cone must also be proved to contain only boundedly many
blocks, including its boundary data and any paired-witness labels. An
independent fresh-context review found no small counterexample to the
phase-tagged joint histogram under fresh uniform matchings and identified
strong lumpability plus joint split allocation as the key formal gate.

If closure holds, the proof program would be:

1. Prove a conditional exchangeability invariant for each cone phase, including
   the exact tail and the deterministic half split.
2. Prove strong lumpability for the exact histogram transition under every
   phase-tagged random matching pass; count the needed random-permutation
   contingency/cycle types and carry the joint split allocation. A simple
   pairwise contingency table may not encode the permutation-cycle effects.
3. Bound the large-`h` transition by a certified method-of-types/entropy
   operator, preserving positivity and uniform finite-width errors.
4. Optimize the rate over every edge phase and boundary class for a schedule
   whose depth coefficient is below 300; require the bad-edge exponent to
   exceed `ln 2` with explicit slack.
5. Sum the subexponential trajectory and edge factors, then use the first
   moment and wire restriction to obtain the all-`n` limsup bound.

The first small-width check now passes: for `k=3`, the script
`ub28-joint-histogram-check.py` enumerates every input pattern at widths 2 and
4, checks both adjacent pair phases under every uniform matching, and compares
the joint half-split law against the multivariate-hypergeometric allocation.
This supports the orbit argument but is not a proof for arbitrary width or a
complete schedule cone. The next closure test should compose the full two-offset
pass and support updates, including boundary cases, with exact kernels. If
that fails, enrich the state or park the route. Even if it passes, the rate
gate remains open: no numerical evidence yet shows that the worst joint-pattern
rate clears `ln 2` for a schedule below coefficient 300. No Lean work should
start before arbitrary-width closure, a rate screen, and independent review.
