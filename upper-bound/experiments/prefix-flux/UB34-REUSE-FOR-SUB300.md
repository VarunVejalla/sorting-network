# What UB-34 can contribute to the sub-300 route

Status checked 2026-10-28. This is a source crosswalk, not a proof of a new
bound.

## Useful pieces

The `ub-34-fringe-duality` worktree has a more developed all-depth *style* of
global argument than the D2 work here:

* `upper-bound/experiments/sub500-screen/INDUCTION-v6.md` gives a node-by-node
  width induction, explicit sender roles, and a proposed low/high prefix
  sidedness invariant (L4). That is useful design material for stating the
  missing spatial state in D2.
* `upper-bound/experiments/runaware/AKS/Chvatal/StrangerBounds.lean` proves
  `sent_outside_le_of_tail_profile`, which replaces a scalar outsider cap by
  an all-rank-prefix escape profile. This is a reusable abstract interface.
* The same branch's L3 work relates far crossings to distance-graded separator
  tails. The certified tail tooling can potentially price a fixed D2
  separator's far-error component once its threshold event is matched to the
  D2 wire map.

These can help formulate and prove a D2 state that separates local, short
range spill from long-range rank outsiders. They do not supply that state for
D2, nor identify its flow nodes with actual key ranks.

## What does not transfer as a sub-300 result

UB-34 changes the Chvatal R1 separator/accounting route. Its own `SCREEN.md`
prices an idealized route near 490 after corrections; `REVIEW-v7.md` records
that the earlier 477 package omitted a factor-two tail charge and a band-stage
fringe term. The revised package still has unresolved proof/provider items.
Even a completed ~490 result would not meet 300 without combining it with a
cheaper stage and proving a compatible restoration invariant.

UB-40's scalar periodic-restoration screen is not that invariant. In
`UB40-SCALAR-RESTORATION-GATE.md`, the existing fringe-support condition fails
by orders of magnitude between refreshes. The branch's tail-profile lemma
removes the *formal* scalar cap from one send inequality, but its current
separator contract does not yet provide the required all-`j` tail profile on
the actual scheduled D2 states.

## Best sub-300 target and exact gap

The D2 candidate has prefix-stage price `p=273` for `(x,y,z)=(3,3,2)`.
The fixed cleanup argument reaches coefficient 300 if its terminal Boolean
inversion count is at most `N^theta` for `theta < 27/301`; the screened
third-moment exponent near `0.045` would give about 286 if proved uniformly.
The moment screen is oracle-driven and assumes a localized root band, so this
is only a target.

The next theorem must be an all-depth transition for an actual spatial
rank/inversion potential, with (i) startup/root initialization, (ii) the
fixed D2 port map and fresh-error term, and (iii) a terminal bound. UB-34's
L4 sidedness and tail-profile interfaces are candidate ingredients for (i)
and (ii), but must be rederived against D2's concrete routing. The local D2
832-wire band/port bounds alone do not bound global seam concentration.

## Decision

Reuse UB-34's invariant architecture and abstract tail-profile lemma as
references; do not port its R1 cost package into the D2 proof. First test
whether an L4-style signed low/high rank state, together with the checked D2
weighted-port variation bound, yields a closed all-depth D2 transition. If
not, the current 286 screen has no proof path yet.

## D2 cut-accounting refinement (2026-10-29)

The local D2 source has a sharper route to one-sided escape than the pointwise
displacement adapter. `D2RankCutTail.lean` turns displacement `832` into the
profile `min(j, j - pi/2 + 832)`. At the candidate tile capacity
`262144`, the ordinary half-ports are only `480` wires (top-rise: `512`), so
this profile gives no contraction. By contrast, the fixed-core rank-profile
provider has total l1 error `448`; conservation makes leakage in either
direction across any union of destination cells at most `224`. The new
kernel-checked `D2BalancedPrefixProfile.lean` lemma and its routed-profile
adapter in `D2RankProfileRouting.lean` expose this one-sided accounting.
Against the ordinary port margins this leaves at least `256` wires of
contraction per complete tile.

This is a useful local sender estimate, not yet a global transition: the
tile-local ideal rank splits still have to be identified with the actual
scheduled sender's global rank split, and the destination-cell unions must be
shown to be the real address prefixes. The unresolved all-depth schedule to
profile map therefore remains the decisive gap.
