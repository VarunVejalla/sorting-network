# Research sequence: direct multiway partitioning

Status: active construction search; no new theorem or coefficient claimed.
The target is a structural improvement to the current `limsup` bound 1419,
with `<=500` as the current design gate and below 200 as a later stretch goal.
The required symbolic recurrence and stage-depth budget are specified in
[`RECURRENCE-BUDGET.md`](RECURRENCE-BUDGET.md); that budget must close before
large finite-network search begins.

## Why this is the bigger option

The current endpoint spends 2838 binary layers on an ordinary node, three
times per factor-64 growth, giving `3*2838/6 = 1419`. Improving constants in
an isolated halver cannot change that scale much unless its guarantees compose.
The row-scramble route has not produced a usable tail/repair interface. The
active target is therefore a partitioner whose construction itself enforces
the multi-cut structure needed downstream.

## First define the acceptance contract

There are two valid routes; do not mix their promises:

1. **Drop-in node.** Prove the exact existing `NodeSpec` contract (all 65
   bulk cuts, both orientations, every supported fringe rank) for one fixed
   replacement network. This permits reuse of the checked Chvatal scheduler.
   Its node depth must be below 2838 to improve 1419, and below 400 to get
   below 200 with the unchanged three-nodes-per-six-bits schedule.
2. **New multiway schedule.** First state a stage contract containing all
   output cut locations, rank ranges, both orientations, fringe/cohort error,
   and how children/stragglers are assigned. Prove a recurrence from that
   contract before optimizing the stage. Charge every serial partition,
   combining, local-sort, cleanup, and terminal layer. For a simple
   one-stage-per-factor-`p` recurrence the coefficient would be
   `(T+G)/log2(p)`; for a multistage recurrence charge the sum of stage costs
   per log-growth. No `T/log2(p)` depth-only estimate counts as a bound.

The drop-in contract is a diagnostic and a route to moderate improvements.
A genuinely new schedule is the route with more room below 200, but it is not
allowed to hide the repair obligation inside a vague “combine the parts” step.

### Contract-to-invariant table for the drop-in route

The checked sources are `AKS/Chvatal/NodeSpec.lean`, `KernelSetup.lean`,
`RealNets.lean`, `PackSpec2.lean`, and `RealSorter.lean` in `upper-bound/best`.
For an ordinary node, let `a=m*n`, `m=2*f+64*b`, `up=2*f*n`, and
`down=b*n`. The current interface consumes:

| Clause | Exact checked obligation | Why the scheduler consumes it |
|---|---|---|
| Bulk high | At each `p=(f+j*b)*n`, `j=0..64`, count largest-`p` keys in the first `a-p` output cells; bound by `EB=(1/59,000,000)*a/2`. | `BadSendField` bounds worst-key strangers sent from a parent bag. |
| Bulk low | Symmetric count of smallest-`p` keys in output positions `>=p`; same `EB`. | `FringeSendField` and flipped low-key orientation. |
| High fringe | For every `1<=r<=Jmax`, count largest-`r` keys outside the last `up/2=f*n` positions; require `< r/86,000,000`. | `FringeSendField` controls rank-pure delivery of a bag's extreme cohort. |
| Low fringe | For every `1<=r<=Jmax`, count smallest-`r` keys in positions `>=up/2`; same strict bound. | Symmetric cohort control; strict integer slack matters. |

Here `Jmax=floor((128/4095)*(up/2))`. For each applicable node geometry, its
selected network must satisfy all four clauses simultaneously for every
permutation input.
This table makes the drop-in target concrete: a scalar all-cuts leakage rate
or a guarantee for one threshold is insufficient. Ordinary-node dimensions
have `2^42 < m <= 2^43`, `n>=16`, and either `f=0` or even `f>=131040`.
The root uses a separate, additive 6320-layer budget and need not set the
limsup coefficient.

The checked factor-64 scheduler has `3d-21` ordinary nodes over `6d` bits of
growth, so if a replacement keeps this interface and schedule its asymptotic
coefficient is `T/2`. Thus the exact numerical acceptance tests are `T<2838`
for any improvement and `T<400` for below 200. If a new schedule changes the
interface, this table must be replaced by a proved recurrence-specific one.

The drop-in target is extremely strict: its ordinary bulk allowance is about
`8.5e-9` of all wires and its fringe allowance is about `1.2e-8` per extreme
key. The two-round AKS screen allows 45-55% aggregate leakage. So reaching
below 200 by substituting a faster core into the current invariant is not a
credible first bet. The high-upside path has to change the **error potential
and stage together**.

## Main path to below 200: contract a weighted error potential

The existing tree proof already tracks outsiders by rank-distance and bag
size. Instead of requiring one tiny uniform error at every stage, derive a
finite transfer rule for the whole error profile. For a node, let `S_r` be
the number of outsiders at rank-distance `r`; seek bounds of the form

```text
S'_r <= local_error_r + sum_s K[r,s] * S_s.
```

Here `K` is the contamination kernel of one fixed multiway stage, including
the effects of all p-way cuts and both orientations. Choose positive weights
`w_r` and define `Phi = sum_r w_r*S_r`. The compositional target is

```text
sum_r w_r*K[r,s] <= rho*w_s   for every s, with rho < 1,
sum_r w_r*local_error_r <= (1-rho)*Phi_budget.
```

This would replace the current demand for roughly `10^-8` uniform local error
with a profile-sensitive condition. The stage still has to be a single fixed
oblivious comparator network. This is a proposed proof interface, not a
derived inequality yet.

The key practical benefit is modularity: a network search can minimize its
weighted kernel cost while a separate potential calculation verifies
contraction. It also identifies exactly which fringe ranks need very strong
protection and which bulk errors can be tolerated. The older
[`few-hundred tapered-invariant study`](../../backlog/few-hundred-tapered-invariant.md)
shows that merely loosening Chvatal's scalar epsilon plateaus around
600-900; the new opportunity is to optimize a *joint p-way transfer kernel*
and its branching schedule, rather than retune that same scalar model.

There is little headroom in the current scalar proof itself. Using the exact
rational constants in `StageKernel.lean`, and holding `invMu`, `invDelta`,
`siblingFactor`, and `slackCoeff` fixed, inequalities `cond42_scaled` and
`cond45_scaled` allow at most:

| Local error | Current | Maximum from that one inequality | Gain |
|---|---:|---:|---:|
| `invEpsB` | `1/59,000,000` | `1.7674e-8` | `1.043x` |
| `invEpsF` | `1/86,000,000` | `1.2037e-8` | `1.035x` |

These are exact-rational calculations displayed in decimal, with the other
constants frozen; additional parameter constraints can only reduce the
available range. So the bigger path must change the potential/flow algebra,
not just increase the two epsilon constants in `StageKernel`.

## Construction hypothesis

Search for a **jointly designed multicut network**: several fixed layers of
disjoint comparator matchings, organized by an explicit expander or
multicommodity routing structure, followed by local block sorting only where
the invariant permits it. The same layers must control all cut/rank/orientation
requirements at once. A collection of separately good one-cut networks is
not enough, and an arbitrary permutation between layers is not a comparator
operation.

The first target is not a full sorter. It is one finite p-way stage with:

* output blocks assigned to the intended child regions (internal order is
  handled by the proved recurrence, not silently assumed);
* a simultaneous bound at every block boundary for every 0-1 rank;
* a separate extreme-cohort/fringe bound strong enough for the chosen
  composition invariant;
* an explicit binary comparator depth `T`, including every local sorter.

For a drop-in candidate, the exact acceptance criterion is `NodeSpec`, not a
generic relative leakage estimate. For a new schedule, derive the minimum
contract from its invariant before selecting numerical tolerances.

## Work gates

### Gate A: derive the interface and recurrence

Read the current `NodeSpec`, `PackSpec`, and the tree scheduler together.
Produce a compact table mapping each invariant clause to the local cut/rank
that must be established by the new stage. For a new schedule, prove the
symbolic recurrence and identify the precise finite error budgets it consumes.
Do not construct gadgets until those obligations are explicit.

### Gate B: search the right finite object

Search over *joint layer schedules*, not exact sorters on the full node. The
candidate should be a small structured family (expander-derived matchings,
coarse-to-fine routing, or a multiway analogue of the current node), with one
objective equal to the worst normalized violation over all required cuts,
ranks, and orientations. Exhaustive finite sorter tools are useful only for
local compaction/merge gadgets whose replication and global proof are stated.
For each candidate, save the network and a machine-checkable certificate of
the complete local 0-1 contract; sampled profiles are discovery data only.

### Gate C: price the whole node

Compute `T` including partition layers, combining layers, local exact sorts,
and fringe repair. Under the current scheduler:

| Goal | Maximum ordinary-node depth |
|---|---:|
| Improve 1419 | `< 2838` |
| Reach below 200 | `< 400` |

For a new schedule, replace these gates by the coefficient from its proved
recurrence, including every serial stage and the terminal network. If no
candidate has a plausible complete cost at the gate, change the construction
family rather than formalizing the partial stage.

### Gate D: prove and formalize modularly

First prove the finite 0-1 partition theorem and exact depth for one parameter
tuple. Then prove a standalone composition/scheduler theorem parameterized by
that contract. Only after their numerical composition beats 1419 should the
work be promoted toward the best package. Keep the local stage, cut theorem,
fringe theorem, and global recurrence in separate modules.

## Immediate deliverable

The contract-to-invariant table for the current scheduler is now recorded
above. Scratch work is deriving profile-sensitive sibling bounds and the
higher-rank transfer; see `ProfileKeysBelowChild.lean`,
`ProfileBadSendField.lean`, and `ProfileStageKernel.lean`. These are experiment
files, not promoted theorems. The immediate missing piece is the rank-1
ordered-window transfer: parent outsiders can shift every cut, so disjoint
child output sets do not justify charging their mass only once. The
one-sided-outsider example and the corrected coefficient screen are recorded
in [`TRANSFER-AUDIT.md`](TRANSFER-AUDIT.md) and tracked as
[UB-11](../../backlog/high-upside-architecture.md#ub-11--price-cumulative-boundary-displacement-in-the-profile-scheduler).
Prove the aggregate boundary-displacement inequality with explicit fringe
terms, then use the child-defect vector and left/right outsider split to
recompute the full rank-1 column. Only after that should the profile kernel,
fresh-error vector, and terminal-purity condition be closed together. Reprice
the complete recurrence against the 500 gate before searching finite
networks; the old-scheduler 400-layer test remains a separate below-200
stretch gate.

## Parked branch

The existing AKS two-round row-scramble aggregate-leakage certificates and
the attempted exceptional-column tail/repair argument are retained under
`upper-bound/experiments/ajtai-multiway/`. The tail argument's rank-inflation
barrier is summarized in
[`upper-bound/backlog/ajtai-row-scramble-tail.md`](../../backlog/ajtai-row-scramble-tail.md).
This branch can be revisited if a uniform discrepancy theorem or a genuine
oblivious sparse repair becomes available; it is not the active construction
search.
