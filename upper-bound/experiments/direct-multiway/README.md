# Direct multiway partitioner

Active structural upper-bound experiment. Goal: design one fixed comparator
network that produces a multiway partition with simultaneous cut and fringe
guarantees, then prove a global schedule that composes those guarantees.

This is separate from `ajtai-multiway/`, whose current row-scramble approach
has a strong aggregate leakage screen but no composable sparse repair. The
row-scramble tail audit is retained in the backlog; its scripts and prior
certificates remain available for comparison.

Start with [the research sequence](RESEARCH-SEQUENCE.md). Keep Lean scratch
outside `upper-bound/best` until a complete local theorem clears the cost
gate.

The checked scalar bag recurrence and the missing information needed for a
genuine weighted transfer kernel are recorded in [the transfer audit](TRANSFER-AUDIT.md).
The explicit stage/scheduler recurrence and C<=500 cost gate are in
[RECURRENCE-BUDGET.md](RECURRENCE-BUDGET.md).

## Profile-stage status

`ProfileStageKernel.lean` now proves the one-stage geometric-profile recurrence,
including the distinct rank-zero update, higher-rank transfer, leaf bags, and
the maximum-rank zero case. `ProfileRealKernel.lean` instantiates that interface
for the actual execution-defined placement: the new profile BadSend argument
handles sibling mass, while the existing fringe theorem still applies because
the profile pointwise implies the old scalar invariant. The resulting
`realProfileOutsiderBound_step` is kernel checked, conditional on the profile
bound at stage `t` and the existing `RealSpecs`.

`ProfileInitial.lean` proves the stage-one profile bound. Its root case sharpens
the initial epsilon estimate to `paperRootEpsB ≤ profileScale · invMu / 64`;
all other nonempty cases vanish by rank. `ProfileInduction.lean` composes that
base case with the real stage theorem, proving the proposed profile at every
scheduled stage, conditional on `RealSpecs`. These scratch results do not yet
improve the final sorting-depth coefficient: the remaining work is to use the
stronger profile in a cheaper global scheduler/construction and reprice its
full depth. The scheduler audit in `PROFILE-SCHEDULER-AUDIT.md` shows that
tightening the profile alone leaves the coefficient at 1419: it must justify a
cheaper separator pack or a different terminal schedule. That note quantifies
the required per-round savings and explains why simply stopping early does not
improve the asymptotic coefficient with the current bitonic leaves.
