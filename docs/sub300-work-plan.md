# Sub-300 work plan

## Objective

Prove

```text
limsup D(n) / log₂(n) < 300,
```

where `D(n)` is the minimum depth of a binary-comparator sorting network.
The accepted repository bound is still 789.75. The D2 route below is a
research candidate, not an established improvement.

## Start here

1. Read [`AGENTS.md`](../AGENTS.md) and [`docs/research-index.md`](research-index.md)
   for repository rules and current project context.
2. Read the [prefix-flux README](../upper-bound/experiments/prefix-flux/README.md)
   for the source map, then its [current handoff](../upper-bound/experiments/prefix-flux/HANDOFF.md)
   for the mathematical status and next gate.
3. Treat `STATUS-HISTORY.md` and `docs/sub300-search.md` as historical search
   logs; prefer the handoff and current gate notes when they disagree.
4. For a compact goal to reuse after context resets, see
   [`sub300-goal.md`](sub300-goal.md) and its [agent guide](sub300-agent-guide.md).

## Research priority

The candidate is a `(3,3,2)` D2 schedule with a reflected physical sorting
core. Its fixed-core depth and local Boolean error bounds are promising, but
they do not yet prove a global sorting bound. The highest-risk missing piece is
an exact arbitrary-root profile transition through the actual schedule,
including partial tiles and receiver tags. First specify that transition and
test whether its state closes for all stages. It must support an all-depth
invariant and a distance-sensitive terminal cleanup bound. If this gate fails,
record the obstruction and reassess the route before extending many stage
specific Lean bridges.

Within that gate, compose the physical output-slot profile with the canonical
`orderEmbOfFin` placement of each complete sender-rank tile and its receiver
tags. The existing 14,985 seam bound compares slot position to the rank of the
value in that slot; it is not a direct cost to the output-slot 448 profile
transfer and should not be added to its recurrence. Resolve the actual
stage-level count identity, including the partial-tile/startup cases, before
extending the abstract invariant bridge.

### Exact transition gate

Several local parts are already formalized; do not rebuild them without a
specific gap:

- The reflected fixed core has depth at most 276. Its Boolean height map and
  the 448-per-tile clipped profile transfer are in
  `D2ReflectedPhysicalPack.lean` and `D2PhysicalFlowProfileTransfer.lean`.
- The abstract flow gives exact sender rank ports in
  `D2FlowRankBridge.lean`; conditional 4096-grid cuts and whole-cell routing
  are in `D2VariableTilePhysicalFlowTransfer.lean` and
  `D2StaticWireSets.lean`.
- `D2AffineCoreAllStages.lean` proves the abstract flow invariant for all
  stages. `D2AllStageInvariant.lean` separately lifts a physical sender-input
  provider to all stages; identifying that provider with the actual schedule
  remains open. `D2AllStageTwoFrontGate.lean` also proves that every active
  ordinary abstract sender has zero aggregate ideal-prefix overrun, giving a
  pointwise bound of each exact-prefix child mass by its two-front reserve.
  This does not identify the flow deficit with physical false mass.

The physical sender recurrence already has a concrete Python source model:
`flow_dag.py` computes ordered static intervals for each bag, while
`wire_partition_check.py` checks each next bag as the union of its retained
inactive bag, parent down-port, and active child up-ports. `receiver_fiber_types.py`
also handles the parent-root overwrite context. These are finite model checks,
not all-depth theorems. `D2PhysicalBagState.lean` now defines the node bag as
its occupied native interval minus child holes and proves its ordered-run
representation under `StaticHolesFit`. It also proves that `d2FlowTreeInv`
alone cannot supply the fit (an arbitrary invariant-tree counterexample, not
a reachable-run obstruction). The initial fit base case is closed by
`d2FlowTreeStaticFits`, `d2FlowTreeFull_static_fits`, and
`d2FlowTreeInitial_static_fits`. `D2PhysicalBagState.lean` now also proves
`d2FlowStage_regular_child_root_data`, identifying each active ordinary
post-stage child's root tuple with its cut tuple, and
`d2FlowStage_active_ordinary_static_fit`, proving that those post-stage holes
fit between the updated parent fronts. The latter derives the subtraction
identity from the quota and balance clauses in the endpoint-reserve contract.
This is only the active ordinary node case; inactive and exceptional roles
and recursive whole-tree preservation remain. Then prove the one-stage
routed-piece equality and disjointness for every receiver. Only then
bridge the concrete sender sets to `d2FlowCandidateRun` and identify Boolean
64-column profiles using the physical core's output map. Include clipped final tiles and
startup/exceptional roles in the full transition. State root-profile
hypotheses explicitly; a selected-cut LP that allows independently chosen
local cuts is only a relaxation and cannot verify this identity.

Exact equality between the single-prefix profile used by
`D2FalseClippedTransfer.lean` and the ordinary flow's two-front child
deficits is false: the checked witness in `D2PrefixTwoFrontObstruction.lean`
gives child deficits `5, 4`, versus single-prefix masses `9, 0`. This exact
profile mismatch is no longer the immediate analytic blocker. The all-stage
affine reserve in `D2AllStageTwoFrontGate.lean` proves each ideal exact-prefix
child mass is at most its corresponding two-front reserve. Its theorem
`d2FlowCandidateRun_active_ordinary_mass_overrun_le_transfer_atPath` further
shows that if the actual eight grouped counts are within aggregate L1 error
`E` of those ideal masses, their total positive overrun above the next
two-front reserves is at most `E`.

`D2PhysicalTwoFrontGate.lean` composes this with the checked physical
false-profile transfer: for full-height source tiles, parent tile-mass
discrepancy `P` plus the `448*tiles` fresh core error bounds actual overrun,
provided the grouped actual/ideal counts are identified and the ideal groups
are bounded by the sender's flow rank intervals. This is an explicit
conditional transition interface for arbitrary positive port counts. For an
ordinary sender, use ten ordered ports, tagging the two parent ends as a
separate destination and the eight child pieces individually; the all-tag
transfer error then bounds child error as well. This is not yet the actual
schedule transition. The physical child intervals start after the left
parent port, so their ideal mass is naturally measured on right-shifted rank
intervals. `D2FlowRankBridge.lean` now proves that such a shift only decreases
initial-prefix mass, giving the required unshifted reserve comparison. The
remaining ideal-profile obligation is to derive the shifted interval counts
from the actual tile-to-sender rank allocation. The local row-major step is
now checked in `D2ClippedFlowProfileTransfer.lean`: per full-height tile, the
exact-rank counts across all columns of one port sum to the prefix mass in its
clipped flattened interval. `D2ClippedTilePrefixAllocation.lean` and
`D2ClippedTilePortAggregation.lean` now prove that, when tile masses are the
restrictions of one global ideal prefix, all tile/column counts for a port sum
to its shifted global interval. `clippedFlowGroupedRank_eq_shifted_child_interval`
packages this under the condition that each child tag selects exactly one
port uniformly across tiles and columns. Next prove the actual receiver-tag/
port and boundary alignment from static sender sets; this does not yet
identify physical Boolean profiles with the ideal prefix model.

The all-stage flow-side port-grid premise is now discharged by
`D2AllStagePortGrid.lean`: every active ordinary sender has 4096-aligned
ten-port boundaries for every stage and `d >= 7`; it now also projects the
all-stage sender-input contract and port-grid facts to any path. `D2CutAlignment.lean` projects
endpoint alignment to active ordinary candidate paths. `D2PhysicalBagState.lean`
defines the local bag/run state, but the candidate-snapshot fit and routed
next-bag identity remain open. Do not add more path projections before those
identities are established. The static-hole fit
lemma in `D2StaticWireSets.lean` now derives geometric fit directly from the
actual deficit/quota limits and endpoint reserves, without assuming that the
time-dependent schedule capacity equals the native tree capacity.
`D2AlignedPortReceiverCells.lean` proves that an aligned child-port fragment
is a whole 4096-wire cell inside that child's static destination set. Next
compose these results into one path-level static-hole/grid theorem and connect
each clipped tile/column profile count to those routed cells.

The physical sender's Boolean false mass and tags are still **not** identified
with the flow deficit `G` and the rank intervals. The remaining ordinary
gate is to prove the grouped-count identification, ideal interval domination,
and parent tile-mass discrepancy invariant from actual static sender sets.
The theorem currently covers full-height tiles; ragged tiles and exceptional
roles need separate adapters. The older tolerant gate
`4096*G <= 23*capacity` alone gives up to 992 ideal overrun per 262144-wire
core tile (32 flow blocks), so it cannot pay for the local 448 transfer error
within the 512-per-tile doubling budget. The stronger affine reserve removes
that ideal overrun, but applying the new one-sided interface still requires
proving that the actual schedule supplies its hypotheses. Ragged tiles,
startup, and exceptional roles also remain open.

`D2TolerantOverrunScaleObstruction.lean` gives an exact local witness at
capacity 1048576 (four core tiles): it satisfies the tolerant stage-input
predicate, yet its first-child ideal-prefix overrun is 3968 = 992 per tile.
This refutes deriving the target recurrence from that local predicate alone;
it is not a reachable-run counterexample. The stronger reserve `8192*G <=
15*capacity` makes the overrun zero, because half the candidate quota is at
least `15/8192` of capacity. The implication is kernel-checked in
`D2CandidateTwoFrontBridge.lean`. The strict `1/512` reserve gives at most
32 overrun per physical tile, so local cost 480 fits the 512-per-tile budget.

The sharp local recurrence is already kernel-checked in
`D2StrongDeficitPropagation.lean`. Its affine profile is the disjunction
`G = 0 ∧ 256*pi ≤ c`, or
`8192*G + 7 ≤ 15*c ∧ 4096*pi ≤ 15*c`. The file proves this profile propagates
through an ordinary eight-child update at capacity `2*c`, implies the existing
`512*G ≤ capacity` and quota gates, and handles the seven-unit integer slack.
Do not redo this local arithmetic. The all-stage abstract flow provider now
establishes its hypotheses throughout the candidate run, and
`D2AllStageTwoFrontGate.lean` closes the resulting ideal overrun gate. The
missing step is to link actual sender masses, cuts, and tags to those flow
states, including startup, top-rise, mid, bottom-descending, and
exceptional/ragged roles.

The exact compressed-flow screen
`d2_deficit_tolerance_screen.py --depth 100 --scale 8192 --params 3 3 2`
checks 217470 reachable stage/node entries, passes the strict `1/512` gate,
and observes maximum ratio `15/8192 - 7/capacity`. This is finite model
evidence only.

The abstract all-time full-tree core-provider induction is now proved in
`D2AffineCoreAllStages.lean`, combining the checked bootstrap with the
full-tree one-step transition. Do not reassemble that induction. The immediate
formal gate is the physical sender mass/tag identity for the actual schedule,
including partial tiles and startup/exceptional roles. The sources
`D2StrongFlowCoreInputs.lean`, `D2StrongAffineChild.lean`,
`D2TopDescHistory.lean`, and `D2CoreProviderReserveStep.lean` already provide
the contract adapters, ordinary-child profile transition, role-specific root
profiles, and two-visit endpoint reserve transition used by the checked
all-stage theorem. `D2RootFrontierCase.lean` proves that an active
level-zero node is top-descending and its deficit is zero under the prior-core
hypothesis. Bootstrap snapshots 0 through 3 are checked by
`D2AffineCoreBootstrap.lean`; their composition into an all-stage theorem is
also checked. Do not redo these local lemmas.

Passing that flow-reserve gate does not establish the physical stage
transition. The central construction gate remains the joint state linking
Boolean tile masses to flow ideal profiles and the actual receiver group/tag
identity, including ragged heights. Then prove an all-depth spatial or
distance-sensitive terminal bound, fixed cleanup, and complete depth
accounting. Neither finite stage screens nor local witnesses settle the fixed
sorting algorithm.

Treat the gate as passed only when that identity is proved for arbitrary legal
root profiles and all stages, and the induced transition admits an
all-depth spatial/distance bound strong enough for terminal cleanup. The
`512`-per-tile aggregate recurrence alone does not pass: it controls total
count error but does not imply terminal purity. Existing LP witnesses refute
some proposed scalar potentials under relaxed constraints, not the concrete
fixed network. Avoid further scalar-potential sweeps unless the exact state or
constraints have materially changed.

There is a separate possible terminal route in
[`D2-MARGIN-TAIL-TRANSFER.md`](../upper-bound/experiments/prefix-flux/D2-MARGIN-TAIL-TRANSFER.md):
prove bounded rank displacement per actual stage, compose over `O(log n)`
stages, then use its block-and-seam cleanup (asymptotically free). Its
construction-specific crossing contract is also open; do not treat the local
52-row variance bound as that contract.

Keep the proof obligations separate and explicit:

1. Exact global stage/profile transition for the real schedule.
2. Inductive sender-input invariant, including startup and ragged cases.
3. Terminal distance/error bound and a fixed cleanup network.
4. Arbitrary-size padding/restriction and complete depth accounting below 300.
5. Kernel-checked Lean theorem with the repository's contribution checks.

The handoff has current file-level evidence and open details. Do not treat the
conditional local price `230`, finite stage audits, oracle traces, relaxed LPs,
or aggregate error alone as the desired limsup theorem.

## Working rules

- Work only in `.claude/worktrees/sub300` on `sub300-structural`; do not edit the
  main checkout or another worker's worktree. Do not push or promote without
  explicit instruction.
- Before a significant new proof or experiment, state its exact claim, inputs,
  quantifiers, and what outcome would pass or reject the gate. Prefer small,
  decisive structural tests over broad exploratory sweeps.
- Resume by reading the current
  [prefix-flux handoff](../upper-bound/experiments/prefix-flux/HANDOFF.md),
  then inspect only the source files named for the current gate. Keep the
  handoff and experiment index aligned when the recommended next step changes.
- Keep claims labeled as conjecture, simulation/model, hand argument, or
  kernel-checked. A Lean file or finite audit does not by itself establish the
  global recurrence.
- For Lean work, keep scratch modules in the experiment area, use focused
  checks, inspect only relevant errors, and do not introduce `sorry`, axioms,
  `native_decide`, or trust extensions. Follow `AGENTS.md` for final proof and
  contribution checks.
- Commit coherent milestones and handoffs. Keep generated build products and
  run logs out of Git; use the ignored cache and manifest described in the
  prefix-flux README. Keep scripts and source inputs needed to reproduce a
  result with their experiment.
- Update `HANDOFF.md`, `upper-bound/experiments/INDEX.md`, and the relevant
  experiment index when a result changes the recommended route. Mark
  superseded outputs clearly. Avoid duplicating long chronological notes.
- At each checkpoint, report the best supported coefficient, claim level, the
  exact gate closed or failed, what was checked, remaining blockers, and the
  next smallest decisive step. Do not claim success until the complete
  all-input-size theorem is kernel-checked and accepted by the repository's
  contribution workflow.
