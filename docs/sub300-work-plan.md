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
  remains open.

The missing theorem must instantiate these interfaces on one actual
`d2FlowCandidateRun` transition: from the Boolean 64-column profiles in its
source tiles, use the physical core's exact output map, then derive every
column cut and receiver tag from the run's static sender sets and rank ports.
The resulting grouped counts must be exactly the next run's tile profiles,
including clipped final tiles and startup/exceptional roles. State its root
profile hypotheses explicitly; a selected-cut LP that allows independently
chosen local cuts is only a relaxation and cannot verify this identity.

There is a profile-shape mismatch to resolve before composing the current
false-profile provider. `D2FalseClippedTransfer.lean` compares against a
single exact-rank prefix. Ordinary flow children instead receive a two-front
deficit (low-prefix plus high-suffix); the checked witness in
`D2PrefixTwoFrontObstruction.lean` gives child deficits `5, 4` while the
single-prefix reference of total mass `9` gives `9, 0`. The sender's Boolean
false mass has **not** been identified with pre-stage `G`; `G` is a flow
deficit, while the physical provider counts false wires in actual source
tiles. `D2FlowRankBridge.lean` proves only that an *ideal* single-prefix
mass `G` has total positive overrun above the two-front child reserves at
most `G-min(G,low+quota/2)`. Candidate capacities are multiples of 8192,
but a physical core tile is 262144 wires, so there are 32 flow blocks per
core tile. Thus the all-stage gate `4096*G <= 23*capacity` and quota floor
give at most 992 overrun per physical tile, not 31; after the local 448 this
does not fit the 512-per-tile doubling budget.

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
Do not redo this local arithmetic. The missing step is to establish the
profile's hypotheses for every sender in the actual scheduled run, including
startup, top-rise, mid, bottom-descending, and exceptional/ragged roles.

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
