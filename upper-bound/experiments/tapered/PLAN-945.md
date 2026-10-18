# Tapered-flow route to a sub-1000 sorting bound

Status: research ledger, not a theorem. The current candidate arithmetic suggests
a coefficient of `945` for `limsup D(n)/log₂ n` if the integer schedule,
separator invariant, and global recursive construction all close. The earlier
`945.006` figure included a terminal-profile surcharge from a flow model that
has since been replaced. Neither number is currently a proved sorting bound.
For the parameter screen and equations, see [`SUB1000-CANDIDATE.md`](SUB1000-CANDIDATE.md).

## October 14 rank checkpoint

UB-23 closes the initialized count/ownership schedule; see
[its endpoint](UB-23-FLOW-FAMILY.md). UB-24 now proves the actual-execution
clipped threshold recurrence and its shared endpoint corrections. Retirement
also requires exact native subtree totals, which the present local rounding
contract does not force. Cumulative rounding now yields an exact-complement
top-advance split when the coordinated stored-subtree masses and source total
are supplied; proving that global laminar mass invariant and the signed rank
invariant remains open. See
[the current UB-24 proof map](UB-24-RANK-PROFILE.md). No 945 theorem is claimed.

The October 13 descriptions below are historical. In particular, the old
ordinary-only global flow wrapper and bootstrap reset are superseded, and
the provider's half-port/support gaps remain the UB-22 obligations.

## October 13 checkpoint (historical)

The local small-bag scale gap is now closed for the width-16 branch.
`CyclicSmall16PaddedWitness.lean` proves that every live size
`2^34 <= a < 2^38` has a padded two-round witness of depth at most 1890,
with both cut directions and both restricted fringe estimates. Its tuned
`f=16000` low fringe fits from the minimum `2^34` reference capacity.
`TaperedOrdinaryKernel.lean` now takes the provider's multiplicative fringe
coefficient as a field; the tuned coefficient `1/9,000,000` satisfies the
recursive scalar inequality. These were focused direct Lean checks, not a
package build.

`AdaptivePaddedWitness.lean` now gives one size-adaptive separator contract:
the tuned width-16 provider below `2^38` and the standard provider above it,
with a uniform `1/9,000,000` rare-rank coefficient. `GlobalFlowStep.lean`
proves that the actual-cardinality interior transition and frontier count
estimates within 69 wires combine into one coherent next-stage flow table.
Its exact remaining frontier premise is the actual routed count discrepancy
for both moving-frontier families at every stage. This remains conditional,
not a global schedule.

`FrontierInteger.lean` now rounds the upper-frontier retreat into an even
up-port and 64 child blocks, assuming the actual count matches the proposed
frontier mass within 69. Together with the existing top-advance rounding,
this closes two local frontier split rules; it does not derive their mass
identities from the routed wire partition.

Next, prove actual suffix/prefix fit and cohort range at every scheduled
address, and instantiate `badSend0`/`fringeSend`. Then prove the 69-wire
frontier count estimates and propagate the all-order outsider invariant on
the same routed partitions. Root/bootstrap and terminal cases, recursive
sorting/depth, and endpoint/axiom audits remain after those gates.
There is still no complete 945 or sub-1000 sorting theorem; 1419 remains the
best verified global endpoint.

## Proof map and status

### Current checkpoint: local gates closed, global theorem still open

This checkpoint supersedes the older task descriptions below where they say
the output bridge or smaller-row bulk existence is missing.

| Component | Current evidence | Remaining obligation |
|---|---|---|
| Actual output counting | `SlotOutputBridge`, `SeparatorKeyBridge`, `BootstrapSeparatorOutput`, and `BootstrapStageOneProvider` pass focused Lean checks. The exact bootstrap rectangle has a compatible two-orientation B2 pair; the actual stage-one child register is enumerated injectively; its separator output error fits `μ·4·seedRootDown`, the next reference-capacity allowance, under the root `NodeSpec`. | Handle endpoint slots and install these output sets in the next-stage ownership partition; prove the later-stage input invariant. |
| Smaller-row bulk construction | `CandidateBulkWitness`, `CandidateBulkFail`, and `CandidateBulkProvider` pass focused checks. There are actual two-round B2 witnesses in both orientations for rows at least `2^34`, columns at least 16. | Feed the actual cut and rare-rank interfaces into the recursive outsider induction. |
| Arbitrary live sizes | `AnyCutBounds`, `RectanglePadding`, `PrefixPadding`, and `PaddedSeparator` pass. `BaselineFringe` proves a multiplicative rare-rank guarantee after restriction, conditional on truncated F2 witnesses. | Prove the selected suffix contains `f+1` protected rows at every scheduled bag, then use it in the global induction. |
| Wire ownership/execution | `RaggedWireOwnership`, `RaggedExecution`, `RaggedRouteCard`, `RaggedTreeRoute`, and `RaggedTreeFlowBridge` pass focused checks. Unequal wire slices route as a genuine partition; for every ordinary interior address, the tree map's exhaustive source classification and set identity show it receives exactly its selected parent slot and 64 child up-ports. The transition builds a coherent split family from current active flows and chooses one actual-cardinality next-flow witness per address generated by an ordinary interior parent. `candidate_next_active_interior_or_frontier` proves every next scheduled address is interior-generated or lies on an endpoint that moves by exactly one level. | Supply the lower/upper frontier transitions, join their flows with the interior table, and prove the global rank/debt invariant. Root and terminal rules remain separate. |
| Exceptional frontier mass | `FrontierDebtFlow`, `FrontierPositivity`, `FrontierInteger`, and `SubtreeMass` pass: static-debt conservation/positivity, integerizable top advance and top retreat, and exact complete-subtree cancellation. | Integerize bottom expansion/contraction; derive all frontier mass identities from actual routing; derive rank bounds for partial cuts and prove the meeting rule. |
| Price and termination | `WireRoundingBudget` checks a conservative scalar allowance; `Fallback999` checks a conditional 999 scalar price. `TaperedTerminal` proves a conditional parent-group finishing sorter of additive depth 903 from order-two purity. | Charge actual frontier/invariant terms and prove the complete eventual depth recurrence. Neither 945 nor 999 is a sorting theorem. |

The critical remaining mathematical gates are:

1. **Compatible fringe witnesses:** prove actual failure fractions for the
   truncated scrambles and combine them with the full-row bulk pair. This is
   now proved in `TruncatedScrambleMeasure` and `TruncatedFringeProvider`.
   `TruncatedPaddedProvider` packages a real padded pack of depth ≤1890 whose
   same scrambles satisfy B2 in both orientations and the truncated SR/R1/R2n
   contracts in both orientations. `TruncatedPaddedWitness.fHigh_baseline`
   transfers the high-side rare-rank estimate to a restricted live bag,
   conditional on its actual fringe suffix size and cohort range. The
   low-side transfer is not yet formalized: it must turn flipped semantic F2
   into a physical low-tail count and then restrict to the live prefix.
2. **Frontier rank cancellation:** instantiate `SubtreeMass` at actual key
   sets. Complete subtrees cancel exactly; `FrontierPrefixMass` carries that
   identity across any prefix of whole child subtrees, and
   `FrontierRankCounting` gives the three-way counting bridge. Cuts through a
   child still need the recursive outsider budget and an actual instantiation.
3. **Global induction and integerization:** assemble seed, interior, and
   frontier rules into one recursive allocation; prove all-order outsider
   bounds for its actual execution.
4. **Terminal sorting and endpoint:** order-two purity suffices to sort
   parent groups at termination; then price the complete network, prove an
   eventual depth bound, and audit headline axioms.

The best verified global endpoint remains **1419**. All work here stays in
the experiment; promotion requires the user's review.

Additional gates checked in this work session: `FrontierRankCounting` passes
as a generic disjoint-storage/three-way cover lemma; `FrontierPrefixMass`
passes for every prefix of whole child subtrees; `BaselineFringe` passes with
explicit truncated F2 hypotheses; `TruncatedScrambleMeasure` preserves exact
failure fractions under one-row truncation; `TruncatedFringeProvider` proves
simultaneous bulk/fringe scramble existence; `TruncatedPaddedProvider` packages
the actual same-pair padded separator and its conditional high-fringe estimate;
and `TaperedTerminal` passes with the recursive order-two purity hypothesis.
See the modules for exact statements.

The separator's remaining interface gates are now explicit: prove each
scheduled suffix fits the high fringe condition
`(f+1)*columns ≤ u + padding`, keep its cohort within `jmax`, and establish
the corresponding low-side live-prefix fringe estimate. These are downstream
of the global integer scheduler; none follows from the padded witness's
existence alone.

The stage-one transition has now been composed one step further in
`BootstrapStageOneProvider`: exact-dimension scrambles are supplied by the
truncated-fringe/bulk existence result, each actual stage-one child register
is enumerated from its finite wire set, and its post-separator slot error is
bounded by `μ·4·seedRootDown`. This remains conditional on the root `NodeSpec`
and does not by itself define the next global wire partition.

`RaggedRouteCard.routeRaggedWires_card_eq_port_sum` gives the exact size of
any routed address bag as the sum of all source ports assigned to it.
`RaggedRouteCard.routeRaggedWires_card_eq_port_sum` gives the exact size of any
routed address bag as the sum of all source ports assigned to it.
`RaggedTreeRoute` defines a total tree destination map, classifies every
incoming source for an ordinary interior address, proves the exact routed-set
decomposition, and derives the physical cardinality recurrence.
`RaggedTreeFlowBridge` realizes local integer flows as actual wire splits and
proves `actual_routedChildCount_eq`: when the parent and grandchild splits
match their integer-flow ports and counts are actual register cardinalities,
the ordinary recurrence equals the cardinality of the actual routed register.
Thus the ordinary interior cardinality gate is closed locally. The ordinary
split family is now determined from any supplied active actual-cardinality
flow table. The global scheduler must still establish and iterate that flow
table, and root, moving-frontier, and terminal routing/count rules remain open.

### October 12: ordinary interior routing recurrence

`RaggedTreeRoute.lean` and `RaggedTreeFlowBridge.lean` now close the ordinary
interior one-step accounting gate. For a non-root, non-terminal bag, the canonical
parent/child destination map has an exhaustive incoming-port classification;
the actual routed set is exactly the selected parent block union the up-ports
of the 64 children. Pairwise disjointness then gives its exact cardinality.
`actual_routedChildCount_eq` composes that physical equation with the existing
integer recurrence, conditional on the current split matching the local flow
table. `candidate_interior_actual_child_flow_exists` composes the existing
≤69 rounding result with this equality and transports the witness to the
actual next-register cardinality. `candidate_interior_actual_step` removes
the need to supply the split family manually: active flows determine all
active splits, while a valid fallback handles inactive registers.
`candidate_interior_actual_flow_nonempty` and
`chooseCandidateInteriorActualFlows` package one next flow per address in the
ordinary interior-child domain, indexed by actual register sizes.
`candidate_next_active_interior_or_frontier` shows this domain misses only
addresses on a frontier that moves at this step, and proves the corresponding
endpoint moved exactly one level. The two frontier flow transitions and their
rank/debt transfers remain separate. Focused Lean checks passed for
`RaggedIntegerSchedule`, `RaggedRouteCard`, `RaggedTreeRoute`,
`RaggedTreeFlowBridge`, and `BootstrapStageOneProvider`. `#print axioms` on the
two new transition theorems reports only `propext`, `Classical.choice`, and
`Quot.sound`.

| Module | Checked result / status | What remains | Dependency / gate |
|---|---|---|---|
| **A. Variable-width window algebra** | `VariableSlots.lean` and `VariableWindow.lean`: unequal child widths; separate left/right rank tails; per-slot transfer from native mass plus outsider budget; signed endpoint/interior reserve estimates. | Instantiate the cumulative native-slot bounds and outsider budgets from the actual schedule. | Needs the schedule-specific invariant in D; this is an interface, not a separator theorem by itself. |
| **B. Signed flow and integer rounding** | `SignedReserve.lean`, `AddressDebt.lean`, `IntegerRounding.lean`: candidate signed-debt bounds and uniform real occupancy identity; a one-step even natural up-flow and 64 child blocks with exact total under explicit hypotheses. At `C ≥ 2^34`, `|η| ≤ 69`, and the candidate split equation, adjusted targets are positive and the next discrepancy is below 69. | Prove all premises for every active bag, including exceptional levels; choose a globally coherent witness rather than a fresh unrelated witness per local application. | Depends on the globally defined scheduler in C. Local integerizability is not global realizability. |
| **C. Frontier and seed arithmetic** | `CandidateFrontier.lean`: active-window ordering, successor closure, and one-level frontier motion. `CandidateSeed.lean`: exact seed counts/placements through stage 2 and a bootstrap table through stage 3; root, level-one, and both stage-two sender types have `NodeGood` providers. `RaggedBootstrapGeometry.lean` gives the exact address-dependent stage-one row profile and average `NodeGeom`; `RaggedResetGeometry.lean` gives all four stage-two sender geometries with common down-flow. | Connect the ragged row profiles and local-network providers to the actual address-indexed placement. Extend the flow table beyond the finite reset, with coherent moving-frontier and terminal rules. | Geometry and count conservation are checked, but do not construct a placement with ragged child blocks or determine their ranks. |
| **D. Global address-indexed integer scheduler** | `RaggedIntegerSchedule.lean`: ordinary interior active successors remain scheduled; given current local flows, routed discrepancy is ≤69 and a next local flow exists. `RaggedBootstrapFlow.lean` packages the stage-one ragged profile. `RaggedResetFlow.lean` packages the root's zero-fringe stage-two profile and proves exact stage-three top/bottom counts. | Replace the separate finite row/count tables and conditional interior step with one coherent address-indexed placement/scheduler. Prove exact wire ownership, nonnegativity, capacities, address coverage/no duplication, and root/frontier/terminal rules. | These local tables are not a `FlowSizes` replacement or a global scheduler; the standard type has one down-count per level/time and cannot express the varying widths. |
| **E. Two-sided outsider induction (main mathematical gate)** | `VariableSeparator.lean` proves two-sided B2 estimates at arbitrary row-aligned ragged cuts; `RaggedFlowContract.lean` packages the profile and both fringes. `AddressDebt.lean` proves signed cumulative-width budgets and a local bootstrap integerizer. `RaggedStageOneRank.lean` proves actual stage-one input tails. `StageOneWindowGate.lean` proves the exact population split and `candidate_bootstrap_stage_one_wrong_rank_bound`, composing those tails with the signed window theorem. | Connect the input wrong-rank count to the ragged separator's actual output using its two boundary crossing bounds. Extend this into later stages and a coherent scheduler. | The input-tail, population, and joint rank-window gates are kernel checked, conditional on the root `NodeSpec`. The placement-to-rank/output interface remains open; the variable-width profile is not installed in a global scheduler. No stage-one-to-stage-two outsider transition or global bound follows yet. |
| **F. Root, moving frontiers, and terminal bags** | Exact root-to-stage-2 counts and local sender networks are checked. Stage 2→3 conservation and capacity matching are checked. The raw input root exceeds the ordinary ≤69 discrepancy range (`candidate_raw_root_exceeds_interior_target`). | Prove the root and frontier rank invariant, continue local network/flow availability through later frontier shifts, and set a valid stopping condition whose bags can be sorted within the charged depth. Bound exceptional work on every path. | Root geometry alone is not the outsider base case. Stage-3 capacity matching is count-only; it does not imply stage-3 sender geometry or terminal sorting. |
| **G. Recursive sorting network and depth recurrence** | Existing components provide local networks, depth facts, and the two-round separator interface, but the tapered candidate is not yet a complete recursive sorter. | Assemble the finite recursive network; prove it sorts every input, handles all arities (including padding/restriction), terminates, and bounds maximum path depth including roots, frontiers, and terminal sorters. | Requires E and F. Correctness and maximum-path depth must be proved together with the actual variable bag sizes. |
| **H. Constant and asymptotic endpoint** | Current candidate price is 3 stages at 1890 layers per six input bits, i.e. 945 layers per `log₂ n` bit for ordinary stages, subject to the candidate's exact parameters. This is a conditional leading-cost calculation. | Recompute the complete recurrence from G, including finite/root/terminal overhead and ceilings; prove an eventual bound `D(n) ≤ c log₂ n + b` with `c < 1000` (target 945 if the ledger survives); derive the limsup theorem. | Only follows from G. Do not infer the endpoint from the local stage price. |
| **I. Package verification / possible promotion** | Focused direct Lean checks with Lean `v4.29.0-rc4` passed for the arithmetic, seed, separator/window, ragged-flow/geometry, and conditional rank-interface modules in dependency order. | Once H exists, run the tapered package build and its axiom audit; then review dependencies and only afterward consider porting. | No full Lake build, headline theorem, or axiom-guard result for this candidate is recorded. Nothing here has been promoted to `upper-bound/best`. |

## Dependency order and decision gates

```text
A window algebra ───────────────────────────────┐
B signed flow + rounding ──┐                    │
C frontier + seed arithmetic ──> D global schedule ──> E outsider induction
        │                    │                         │
        └─> F root/frontier/terminal rules <───────────┘
                                                   │
                                      G recursive sorter/depth
                                                   │
                                      H coefficient + limsup
                                                   │
                                      I build/axiom audit
```

The root-to-level-one outsider estimate is formalized, conditional only on
the root's `NodeSpec`, and fits the candidate's `mu * capacity` budget. The
actual level-one input tails at every internal ragged cut are now bounded by
that root outsider budget plus the exact signed address-profile slack. The
first ragged sender geometry, four stage-two sender geometries, root stage-two
ragged allocation, and exact stage-three count reset are also formalized. The
`candidate_bootstrap_stage_one_wrong_rank_bound` now composes the input-tail
and card-split results into the variable-window wrong-rank count (focused Lean
check passed). The next missing step is a theorem connecting that rank count
to the ragged network output. The standard `FlowSizes` and
wire-placement model still cannot encode these varying blocks. This is a
closed input-tail gate, not a sorting theorem.

## What the present Lean results do and do not establish

- The local arithmetic and interfaces are kernel checked under their stated
  hypotheses. In particular, the one-step integerizer and the interior
  successor-flow result do not select one schedule consistently across the
  whole tree.
- The two-round separator boundary lemma is about its physical pack at ragged
  cuts. It does not supply the address occupancy premise or prove a subtree
  outsider bound.
- `RaggedBootstrapGeometry.lean`, `RaggedResetGeometry.lean`, and
  `RaggedResetFlow.lean` prove compatible finite geometry/count equations.
  `RaggedFlowContract.lean` gives cut bounds once a physical pack and row
  profile are supplied; it does not install that profile in the current
  execution semantics.
- `RaggedStageOneRank.lean` proves the actual stage-one hL/hR input-tail bounds
  and root-native tail budget, conditional on the root `NodeSpec`;
  `StageOneWindowGate.lean` proves the corresponding cardinality split and
  composed wrong-rank bound: twice the scaled root tail budget plus
  `reserve * seedRootDown d`. The map from this input rank count to the ragged
  network output remains open.
- `CandidateSeed.lean` proves count/placement flow through stage 3, the
  root-to-level-one outsider bound and its candidate-budget comparison, exact
  zero descendant mass below level two at stage one, and actual
  `NodeGood` network existence for the root, level-one bag, and both stage-two
  sender shapes. The stage-one-to-stage-two rank/outsider transition remains
  open, and the stage-3 matching does not establish later sender geometry.
- The ordinary root cannot satisfy the interior discrepancy hypothesis
  directly. A proved root funnel is mandatory.
- Therefore there is currently no complete sorting theorem at 945 (or any
  sub-1000 coefficient) in this experiment. The best verified repository
  endpoint remains the separately maintained `upper-bound/best` package.

## Verification scope

### October 12: internal stage-one rank-window gate

Focused direct Lean checks passed for `StageOneWindowGate.lean` and
`VariableSlots.lean`. The former now bounds actual input wrong ranks at each
internal address `1 ≤ j ≤ 62`. The latter's `VariableRankSlotSpec` now describes
a particular output permutation, rather than incorrectly requiring the
boundary guarantee for every arbitrary permutation. No other source currently
uses that interface.

Next prove that wrong keys in an output slot are covered by the input's
wrong-rank keys and its two boundary crossing sets. Use injectivity of the
output rank permutation to charge the first set, and the existing physical
ragged pack estimates for the crossings. Then instantiate this counting bridge
with the actual key-to-local-rank bijection and bootstrap profile. Endpoints,
later stages, and the global scheduler remain separate obligations.

The focused scratch checks above used direct Lean invocation against cached
dependencies. `lake env` attempted a GitHub dependency fetch in a network-
restricted environment, and neither the complete tapered Lake package nor the
best package was rebuilt for this ledger update. Re-run focused checks after
source changes; run the full candidate build and axiom audit only when the
recursive theorem is assembled. Keep all scratch work in this experiment until
the proof and endpoint have been reviewed; this plan does not authorize
promotion or a commit.

### October 12: exact finite frontier and scalar-flow audit

`frontier_numeric_audit.py` now passes end to end using Python `Fraction`
arithmetic and a parity check that exhausts candidate even-up counts. The
frontier scan checks every transition for `d = 14..2500` (9,328,737
transitions), including parity, one-level endpoint motion, endpoint ordering,
and arithmetic-progression coverage of all scheduled next-stage levels by
interior levels plus newly exposed fringe endpoints. This is a finite
sanity-check of the formulas, not an induction over all `d`.

The same script checks exact scalar conservation identities at rational debt
samples and reports positive minimum normalized coefficients:
retreat-up `30697/2012774400`, advance-down `30697/1965600`, bottom factor
`1030540427279/1030540492800`, and ordinary-down
`268238849/17175674880`. These checks diagnose arithmetic only; the affine
identities still need their Lean theorems, and positivity does not establish
integer ownership or the global outsider invariant. In particular, bottom
contraction with zero down-flow requires an even register size, so any global
integer schedule must handle its parity explicitly.

A numerical adversarial-cut DP/LP is not yet well-specified: the missing
schedule invariant does not give a recurrence or state transition for outsider
mass across arbitrary rank cuts. Inventing one would test a surrogate model,
not the proof obligation. The fastest useful next numerical step is to first
extract a precise finite recurrence from the actual `VariableWindow` /
`VariableSeparator` interfaces and rank-counting bridge; then exhaust or
optimize that recurrence on small trees to search for counterexamples and
identify which signed boundary terms need charging. Until that recurrence is
specified, further simulation would create false confidence.

### October 12: first actual output-rank transfer confirmed

The output-rank gate called out above is now closed for the bootstrap stage,
conditional on the root `NodeSpec` and the stated bulk-separator provider.
`SeparatorKeyBridge.lean` proves the exact recurrence for one separator:

`wrong_output_keys_in_target_slot <= wrong_input_rank_keys_in_native_window + lower_boundary_crossings + upper_boundary_crossings`.

`BootstrapSeparatorOutput.lean` specializes this to the physical ragged
separator. `BootstrapStageOneProvider.lean` then supplies an enumeration of
the actual stage-one child register and separator existence, and proves
`candidate_bootstrap_stage_one_actual_output_exists`; its focused direct Lean
check passed on October 12. The output allowance is compared against the
next reference-capacity budget in `bootstrap_stage_one_separator_budget_le`.

This does not close the later-stage recurrence: the theorem is for the
bootstrap split and does not show that arbitrary later rank prefixes admit
the required three-way cover/descendant-mass lower bound with a controlled
outside-storage term. `FrontierRankCounting.lean` states the needed abstract
counting lemma, but its hypotheses are not yet instantiated by a global
address-indexed schedule. Thus the next mathematical task is no longer the
first output transfer; it is to prove that schedule-specific cover and carry
its signed frontier terms through successive stages. The exact numerical
audit remains limited to frontier formulas and scalar flow: do not interpret
it as an adversarial-cut search or as verification of this later recurrence.

### October 12: three-way rank-cut recurrence instantiated for ragged ownership

Added `RaggedRankRecurrence.lean`. For every time `t` in any
`RaggedWirePartition` sequence, the actual `raggedPlacement` of an address
`w` is partitioned into (i) its current register, (ii) all strict descendant
registers, and (iii) the complement of that subtree. Thus every actual global
key interval `[lo, hi)` is covered by those three sets, with pairwise
 disjoint ownership. The focused theorem `ragged_rank_cut_recurrence` proves:

`currentRegister ∩ [lo,hi)` has size ≤ (hi-lo)-D+O`,

assuming descendants hold at least `D` interval keys and outside-subtree
storage holds at most `O`. The interval cardinality is also proved directly
for the finite key universe. Direct Lean check of `RaggedRankRecurrence.lean`
passed October 12.

This is now a schedule-instantiated structural recurrence, but it does not
supply the quantitative hypotheses. The current schedule type guarantees
ownership only; it has no proved stage-to-stage relation that forces enough
native-prefix mass into descendants or bounds the outside-prefix spill. The
next obligation is to derive those two estimates from the routed split and
separator rank bounds (including moving-frontier signed corrections). Until
then this theorem is an interface for that induction, not a bound on `D` or
`O`, and does not improve the 945 candidate endpoint.

### October 12: ordinary-slot lower bound for descendant native mass

Added `RaggedSlotMass.lean` and imported it from `RaggedRankRecurrence.lean`.
The kernel-checked lemma `descendant_native_mass_lower_of_slot_errors`
proves the local quantitative step: if child-native intervals partition the
rank interval, are pairwise disjoint, and every physical output slot is routed
into strict descendant storage, then slot errors `error[j]` imply

`D >= sum_j (width[j] - error[j])`.

The lemma is deliberately stated over a finite index set, so frontier cases can
use only the active child slots. It converts any per-slot wrong-key estimate
(such as the ragged separator output estimate) into a lower bound on `D`.
The focused direct Lean check of `RaggedSlotMass.lean` passed October 12.

The ordinary-transition instantiation is not yet proved. It must identify the
actual global output key set of each local pack with its routed down-port,
verify the child-native intervals partition the selected parent interval,
and supply the per-slot rank-window input and boundary-crossing bounds. The
same step needs a separate estimate for `O`, charging keys sent to ports
outside the subtree. In particular, this work provides the D-accounting
formula, not the schedule-specific error values or the O recurrence.

### October 12: outside-spill accounting and route inclusion

Extended `RaggedSlotMass.lean` with
`outside_native_mass_upper_of_slot_errors`. If the outside storage under
consideration is covered by designated slots plus an ambient remainder, and
the target interval is disjoint from each designated slot's intended native
region, then its target-interval count is at most

`ambient allowance + sum_j slot_error[j]`.

This is the complementary local O formula; it does not bound the ambient
remainder or identify which off-subtree ports exhaust the complement.
`RaggedTreeRoute.lean` now proves that a child's selected parent down-port is
contained in the child's routed register. Focused checks passed for
`RaggedSlotMass`, `RaggedRankRecurrence`, and `RaggedTreeRoute` on October 12.

The ordinary-step proof still needs to lift that wire inclusion through the
actual stage execution, show the selected native child intervals cover the
parent interval used by the rank cut, and instantiate slot errors using the
input-window wrong-key estimate plus the two B2 boundary-crossing terms.
For O, the complement also contains ancestor and frontier up-ports; their
native leakage and the inherited ambient term need a separate signed
recurrence. These lemmas now turn those obligations into explicit finite
inequalities but do not yet establish their premises for the global schedule.

### October 12: stage execution to routed down-slot

Added `RaggedStageSlotBridge.lean`. The kernel-checked theorem
`ragged_stage_downslot_keys_eq_local_outputs` identifies the actual global key
set in a parent's physical down-slot after a stage with the outputs of the
local node network at precisely that slot's input ranks. The companion
`ragged_stage_downslot_keys_subset_child` lifts this key set into the next
stage's child register, assuming the next ownership partition is exactly the
tree-routed current partition. The focused check passed.

This closes the execution/ownership bridge, but not the numerical induction:
the scheduler must still establish that partition-transition equation,
partition the parent's native interval among child-native intervals, and bound
the local wrong-key counts and off-subtree ambient spill. In particular, the
current result does not yet instantiate either the `D` or `O` recurrence.

### October 12: native-child partition and D-mass specialization

Added `NativeChildrenPartition.lean`. The checked theorem
`native_children_cover` proves that the 64 native key intervals of a bag's
children cover exactly the parent's native keys; `native_children_disjoint`
proves pairwise disjointness. The proof reuses the same child-interval
arithmetic already used in the older Chvatal analysis.

Added `RaggedTreeMassInstantiation.lean`, whose checked theorem
`native_child_mass_lower_of_slot_errors` specializes the generic D-mass lemma
to those actual tree children. For a child slot with capacity `width[j]` and
at most `err[j]` keys outside that child's native interval, if the slot is
owned by the child subtree, the total native mass of the parent in the
descendant storage is at least `sum_j (width[j] - err[j])`. Both focused checks
passed.

This isolates the D-side ordinary-node obligation to scheduler-specific
hypotheses: show actual stage slots have the claimed capacities, are routed
into descendant registers, and satisfy the per-slot wrong-key bounds. It
still does not prove those hypotheses or the O-side outside-spill recurrence;
therefore it does not yet establish the candidate global coefficient.

### October 12: compose the D-side stage geometry

Added `RaggedActualTreeMass.lean`. The theorem
`ragged_actual_child_mass_lower_of_slot_errors` now takes an actual scheduled
transition `P (t+1) = route (P t)` and the physical split at parent `q`. It
derives the slot capacities from the split, proves the emitted slot keys are
owned in strict descendant storage (including terminal children), and applies
the native-child mass estimate. Thus the complete ordinary-step D inequality
is kernel checked conditional only on the per-slot wrong-native-key error
bounds.

Added `RaggedPackNativeError.lean`. It lifts the existing two-boundary B2
output estimate from natural-valued labels to actual `Fin` keys and specializes
the wrong-key predicate to a child-native interval. This proves the required
output-error estimate whenever the input rank-window error `hA`, separator
scrambles, and ragged profile are supplied. `RaggedProfileGeometry.lean`
proves that if the physical up-fringe and child widths are the row-profile
quantities scaled by the column count, physical slot boundaries equal the
row-aligned pack boundaries. All three new modules pass focused checks.

The ordinary-stage D proof is now reduced to a sharper set of concrete gates:
install the pack network/output set into the scheduled node (`hslot`) and prove
the per-slot input rank-window estimate `hA` from the signed outside-tail and
descendant-mass invariants. The row-profile geometry theorem discharges the
boundary alignment once the schedule proves its scaled-width equalities.

### October 12: slot-zero output endpoint

Added `RaggedEndpointOutput.lean`. The checked theorem
`physical_ragged_output_fin_wrong_le_endpoint` proves the same two-boundary B2
output error estimate for slot zero as for interior slots, provided the
initial fringe and first slot have positive width. Its child specialization
`physical_ragged_output_fin_child_wrong_le_endpoint` targets the actual first
native child interval. The focused check passed.

The bootstrap suffix-slack identity now also accepts index zero, and the
stage-one population-split lemma accepts every actual slot index `j < 64`.
This establishes the arithmetic prerequisites for a slot-zero input-rank
gate. That gate is still open: the existing actual hL/hR provider is stated
only for internal slots, and its endpoint adaptation has not yet been
kernel-checked. Thus slot-zero output is closed conditional on its input hA;
the root-to-slot-zero input estimate remains an explicit obligation.

No O-side induction has yet been proved. In particular, outside-subtree
storage includes ancestor/frontier contributions as well as siblings; its
native-prefix leakage must be decomposed by the tree route and controlled by a
separate signed recurrence. The 945 candidate remains unproved, and these
local results do not change the verified 1419 best bound.

## Work estimate and parallel plan (October 12)

These are rough active-work estimates; the candidate's unproved global invariant
makes the large ranges highly uncertain.

| Work package | Concrete deliverable | Estimate | Parallel work |
|---|---|---:|---|
| Bootstrap endpoint input | Slot-zero `hA` from the root outsider tails and the index-zero suffix-slack identity; then compose the endpoint output lemma | 3–8 hours | Independent Lean/interface audit is safe |
| Bootstrap separator installation | A checked `hslot` theorem for the actual child register, pack output, and endpoint slot | 4–12 hours | Can proceed alongside endpoint input once interfaces are fixed |
| Ordinary-node schedule interface | Match physical splits, ragged row profiles, integerized blocks, and ownership transitions for a generic active node | 1–3 days | Split geometry and ownership lemmas across separate workers |
| Candidate all-order outsider invariant | Establish the stage induction for every stranger order, especially top retreat/advance and bottom expand/contract | Several days; may require redesign | Best independent math audit / counterexample search task |
| Recursive signed-prefix/subtree identity | Extend complete-child debt cancellation to a recursively partial child prefix, with endpoint residual inside `reserve` | 1–3 days after invariant is explicit | Can be audited independently from integer rounding |
| Terminal/frontier closure | Seed, recurring moving-frontier exceptions, small-bag stopping, and final purity | 2–5 days after ordinary induction | Frontier case table can be handled separately |
| Depth and limsup conclusion | Sum actual stage and separator costs, then prove the eventual coefficient | 1–2 days after schedule closes | Independent arithmetic audit can run throughout |

Recommended concurrent tracks: (A) endpoint/bootstrap plus pack installation; (B)
all-order outsider induction and a search for a failed frontier case; (C) recursive
signed-prefix cancellation and its exact reserve; (D) independent depth-constant
audit. Keep each track in a separate experiment/scratch file and exchange only
explicit lemma statements. The first decision gate is whether (B) can prove the
candidate invariant at every ordinary and exceptional transition; defer broad
scheduler formalization until that succeeds.
