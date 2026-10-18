# Sorting-network research index

## Current package layout (2026-10-10)

- `upper-bound/best`: current Chvátal endpoint with the two-round separator, coefficient 1419
  (`D(n) ≤ 1419 lg n − 43861`, `limsup ≤ 1419`). Full build and the headline guards passed on
  2026-10-10; math notes in `upper-bound/best/notes/two-round/` (`BULK2.md`, `F2ROUND.md`).
  The previous endpoint (1770) is `upper-bound/alternatives/chvatal-1770`; parked and ruled-out
  ideas are in `upper-bound/backlog/`.
- `lower-bound/best`: Kahale endpoint, coefficient approximately 3.270559454.
  Its real-valued liminf boundedness premise uses the legacy upper package;
  the finite Kahale inequality itself is independent of that construction.
- `upper-bound/alternatives/legacy`: Paterson all-n 6991 / limsup 6990.5 and
  older Seiferas/MGG infrastructure.
- `upper-bound/experiments`: candidate Chvátal improvements and optional
  certificate/expander research.
- `lower-bound/experiments`: retained research beyond the Kahale endpoint.
- `research/limit-existence`: conditional convergence and repair research.
- `archive/handoffs`: preserved historical handoffs; these are not current status.

Build packages separately; their AKS module names overlap. See the root README
and each package README. The completed migration checks are summarized in
[the reorganization verification](reorganization-verification.md). The older proof map below remains historical context;
its dated constants and inline command paths may describe earlier layouts.

### Active upper research

The proposed smaller **one-round** fringe target is ruled out by a deterministic
adversary. The current route is a joint two-round fringe guarantee, paired with
a variance-sensitive bulk lemma. These are research arguments, not improved
kernel-checked endpoints. See [the obstruction](chvatal-fringe-obstruction.md)
and [the small-rank branch](chvatal-two-round-small-ranks.md).

The active UB-25 packet worktree is documented in
[`upper-bound/experiments/packets/INDEX.md`](../upper-bound/experiments/packets/INDEX.md).
Its current checked audit rules out repeating the endpoint-repair macro while
requiring every output packet to remain a consecutive 64-rank slice: the
repaired first/last 32-wire pair has at least 64 down-cut wires between it, and
the merge output preserves those packet supports. The workstream therefore
needs either a depth-accounted repacking step or a redesigned selector/routing
stage that consumes logical packet IDs directly. Simply allowing scattered
sorted packets is insufficient: the current `PacketSortedOn` invariant and
selectors are defined on physical consecutive rank cells. The workstream has
not proved a repeated schedule or improved the 1419 endpoint. The checked
generalized-network model suggests a whole-construction route around that
midstream constraint: sort the initial packet cells, keep later arbitrary
packet embeddings inside one `GenNetwork`, physically re-sort each receiver's
4096-rank windows before the next `WireFlow` step, and apply `Untangle` only
after proving the full composition sorts every input in a fixed output order.
`Untangle` preserves depth, but this is not yet assembled; the all-input error
recurrence and the parallel receiver-window sorter remain open. The checked
`flowA7_globalReceiverMacroBatch` now also exposes that every 4096-wire macro
block remains globally sorted after flattening receiver-local batches. This
provides sorted runs for owner/profile analysis but does not establish their
alignment with destination rank cells. The checked
`profileIntervalMean_partition_sum_interval` lemma shows that an ideal target
on any rank interval is additive under subdivision, which may preserve target
compatibility when actual port-local macro groups subdivide receiver
intervals. The required nested partition for actual `WireFlow` groups is not
yet established. The independent 2026-10-18 review is incorporated in the
packet index: recurrence and precision-versus-depth analysis precede more
routing formalization. The current fine-scale matching contraction preserves
each cohort mean; the exact remaining gate is contraction of those means
under actual cross-stage `WireFlow` reblocking, plus bounds on coarse/fine mode
conversion. See the “Exact form of the missing coarse-mode gate” in
`MIXING-TAIL.md`. An exact integer-count simulation confirms that dense
imbalance can mix while a lone threshold occurrence retains its L1 error under
rounded merge-and-deal; it is only a matching-round model, not the full
`WireFlow` scheduler. No improved global bound is proved. The
four-lane rank-block theorem now composes with a depth-78 physical sorter on
the exact 4096-wire support interval, closing sortedness for that individual
full block at the conditional reassembly cost. It does not establish target
coupling, residue/frontier handling, or a repeatable global recurrence. The
interior `mid` flow formulas also give a derived whole-bag density transfer:
each receiver takes about `1/4096` weight from its parent and the rest from its
64 children. This is a concrete coarse operator, but it does not yet apply to
rank-block errors or show contraction across active levels. See the new
interior-transfer section in `MIXING-TAIL.md`. The
homogeneous mid-level tree operator has a derived deep-subtree conductance
obstruction: receiver-local sibling averaging need not uniformly contract
coarse means. This is not yet a result about the full time-varying schedule;
the current next test is whether actual frontiers or global cross-cohort
mixing remove that mode. See `MIXING-TAIL.md`. The exact
`flow_subtree_cut_screen.py` adds actual `flowA7` frontiers for sample stages:
a level-6 descendant subtree retains bag-density L2 ratio at least
`0.999999999992724` through the flow transfer. This is not a packet-profile
realizability claim, but confirms that global cross-receiver mixing or a
stronger profile restriction is necessary. A sparse power-iteration screen of
eight global matchings through 65,536 packet IDs estimate centered norm near
0.21 and contracts one-packet indicators to about 0.044. A new analytic lead
uses Bordenave--Collins strong convergence for random matchings plus a
Haagerup estimate to bound the limiting eight-round free-product norm by
`225/256`; hence contracting schedules exist for every sufficiently large
even packet count. This gives a raw conditional packet cost of 188.5 per two
bits, but is nonconstructive and not Lean checked. It does not solve
the actual `WireFlow` packet-ID transition, nor does spectral contraction
alone close the L1 error budget or rare integer tails. The eight-round bound
also cannot cancel the factor-65 energy transfer by direct composition; that
crude combination needs 16 global rounds and costs 240.5. A separate exact
screen shows uniform-random compare-split rounds also fail the singleton tail
at logarithmic depth: the singleton must meet the final packet directly each
time, giving success probability at most `R/(C-1)`. No rank-aware multiscale
tail repair is yet designed. If the two-scale coupling fails its `27/256`
cross-term gate, UB-26's localization plus recursive cleanup is the clearest
fallback; its preprocessor remains open. See
`global_matching_power_screen.py`, `random_compare_split_tail_screen.py`, and
`MIXING-TAIL.md`. The
`profileIntervalMean_partition_sum_4096_grid` specialization
handles the two partial boundary groups by clamping grid cuts, and
`blockOf_inter_eq` identifies intersections of port and receiver intervals.
The actual regular-stream block intervals are now checked in the source-port
rank coordinates. A shifted-grid generalization of
`not_three_partial_rankGroups` proves that, for one target receiver interval,
at most two groups in one ordered source stream can be partially intersected,
provided those groups lie in the receiver support. A guarded calculation also
shows one ordinary down-port spans an unbounded number of 4096-wire groups as
dimension grows; the 65-neighbor incidence estimate alone is therefore not a
substitute for the per-interval bound. The old child-cohort merge transposes
packet indices across 64 child ports and remains outside the theorem's scope.
`flowA7_receiver_regular_partial_groups_bound` now proves actual per-port
group containment and at most two partial groups per regular stream; its
guarded aggregate corollary bounds these by 258 per receiver interval. This is
incidence bookkeeping only: it does not bound profile error or charge pooled
tails/frontiers. The independent 2026-10-18 review identifies the closed
one-stage rank/error recurrence as the go/no-go gate before further routing
plumbing. The checked `wireFlowLayer_reencoded_profile_energy_recurrence`
already supplies a conditional layer transfer with squared-error factor 65;
what is missing is its coupling to merge-and-deal's moving target. Under exact
coupling, a matching energy contraction `ρ²` would yield factor `65ρ²` and
requires only `ρ < 1/√65`, before rounding, exceptions, and frontiers. A new
exact-integer Python screen supplies fixed 15-round cycles with Frobenius norm
at most `1/16` for every fan-in `c≤130`, including one pooled exception-block
stream; the incomplete exception tail is omitted. This may replace an
unbounded-family gate if equal-index blocks across the streams are the actual
transition. Its conditional transfer is `65/256`, before fresh errors. It is
not Lean-checked and does not prove that coupling. The 2026-10-18 review's main recommendation
is adopted: derive and simulate the closed recurrence before adding routing
plumbing. The
review's stage-sum arithmetic mixes packet scales: for `s=26`, `m=4096`
gives fresh fraction `0.001587` (about `0.156N` over 98 stages of total mass
`N`), while `m=64` gives `0.1015625` (about `9.95N`). The former is still
about 94,000 times the existing `1/59,000,000` Chvatal allowance. Neither is a
closed recurrence; see the packet worktree's `INDEX.md` for the precise gate.
The newer candidate tracks a separate centered L1 error on 4096-wire blocks;
the 15-round cycle contracts only that component (`sqrt(130)/16 < 0.713`).
The constant mean mode is uncontracted, so no scalar `0.00638` bound applies
to total profile error until its transport is proved. The finite schedule
screen measures unmatched pool-tail mass as `3.94e-6N` through depth 80. A
uniform geometric envelope now bounds this wire mass by `N/86016` at every
depth, but does not bound its profile-error effect. Under an unproved unit-gain
tail-to-centered-error assumption, the candidate recurrence limit is
`22541/3526656 ~= 0.006392`. `monotoneBlocks_assignedRankProfiles_L1_nonincrease` now
kernel-checks an abstract L1 nonincrease for arbitrary reblocking under the
induced suffix-interpolated targets. The 66-piece sender interval owner and
selected-mean identity are already checked by
`wireFlowLayerPieceOwner_profileMean_eq_selected`; the missing owner crosswalk
is for the 4096-wire output blocks/parity lanes and their next-stage targets.
The coarse-mean recurrence remains open. A newer exact finite screen truncates
the local matching cycles to 14 rounds with `rho<=2/25` for fan-ins 1--130;
paired with ten conditional global rounds it raises the ideal cross-mode
allowance above `7/20` at raw coefficient 195. This changes the numeric gate,
not the review's priority: close and test the full scheduler recurrence before
adding routing formalization.
An exact antipodal-pair screen now shows why the global spectral norm cannot
be treated as sorting-error contraction without a target map: on 64 already
rank-sorted 4096-wire packets it creates normalized aggregate profile error
`16/63`. The two-scale contraction calculation also needs its actual rounding
projections; a general spectral lower bound forces at least `167/12288`
asymptotic rank-profile drift for the nine-global-round candidate before
rank-aware correction. The earlier `0.01578` affine fixed point omits this
target drift and is not an actual scheduler bound. See the packet index.
The previously truncated `PacketReceiverOverlap.lean` source has been rebuilt.
Its 4096-wire support sorter, four-lane physical-sort bridge, and receiver
partial-group bounds now compile from source, and `PacketMergeAxioms` passes
its guarded axiom checks. This is structural bookkeeping only; scheduler
coupling and the global rank-profile recurrence remain open.
The candidate port-local repair now has a checked
cell-level lemma: `rankPacketCell_macroGroup` proves that 64 consecutive
64-rank cells form exactly one 4096-rank block within the same port. Together
with `rankIn_blockOf_eq_sub` and `blockOf_blockOf_eq_shift`, this identifies
those groups as the corresponding `blockOf port` slices, which is the premise
shape used by `not_three_partial_rankGroups`; the focused repair-module and
axiom checks pass. The current selectors suggest 129 regular streams per
receiver, each with fewer than 64 residue packets, plus at most 65 endpoint
packets. This caps the pooled exception family at 8,192 packets (128 merge
blocks). The actual selector decomposition and exception pooling are now
formalized by `flowA7_receiver_regularStreams_bundle` and
`flowA7_receiver_exceptionPool`; `flowA7_receiver_exceptionPool_batch` further
groups that concrete pool into at most 128 sorted 4096-wire blocks in one
≤57-layer batch plus fewer than 64 sorted packets. Focused source and standard
axiom checks pass. Global iteration, profile-target compatibility, and the
exception/error contribution to the recurrence remain open. The checked
packetFamily64BlockEmbedding_rankInterval_support proves that one grouped
4096-wire block has exactly its corresponding rank interval when its 64
input embeddings are consecutive 64-rank cells. The checked
packetFamily64BlockList_rankIntervals lifts this to every explicit
grouped-list entry and returns its group index; focused PacketInduction and
PacketMergeAxioms checks pass. CanonicalPacketFullBlockProvenance now records each source packet group and
generated block, and CanonicalStreamFullBlockData carries that provenance.
CanonicalStreamFullBlockData.block_rankIntervals proves exact port-local
interval support conditional on a consecutive rank-cell contract for the
source packets. The focused source and axiom checks pass. The actual stream
rank-cell contract has since been proved in
`flowA7_receiver_childPorts_streamPartition` and carried through
`flowA7_receiver_regularStreams_bundle`; `PacketInduction` compiles. The new
`CanonicalStreamFullBlockData.rankIntervals_of_rankCellStreams` derives the
full-block endpoint condition from the 64-wire cell cardinalities, and
`flowA7_receiver_regularFullBlocks_rankIntervals` instantiates it for the
actual receiver streams. These intervals are in source-port rank coordinates;
transport to receiver ranks and overlap/error accounting remain open. A checked
`rankPacketCell_stream_contract` now packages each aligned regular interval
as sorted, disjoint 64-wire cells with exact support, so the existing
full-block-plus-tail theorem can be applied per stream. The checked
`canonicalStreamFamilies_fullBlocks_disjoint` theorem now applies the
full-block decomposition uniformly to any disjoint family of canonical
streams and proves cross-stream block disjointness; its source and
standard-axiom checks pass. `CanonicalStreamFullBlockData` packages that
decomposition as reusable data, and `flowA7_receiver_regularFullBlocks`
instantiates it for the actual receiver streams while retaining endpoint
coverage. Focused source and standard-axiom checks pass. The exact tails are
now pooled with active endpoints by `canonicalStreamFullBlock_exceptionPool`,
and `flowA7_receiver_regularTailPool` proves the receiver support is covered
exactly by the regular full blocks and that pool; it also packages the pool's
full-block batch. The focused source and standard-axiom checks pass for the support identity,
regular-versus-pool disjointness, generic theorem
canonicalStreamAndExceptionPool_fullBlocks_batch, and its actual interior
receiver composition flowA7_receiver_regularTailPool_commonBatch. It proves a
single ≤57-layer batch covers each interior receiver exactly by sorted output
chunks and a sorted pool tail of fewer than 64 packets. This is not a repeatable
rank-aligned transition; root/frontier composition and the rank-profile
recurrence remain open. The checked
lowA7_shiftedUp_regularStreams_contract` now extracts the prefix and suffix
streams from the actual half-misaligned up-port repair selector, deriving their
lengths from the flow split and residue equation; it leaves the repaired
endpoint pair outside the streams. This closes only that selector branch.
`flowA7_shiftedDown_interiorStream_contract` also extracts, for each actual
shifted down-cut, the interior cells as one canonical aligned stream. Its
32-wire offset is accounted for in the endpoint inequality; the endpoint pair
is excluded. The aligned up-port now similarly splits into separate prefix
and suffix streams, and each aligned down-cut into one complete stream; these
branches have no repaired endpoint packets. The source modules compile.
All four extracted contracts pass their standard-axiom guards through
`PacketMergeAxioms`. Pooling tails/endpoints, proving repeatability, and
establishing the recurrence remain open. The arithmetic cap is now isolated
as `shiftedSelector_exceptionPool_budget`: 129 residues of fewer than 64
packets each plus 65 endpoint packets total at most 8,192 packets (128
4096-wire blocks). This is a conditional count bound, not yet an actual
support partition or error-overlap theorem. The theorem uses only the
standard Lean axioms in its explicit guard. `shiftedSelector_exceptionPool_index_card`
packages these slots as the dependent sum of 129 stream residues plus 65
endpoint slots, ready for a flattened packet-family construction; it still
does not supply their actual supports. `canonicalExceptionPool_family` now
provides that construction interface: with an actual endpoint type of size at
most 65 and sorted, disjoint 64-wire packets at each residue/endpoint index,
it builds a canonical family on the union of those supports. The concrete
selector packet function and its disjointness proof are still missing. Its
source compile and standard-axiom guard pass. `canonicalPacketFamily_residue_contract`
now exposes the final fewer-than-64 original packets of any canonical stream
as a separate canonical sorted/disjoint family. This is the extraction step
needed before combining actual stream residues. It also identifies each tail
packet as a subset of its original stream packet, enabling disjointness to be
transported from disjoint stream supports. Its standard-axiom guard passes.
`canonicalStreamResidues_exceptionPool` now combines supplied residue
families and an actual endpoint family into a canonical pool of at most 8,192
packets, deriving cross-stream disjointness from those support inclusions.
This generic assembly passes its source check and standard-axiom guard; the
concrete selector residues and endpoints are not yet supplied. The two
shifted endpoint constructors now have explicit sortedness, size-64, and
port-containment contracts, and prove disjointness from the regular packets
in the same port. `flowA7_shiftedUp_port_partition` now composes both actual
shifted child streams with their endpoint into an exact up-set support
partition; its focused source check and standard-axiom guard pass. The
positive-flow aligned-up case also has an exact per-port partition;
the aligned theorem's source check and axiom guard pass. The zero-down-flow
child theorem packages the whole up-set as one stream plus an empty stream,
also with both checks passing. Thus all child up-port cases are covered;
the selected parent down-port now has parallel shifted, aligned, and zero
contracts as well. Their focused source checks and standard-axiom guards pass.
The positive-flow child up partitions also prove their two regular streams
are disjoint. What remains in this local stage is to assemble these per-port
results into the indexed 129-stream receiver family and actual endpoint
subtype. This assembly and the concrete exception pool are now checked as
described above; the remaining gap is to combine those pooled exceptions with
each stream's regular full groups in a repeatable rank-profile transition.

## Historical proof map

Local review: 2026-10-09. This index describes the checked-out sources, including
the local Paterson work, rather than just the upstream clone or September handoff.

## Objective and current result

The active target is a smaller upper bound on
`limsup_{n -> infinity} D(n)/log_2 n`, where `D(n)` is minimum binary-comparator
sorting-network depth. A constant for natural logarithms is the base-two constant
divided by `ln 2`.

The completed all-input-size Paterson endpoints are in
[Bounds/PatersonTight](../upper-bound/alternatives/legacy/AKS/Bounds/PatersonTight.lean):

```text
minimum_depth_le_6991: D(n) <= 6991 * Nat.clog 2 n (every n).
minimum_depth_double_le: 2*D(n) <= 13981 * Nat.clog 2 n + 13979.
limsup_minimum_div_logb_le_6990_5: limsup D(n)/log_2 n <= 13981/2.
eventually_minimum_depth_le_7000_logb: eventually D(n) <= 7000 * log_2 n.
```

`minimum_depth_le_7000_logb` gives the explicit sufficient condition
`n >= 2` and `log_2 n >= 1472`. The networks are selected classically.
All correctness and depth proofs are kernel checked. The older complete
million-coefficient theorem remains in [Bounds/Paterson](../upper-bound/alternatives/legacy/AKS/Bounds/Paterson.lean).
The inherited executable networks remain available. This is an improvement to
this repository's formal bound, not to the best published sorting bound.

**Chvátal-form 1830 endpoint (complete, 2026-10-07).** The folder
[`chvatal-1830/`](../upper-bound/best/README.md) is a self-contained Lean package proving, with only
the standard axioms (`propext`, `Classical.choice`, `Quot.sound`):

```text
SortingDepth.minimum_depth_le_1830_logb:  for n ≥ 64^7,
  D(n) ≤ 1830 * log₂ n − 58657
SortingDepth.limsup_minimum_div_logb_le_1830:
  limsup D(n)/log₂ n ≤ 1830
```

(`chvatal-1830/AKS/Bounds/Chvatal1830Final.lean`). The witness networks are full-wire Batcher for
`7 ≤ ⌈log₆₄ n⌉ ≤ 13` and Chvátal's network `Chvatal.chvatal_sorter_exists` beyond (depth
`≤ totalDepth d = 6320 + (3d−21)·3660 + 903` on `64^d` wires, `d ≥ 14`), restricted to `n` wires. It
follows DCS-TR-294 (`dcs-tr-294.pdf`). The Chvátal code is no longer part of the main `AKS`
library; its shared basics (`Sort`, `Bitonic`, `Halver`, `Misc`) are copied into the folder.
The repaired simplification passed its full build and headline axiom guards on 2026-10-08;
see [BUILD_STATUS](../upper-bound/best/BUILD_STATUS.md). Before
this, the best complete upper bound was Paterson's `6991·⌈log₂ n⌉` (above).

## Lower-bound endpoint

The independent Kahale formalization proves
`liminf D(n)/log_2 n >= 1/(1-log_2(phi))`, approximately `3.270559454`,
with `phi = (1+sqrt(5))/2`. It includes the actual comparator execution,
greedy depth scheduling, and analytic limit. The finite inequality is
`n * fib(D(n)+1) <= 2^(D(n)+1) * (D(n)+1)^2`.

Entry point: `lake build AKS.Kahale`. See
[the detailed proof map](kahale-lower-bound.md) and
[the asymptotic endpoints](../lower-bound/best/AKS/Bounds/KahaleAsymptotic.lean).
This reproduces the published lower bound; stronger constants remain research.

## Proved milestones

| Component | Endpoint and source | Precise scope |
| --- | --- | --- |
| Restricted halvers | `Paterson.exists_paterson_halver_all_arities` in [PatersonTail](../upper-bound/alternatives/legacy/AKS/Halver/PatersonTail.lean) | Every side arity, including zero; entropy-formula ceiling depth; existential and selected noncomputably. |
| Full-support provider and complete sorting bound | [PatersonFull](../upper-bound/alternatives/legacy/AKS/Halver/PatersonFull.lean), [PatersonProvider](../upper-bound/alternatives/legacy/AKS/Separator/PatersonProvider.lean), [Bounds/Paterson](../upper-bound/alternatives/legacy/AKS/Bounds/Paterson.lean) | Full halvers at every even arity, the complete scheduler, all-n restriction, and a limsup coefficient at most `10^6`. |
| Shared first-level network | `Paterson.exists_paterson_first_level_all_arities` in [PatersonJointTail](../upper-bound/alternatives/legacy/AKS/Halver/PatersonJointTail.lean) | One network satisfies both required contracts with depth at most 263. Separate existence theorems would not suffice. |
| Five-level network depth | `Paterson.separatorNetwork_depth_le` in [PatersonConstruction](../upper-bound/alternatives/legacy/AKS/Separator/PatersonConstruction.lean) | Depth at most 989 for every arity; correctness has a narrower domain. |
| Supported separator | `Paterson.separatorNetwork_certificate_of_dvd32` in [PatersonCertificate](../upper-bound/alternatives/legacy/AKS/Separator/PatersonCertificate.lean) | For `32 ∣ n`: both extreme cohorts of size `k <= n/50` reach fringes of size `n/32`, with error at most `patersonTailError * k`, and the same network has depth at most 989. |
| Odd-block gadgets | `Paterson.oddInitialHalver_injective` and `Paterson.oddFinalHalver_injective` in [PatersonOdd](../upper-bound/alternatives/legacy/AKS/Separator/PatersonOdd.lean) and [PatersonOddFinal](../upper-bound/alternatives/legacy/AKS/Separator/PatersonOddFinal.lean) | Separate directional virtual-maximum and virtual-minimum constructions. They are not yet an arbitrary-arity five-level separator. |
| Numerical budgets | [PatersonNumerics](../upper-bound/alternatives/legacy/AKS/Bags/PatersonNumerics.lean) | Six entropy bounds: 262, 263, 155, 167, 187, 217; first level shares the maximum, so total depth is 989. |
| Parameter repair | [PatersonParams](../upper-bound/alternatives/legacy/AKS/Bags/PatersonParams.lean) | Literal reported choices fail two interior inequalities. `nu = 693/1000` repairs them with strict slack; ideal stage ratio is below `123/20`. These are scalar inequalities, not a bag invariant proof. |
| Trust audit | [PatersonAxioms](../upper-bound/alternatives/legacy/AKS/Halver/PatersonAxioms.lean) | Compile-time axiom checks for the main local results: only `propext`, `Classical.choice`, `Quot.sound`. |

The supported contract is intentionally weaker than the existing
[`IsSeparator`](../lower-bound/experiments/AKS/Separator/Defs.lean): its cohort support `1/50` is smaller
than its fringe fraction `1/32`. The first-level large-cohort contract remains
available in `firstLevelNetwork_good`; it must be used by the future bag proof.

## Proof files by role

Read the endpoint for a milestone first, then follow its imports. The files
already separate the main arguments; there is no need to merge them into one
large proof or build optional certificate libraries to work on them.

| Layer | Files under `AKS/` |
| --- | --- |
| Interfaces and matching networks | `Halver/Paterson.lean` |
| Counting and trap correctness | `Halver/MatchingCount.lean`, `Halver/PatersonCorrectness.lean`, `Halver/PatersonExistence.lean` |
| Entropy and depth accounting | `Halver/PatersonEntropy.lean`, `Halver/PatersonMonotonicity.lean`, `Halver/PatersonDepthBridge.lean` |
| Witness reduction and uniform tail | `Halver/PatersonWitnesses.lean`, `Halver/PatersonCollapsedWitnesses.lean`, `Halver/PatersonTail.lean` |
| Simultaneous first-level guarantee | `Halver/PatersonSimultaneous.lean`, `Halver/PatersonJointTail.lean` |
| Ambient input and separator interface | `Separator/PatersonInjective.lean`, `Separator/PatersonDefs.lean`, `Separator/PatersonFamily.lean` |
| Network assembly and even-chunk induction | `Separator/PatersonConstruction.lean`, `Separator/PatersonNear.lean`, `Separator/PatersonStep.lean`, `Separator/PatersonPrefix.lean`, `Separator/PatersonCertificate.lean` |
| Odd-size directional bridges | `Separator/PatersonOdd.lean`, `Separator/PatersonFlip.lean`, `Separator/PatersonOddFinal.lean` |
| Scalar parameters and numerical certificates | `Bags/PatersonParams.lean`, `Bags/PatersonNumerics.lean` |
| Axiom assertions | `Halver/PatersonAxioms.lean` |

## Completed rounded Paterson implementation

The active candidate uses `A = 19/4`, `mu = 199/10000`, `delta = 1/57`,
`nu = 707/1000`, minimum capacity `300000`, and rounding allowance `10`.
[FastParams](../upper-bound/alternatives/legacy/AKS/Paterson/FastParams.lean) checks every interior parameter
constraint and `(2*A)^2 * nu^13 < 1`.
The older `roundedParams` and ideal approximately-6100 certificates are
historical candidate arithmetic; the current budget includes root sorting.

### Checked concrete components

| Component | Files | What is proved |
| --- | --- | --- |
| Parallel separator stage | [BagSeparator](../upper-bound/alternatives/legacy/AKS/Paterson/BagSeparator.lean), [Stage](../upper-bound/alternatives/legacy/AKS/Paterson/Stage.lean) | Actual scattered bag networks, depth at most 989, local execution identities, supported old-stranger filtering, and a routed placement for specified fringes. |
| Fresh-stranger source | [Fresh](../upper-bound/alternatives/legacy/AKS/Paterson/Fresh.lean), [Balance](../upper-bound/alternatives/legacy/AKS/Paterson/Balance.lean) | Actual first-halver execution estimates, finite disjoint-cohort counting, rounded fresh-cost arithmetic, and a capacity-based sufficient condition for rank balance. |
| Concrete interior preservation | [Transition](../upper-bound/alternatives/legacy/AKS/Paterson/Transition.lean) | `interior_parallel_step` discharges the former abstract separator-filter and first-stranger hypotheses. Actual size, capacity, fringe, parity, and `ChildBalance` hypotheses remain explicit. |
| Descendant contamination | [Subtree](../upper-bound/alternatives/legacy/AKS/Paterson/Subtree.lean) | Geometric subtree intrusion bound for the new Paterson parameters, conditional on the old invariant and parity emptiness. |
| Rounded size recipe | [Schedule](../upper-bound/alternatives/legacy/AKS/Paterson/Schedule.lean), [BoundarySchedule](../upper-bound/alternatives/legacy/AKS/Paterson/BoundarySchedule.lean), [ClippedRouting](../upper-bound/alternatives/legacy/AKS/Paterson/ClippedRouting.lean) | 32-lattice subtree totals, size bounds, fringe coverage, and exact routing counts at full, clipped, and empty levels. |
| Explicit cold storage and one-tree allocation | [ColdStorage](../upper-bound/alternatives/legacy/AKS/Paterson/ColdStorage.lean), [ColdAllocation](../upper-bound/alternatives/legacy/AKS/Paterson/ColdAllocation.lean), [AllocationSchedule](../upper-bound/alternatives/legacy/AKS/Paterson/AllocationSchedule.lean), [AllocationPreservation](../upper-bound/alternatives/legacy/AKS/Paterson/AllocationPreservation.lean), [AllocationInitial](../upper-bound/alternatives/legacy/AKS/Paterson/AllocationInitial.lean) | Computable ownership including cold storage, centered initialization and feeds, actual routing, and `allocationRun_invariant`. Every bag and cold-storage cardinality is checked while the root capacity stays above the threshold. This is positional allocation, not sorting correctness. |
| Storage-aware comparison and routing | [StoredStage](../upper-bound/alternatives/legacy/AKS/Paterson/StoredStage.lean), [StoredRouting](../upper-bound/alternatives/legacy/AKS/Paterson/StoredRouting.lean), [StoredSizes](../upper-bound/alternatives/legacy/AKS/Paterson/StoredSizes.lean) | Parallel execution for arbitrary bag-local networks, depth bounds, unchanged cold inputs, nonroot register flow, root returns, and actual output cardinalities. |
| Actual full-bag rank balance | [AllocatedSubtree](../upper-bound/alternatives/legacy/AKS/Paterson/AllocatedSubtree.lean), [RankCohorts](../upper-bound/alternatives/legacy/AKS/Paterson/RankCohorts.lean), [AllocationBounds](../upper-bound/alternatives/legacy/AKS/Paterson/AllocationBounds.lean), [AllocatedBalance](../upper-bound/alternatives/legacy/AKS/Paterson/AllocatedBalance.lean) | Actual subtree totals and parent/sibling conservation, native rank counts, and `allocated_full_cohort_balance` from the old stranger invariant. Coherent rounding cancels in the sibling deficit. |
| Actual partial-bag rank budgets | [PartialBoundary](../upper-bound/alternatives/legacy/AKS/Paterson/PartialBoundary.lean), [AllocatedPartialBalance](../upper-bound/alternatives/legacy/AKS/Paterson/AllocatedPartialBalance.lean) | Available cohort counts, actual half-size upper bounds, `allocated_partial_fresh_budget`, and separator support when the outgoing middle is nonempty. These estimates are now assembled by `ScheduledPartialTransition`. |
| Root purity and sort cost | [Root](../upper-bound/alternatives/legacy/AKS/Paterson/Root.lean), [TightDepth](../upper-bound/alternatives/legacy/AKS/Bitonic/TightDepth.lean) | At a sufficiently small root capacity, the invariant implies zero deepest strangers from level six. Given explicit region size bounds, the top region has fewer than `2^33` wires and its scattered bitonic sort costs at most 561. No forest splitting correctness theorem yet. |
| Arbitrary virtual padding | [Padding](../upper-bound/alternatives/legacy/AKS/Paterson/Padding.lean) | Both directional supported contracts survive restriction with virtual maxima/minima, without additive error. |
| Concrete partial-bag gadget | [PatersonRefinement](../upper-bound/alternatives/legacy/AKS/Separator/PatersonRefinement.lean), [PatersonPartial](../upper-bound/alternatives/legacy/AKS/Separator/PatersonPartial.lean), [PatersonHalfCounting](../upper-bound/alternatives/legacy/AKS/Separator/PatersonHalfCounting.lean), [PatersonPartialCertificate](../upper-bound/alternatives/legacy/AKS/Separator/PatersonPartialCertificate.lean) | Four refinement levels cost 726; the actual-size first split and padded half refinements cost 989. `partialNetwork_supported` proves both whole-network directional supported contracts with explicit actual-size and virtual-size support budgets. The first split retains its large-cohort guarantee. The mixed boundary invariant is checked in `ScheduledInvariant`. |
| Proposed operation counts | [Accounting](../upper-bound/alternatives/legacy/AKS/Paterson/Accounting.lean) | `T(k) = 13*ceil(k/2)` overcomes initial capacity growth. The proposed cost `989*T(k) + 561*k` is at most `7000*k` for `k >= 613`. These are arithmetic theorems, not sorting theorems. |
| Kernel audit | [Axioms](../upper-bound/alternatives/legacy/AKS/Paterson/Axioms.lean), [StorageAxioms](../upper-bound/alternatives/legacy/AKS/Paterson/StorageAxioms.lean) | Guarded axiom checks on transition, padding, partial certificates, allocation runs, actual rank balance, root bounds, and accounting. Only `propext`, `Classical.choice`, and `Quot.sound` appear. |

### Remaining global obligations

The comparison-stage obligation is now closed: `scheduledCompare_preserves`
in [ScheduledInvariant](../upper-bound/alternatives/legacy/AKS/Paterson/ScheduledInvariant.lean) handles full,
partial, root, inactive, and empty-middle cases. The selected local networks and
actual stage have depth at most 989.
[PatersonRun](../upper-bound/alternatives/legacy/AKS/Separator/PatersonRun.lean) constructs the repeated network
and proves its invariant and depth at most `989*t` within the root window.

Root split groundwork is also checked:

- [RootAllocationBudget](../upper-bound/alternatives/legacy/AKS/Paterson/RootAllocationBudget.lean): the actual
  upper region has fewer than `2^33` registers in the root split window.
- [UpperRegionCounts](../upper-bound/alternatives/legacy/AKS/Paterson/UpperRegionCounts.lean) and
  [DescendantRegisters](../upper-bound/alternatives/legacy/AKS/Paterson/DescendantRegisters.lean): the upper
  and deep regions partition all registers, with upper size `N - 64*T6`.
- [DeepErrors](../upper-bound/alternatives/legacy/AKS/Paterson/DeepErrors.lean),
  [DeepPurity](../upper-bound/alternatives/legacy/AKS/Paterson/DeepPurity.lean), and
  [DeepPrefixAgreement](../upper-bound/alternatives/legacy/AKS/Paterson/DeepPrefixAgreement.lean): global deep
  error bounds, exact half purity, and actual/assigned prefix agreement outside errors.
- [DeepPrefix](../upper-bound/alternatives/legacy/AKS/Paterson/DeepPrefix.lean): exact assigned deep prefix counts.
- [PrefixDiscrepancy](../upper-bound/alternatives/legacy/AKS/Paterson/PrefixDiscrepancy.lean): generic remaining
  prefix discrepancy and sorted-bin wrong-rank bounds.

### Completed global proof chain

| Obligation | Checked endpoint |
| --- | --- |
| Exact sorted-bin coordinates and errors | [RootPrefixCoordinates](../upper-bound/alternatives/legacy/AKS/Paterson/RootPrefixCoordinates.lean), [RootSortedBins](../upper-bound/alternatives/legacy/AKS/Paterson/RootSortedBins.lean) |
| Actual root rebuild, cardinalities and stranger budgets | `allocatedRebuild_preserves` in [RootRebuildInvariant](../upper-bound/alternatives/legacy/AKS/Paterson/RootRebuildInvariant.lean) |
| Independent halves, actual child allocation and invariant | `scheduledChild_allocation`, `scheduledChild_invariant` in [ChildInvariant](../upper-bound/alternatives/legacy/AKS/Paterson/ChildInvariant.lean) |
| Phase windows, fuel and well-founded recursion | [ForestPhase](../upper-bound/alternatives/legacy/AKS/Paterson/ForestPhase.lean), [PatersonForest](../upper-bound/alternatives/legacy/AKS/Separator/PatersonForest.lean) |
| Actual recursive network depth | `forestNetwork_depth_le` in [PatersonForestDepth](../upper-bound/alternatives/legacy/AKS/Separator/PatersonForestDepth.lean) |
| Input-independent final rank arrangement | `preliminaryNetwork_independent` in [PatersonForestRanks](../upper-bound/alternatives/legacy/AKS/Separator/PatersonForestRanks.lean) |
| Fixed permutation correction in depth k | `exists_known_permutation_correction` in [KnownPermutation](../upper-bound/alternatives/legacy/AKS/Sort/KnownPermutation.lean) |
| Full sorting correctness and doubled depth bound | `correctedForest_sorts`, `correctedForest_depth_double` in [PatersonForestSorts](../upper-bound/alternatives/legacy/AKS/Separator/PatersonForestSorts.lean) |
| All-n minimum depth and limsup | [PatersonTight](../upper-bound/alternatives/legacy/AKS/Bounds/PatersonTight.lean) |
| Complete theorem axiom audit | [PatersonTightAxioms](../upper-bound/alternatives/legacy/AKS/Bounds/PatersonTightAxioms.lean) |

The final coefficient is `989*(13/2) + 561 + 1 = 6990.5`. The doubled
finite-size budget is `13981*k + 13979`. All global obligations needed for
the 7000 target are discharged; reducing the coefficient further is new work.
The older proposed-count arithmetic above is retained as historical context.

## Build and audit

Pinned toolchain: `leanprover/lean4:v4.29.0-rc4`. Use the checked-in
`lake-manifest.json`; an audit does not require updating Mathlib.

```sh
# Independent milestone checks (each builds its own dependency closure).
lake build AKS.Halver.PatersonTail
lake build AKS.Halver.PatersonJointTail
lake build AKS.Separator.PatersonCertificate
lake build AKS.Separator.PatersonOddFinal
lake build AKS.Halver.PatersonAxioms
lake build AKS.Paterson.Transition
lake build AKS.Separator.PatersonPartial
lake build AKS.Paterson.Axioms
lake build AKS.Paterson.GoodRouting
lake build AKS.Paterson.AllocatedPartialBalance
lake build AKS.Paterson.StorageAxioms
lake build AKS.Separator.PatersonRun
lake build AKS.Paterson.CoarsePrefixCount
lake build AKS.Paterson.ForestAxioms
lake build AKS.Bounds.Axioms
lake build AKS.Bounds.PatersonAxioms
lake build AKS.Bounds.PatersonTightAxioms

# Full core, including the existing sorting theorem and local research.
lake build AKS

# Portable source audits; run from the repository root.
python scripts/sorry-gate
python scripts/sorries
```

The full `lake build AKS` passed with the new minimum-depth/limsup theorem
and rounded Paterson modules included in the root build.
The new endpoint axiom assertions permit only `propext`, `Classical.choice`,
and `Quot.sound`. Source audits found no `sorry`, `#exit`,
or declared `axiom` in the protected files. The optional
`upper-bound/experiments/expanders/Random/` native-evaluation path is separate
from the AKS and Paterson proofs. The audit now reads UTF-8 on
Windows and permits the selected refined network in `Bounds/PatersonTight.lean`,
the classical minimum-depth definition in the exact
`Bounds/Upper.lean` file and selected Paterson network in `Bounds/Paterson.lean`,
alongside the two named analytic Paterson files in `Bags/`. Both `network`
and `SortingDepth.upperNetwork` remain computable definitions.

## Current research directions (2026-10-05, unverified unless noted)

- Paterson tuning is exhausted in-family. A full-floor grid search over
  `(A,μ,δ,δᵢ,ν,mincap)` encoding every known floor (bag parameters, lattice
  fringe, cohort corners, rebuild lock, `νA ≥ 1`, ceiling margins) found 775
  fully-feasible points, none with stage ratio `m ≤ 12`; the checked-in
  parameters are the in-family optimum at `6990.5`. Scripts
  (`scripts/paterson_search.py`, `scripts/paterson_fullfloor_search.py`) are
  untracked experiment tooling, not proof. Earlier sub-6990 search hits
  (`6463`, `6894.5`) were retracted as infeasible mirages missing hidden
  floors; the `tune-6463` branch was deleted and `main` rebuilt green.
- Chvátal 1830 track: **complete**. See the headline section above and
  [chvatal-1830/](../upper-bound/best/README.md); the scaffolding-era notes are in
  [old/chvatal-1830-scaffolding-history.md](old/chvatal-1830-scaffolding-history.md).

## Chvátal 1830

The self-contained proof is in [`chvatal-1830/`](../upper-bound/best/README.md) (proof map and build
instructions) with its modular ledger in [`chvatal-1830/LEDGER.md`](../upper-bound/best/LEDGER.md).
Unused earlier scaffolding is archived, unbuilt, in
[`archive/chvatal-scaffolding/`](../archive/chvatal-scaffolding/README.md).

## Documents and history

- [Sorting-depth limit and repair-interface investigation](sorter-repair-barrier.md)
  (2026-10-07): checked prefix-locality, dependency, and cut lemmas; a derived
  obstruction to staged local-module amplification with vanishing repair
  overhead; finite lifted-prefix probes. `Bounds/DyadicLimit` proves full
  convergence **conditional on** a uniform additive composition defect.
  The defect is unproved; existence of the limit and improved coefficients
  are not claimed. See the note's verification and status map.

- [Paterson interface audit](paterson-interface.md): detailed local theorem
  contracts, corrected parameter arithmetic, and remaining mathematical issues.
- [Local Paterson paper](paterson.pdf): primary mathematical source for this
  track; verify claims against the relevant sections before extending the proof.
- [September handoff entry point](../archive/handoffs/AKS_CODEX_HANDOFF_2026-09-27/README_START_HERE.md)
  and [historical proof ledger](../archive/handoffs/AKS_CODEX_HANDOFF_2026-09-27/PROOF_STATUS_LEDGER.md):
  preserved background. Their claim that Paterson is not formalized predates
  the completed rounded forest formalization and its final sorting theorem.
- [Current research state from the handoff](../archive/handoffs/AKS_CODEX_HANDOFF_2026-09-27/CURRENT_RESEARCH_STATE.md):
  Avenue 2 and `GoodSplitter` ideas remain research leads; candidate constants
  from older handoffs are not proved.
- [Bag-tree notes](bags.md), [module guide](modules.md), and the remaining
  upstream `docs/` describe inherited infrastructure. Some progress/trust
  descriptions are historical; use Lean declarations and current axiom checks
  as the evidence for proof status. `docs/old/` is historical planning material.
### UB-28 finite compare-split screen (2026-10-18)

In the active UB-25 worktree, `upper-bound/experiments/packets/dyadic_compare_split_screen.py`
exactly checks candidate dyadic cross-matching schedules on small packet counts.
For 16 IDs, five rounds per pairing pass sort all 65,536 Boolean profiles at
seed 500001 (seed 0 fails); for eight IDs, seed 500001 sorts all 6,561
capacity-2 zero-count profiles under compare-split. This is exploratory finite
evidence, not a uniform construction, a proof of lifting, or an improved
constant. A uniform five-round schedule plus a sorted-run lifting theorem
would suggest a conditional coefficient 130 when each capacity-4096 packet
compare-split costs 13 layers. The exact evidence and gates are in the packet
index. CLRS 3rd ed. Exercise 28.5-3 states the sorted-run lifting theorem, so
that gate appears formalizable from a known result. However, exact SAT screens
find failures at 32/64 IDs for several tested seeds; at 64 IDs, all tested
seeds 0--14 fail for `d=7`. No uniform family has been found. The raw limit is
`d≤7` with 4096-wire packets, or `d≤14` with 64-wire packets (each compare-split
then costs 7 layers).
The previously noted recurrence, precision-versus-cost, target-coupling and
frontier obligations remain open.
The SAT checker now also emits paired forcing certificates for failures; its
backward antichain recurrence and the `n=64,d=7` example are in the packet
index. Counting disjoint certificate pairs across random rounds is the next
mathematical gate; direct antichain enumeration grows too fast even at 16 wires.
An alternative sufficient invariant is rank-correct minimum certificate size
at each output (`n-k` for forcing 1, `k+1` for forcing 0); it may compress the
gate, but overlap still needs control.
All tested dyadic schedules also pass the exhaustive single-swap family at 64
IDs, including a schedule known to fail general inputs; its failure is not
captured by one swapped pair across a threshold cut. See
`dyadic_single_swap_screen.py` in the packet experiment.
The current `n=64,d=7,seed=0` SAT witness is 16 swaps from sorted order (31
ones, 38 runs); a radius-2 minimization query timed out, so the least failing
displacement radius is unknown.

The packet worktree's exact Haagerup screen now also bounds nine independent
global matching rounds by `11/16`; strong convergence gives existential finite
schedules of norm at most `45/64` for sufficiently large even packet counts.
This raises the conditional two-scale cross-mode allowance to `19/64` and
costs 195 per log bit with the current 15 local rounds and 78-layer
reassembly. The operator-state coupling and all error/tail gates remain open;
the details are in `packets/MIXING-TAIL.md` and `free_matching_bound.py`.

The packet worktree now has an exact one-round rank-span diagnostic: on a
rank-sorted array of singleton-key packets, any perfect matching creates
normalized target drift `sum_edges |i-j|/(C*(C-1))`. Random perfect matchings
have expected drift tending to `1/6`, while a `0.02` budget requires average
edge span below `0.04*(C-1)`. This quantifies the rank-locality cost of the
proposed global mixing; later rank-aware correction remains unanalyzed. See
`upper-bound/experiments/packets/rank_target_drift.py` and its worktree notes.

The packet worktree's sampled nine-round global matching product has normalized
pre-reassembly rank-step drift about `0.333` for 64--1024 packet IDs, while its
estimated centered norm is `0.156`--`0.205`. The exact interpretation is total
expected absolute packet-ID displacement in the induced walk; dense comparison
checks it through 256 IDs. This reinforces that the matching product nearly
erases rank information and that later rank-aware correction is essential.
See `upper-bound/experiments/packets/global_matching_power_screen.py` and
`packets/MIXING-TAIL.md`. This remains sampled evidence, not a uniform bound.

For the sampled nine-round matching schedule, the proposed per-packet
4096-wire sorting step preserves each packet's threshold count and therefore
leaves its roughly `1/3` rank-target drift unchanged. It misses the conditional
`0.02` error target unless a cross-packet correction is added and costed; that
correction is not in the 195-layer budget. This refutes the sampled schedule
as currently completed, not every rank-mixing construction.

The packet worktree has a stronger rank-target obstruction than its earlier
step-profile estimate. A centered rank-ramp variance argument forces
pre-reassembly drift `(1-gamma^2)*(C+1)/(12*(C-1))` for a doubly stochastic
mixer of centered norm `gamma`. With merge-deal rounding charged, the candidate
nine- and ten-round schedules have finite lower bounds `0.04104` and `0.05647`
at 65,536 packets, respectively, exceeding their conditional `0.02` error
target. Exact rational checks are in `upper-bound/experiments/packets/free_matching_bound.py`.
This rules out direct rank-indexed composition under those norm gates; the
rank-aware target update is still unproved.

A packet-permutation-robust estimate further strengthens the rank-ramp gate.
For every rank-step profile, contraction by `gamma` leaves L1 error at least
`2*(1-gamma)*h(C-h)/C` even under the best reassignment of whole packet
labels. Summed over all cuts and rounded, the nine-/ten-round candidates force
`0.09786` / `0.14722` normalized error at 65,536 packets. Thus no permutation
of whole packets can fix the direct spectral-mixing target drift; correction
must compare values across packet boundaries or track a different rank-aware
state. This is conditional on the rank-indexed mixer model. See
`upper-bound/experiments/packets/MIXING-TAIL.md` and
`upper-bound/experiments/packets/free_matching_bound.py`.

The per-cut permutation-robust inequality is now kernel-checked in
[`RankDriftBound.lean`](../upper-bound/experiments/packets/RankDriftBound.lean):
for a fractional output profile with mass `h` and centered variance at most
`gamma^2*h*(C-h)/C`, every rank-step labeling of size `h` incurs L1 error at
least `2*(1-gamma)*h*(C-h)/C`. The all-cut summation and finite rounded
applications remain in the exact-rational Python screen; no actual-scheduler
variance contraction is proved.

The dyadic rank-aware compare-split experiment's seed-0, 14-round-per-pass
schedule sorts all Boolean inputs at 64 packet IDs (168 comparator layers,
SAT unsat for any adjacent inversion) but two tested 14-round seeds fail at
128 IDs: seed 0 has an output inversion at `(64,65)` from an input with 63
ones, and seed 1 fails at `(62,63)` with 65 ones. Thus the seed-0 raw
coefficient 196 is rejected, while other seeds and rank-aware schedules
remain open. A nested-matching variant certifies sorting at 128 IDs for
`d=17` and fails for `d=14,15`; a solver-seed-2 SAT run finds a concrete
`d=17` failure at 256 IDs, so its conditional scalar coefficient 34 is
rejected. The `d=18` and `d=20` checks remain `unknown` at 256 IDs. Uniform
families at those round counts would have scalar depth coefficients 36 and
40; no such theorem is known. The coefficient 238 applies only when lifting each scalar comparator
to a 64-wire packet merge. This remains finite evidence, not a uniform family. See
`upper-bound/experiments/packets/dyadic_compare_split_sat_screen.py` and
`packets/INDEX.md`.

A literature screen of fixed-depth `k`-sorting networks found no direct
coefficient route: recursive self-substitution of a depth-`d`, arity-`n^gamma`
network gives depth exponent `log_(1/gamma)(d)`, while the general lower bound
`gamma >= 1/ceil(d/2)` forces that exponent above one for every fixed `d`.
Thus this known k-ary recursion does not supply the needed `O(log n)` bound;
see the qualified analysis in
[`sub200-structural-strategies.md`](../upper-bound/backlog/sub200-structural-strategies.md)
and the [ITCS 2023 paper](https://drops.dagstuhl.de/storage/00lipics/lipics-vol251-itcs2023/LIPIcs.ITCS.2023.43/LIPIcs.ITCS.2023.43.pdf).
