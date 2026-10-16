# UB-25 packet proof workstream

Current local proof checkpoint: 2026-10-16, Codex (GPT-6-astra-high).

The ordinary odd-even merge proof is complete for all power-of-two widths.
This includes merging two ascending 32-wire runs on their original wire
order in at most six comparator layers. No reversal or input permutation is
needed. These are scratch results in the `upper-bound/best` network model;
the accepted sorting bound remains 1419.

## Checked modules

| Module | Result and scope |
| --- | --- |
| `OddEvenMerge64.lean` | `oddEvenMergeNet_sorts_two_runs` proves the actual recursive network correct on any two ascending runs. `oddEvenMergeNet64_sorts_two_runs` and `oddEvenMergeNet64_depth_le` specialize to 64 wires and depth six. Scatter correctness and depth preserve this on any increasing 64-wire embedding. The dealt lanes are sorted and have exact floor/ceiling Boolean counts. |
| `PacketAlignment.lean` | Scheduled flow residues, fragment counts, separated endpoint supports and sender disjointness. Historical bitonic fallback lemmas remain available. |
| `PacketRepair64.lean` | An input-independent ordinary network repairs two physically separated 32-wire supports in six layers. Actual shifted down-cut/up-fringe fragments are sorted under `PacketSortedOn`, which orders each packet but imposes no inter-packet value order. Disjoint repair families have depth at most six and act as the corresponding local merger on each pair. `flowA7_sourcePortRepairStage_depth_le` chooses the shared-port repair on every eligible source bag and composes these networks through the actual `stageNet`, preserving the six-layer depth bound globally. `flowA7_sourcePortRepairNet_layout` lifts the chosen Boolean repair contract to arbitrary linearly ordered values by thresholding. `flowA7_sourcePortRepairStage_layout` proves every designated support sorted on its physical-wire image. `flowA7_sourcePortRepairStage_sourcePackets` combines the actual up-set and all 64 down-cut packet families into one indexed family of pairwise-disjoint sorted 64-wire supports whose union is the full sender register after correction. The canonical parent/child port selectors handle zero, aligned, and repaired cuts, and `flowA7_receiver_allCases_canonical` proves the full local receiver transition for every combination. The remaining gap is carrying these packet embeddings through matching rounds while keeping them compatible with later positional `WireFlow` cuts. |
| `PacketGenMerge.lean` | An arbitrary injective placement of an ordinary network preserves execution and depth in `Untangle.GenNetwork`. `genMerge_sorts_two_runs` and `genMerge_depth_le` apply at every power-of-two width, including seven layers for 64+64 packets and thirteen for 4096+4096. `genScatterBatch` composes any fixed local network across a list of disjoint supports, proves the global depth is at most local depth, and proves exact local execution on every support. Dealing has exact floor/ceiling counts, including all value thresholds. |
| `PacketMergeTree.lean` / `PacketMergeTreeGen.lean` | Both the 63-run (4032-wire) and 64-run (4096-wire) merge trees are proved at depth at most 57. `packetFamily_divisible64_merge` handles divisible cohorts, and `packetFamily_residue63_merge` handles `64*q+63` cohorts by merging all full blocks and the unequal tail in the same 57-layer batch. Exact threshold profiles are carried through both cases. `PacketReceiverResidue.lean` proves these are the only residues for every nonzero active receiver in the actual schedule. Matching the resulting packets to physical next cuts remains open. |
| `PacketInduction.lean` | `flowA7_receiver_allCases_embeddingFamily` composes the all-case `WireFlow` receiver theorem with `canonicalPacketFamily_toEmbeddings`, yielding a sorted, disjoint, exactly covering embedding family ready for matching. The divisible-64 and residue-63 receiver wrappers apply the corresponding 57-layer block batch to the actual receiver output. `genIndexedPacketRound_canonicalOutput` converts the checked list output of a covered indexed matching round into a `Fin`-indexed logical embedding family. For a partial matching, `genIndexedPacketRound_withSingletons_contract` combines dealt outputs with unchanged unmatched singleton packets and proves sortedness, pairwise disjointness, and exact full support coverage; `genIndexedPacketRound_withSingletons_canonicalOutput` reindexes this family by `Fin` and preserves the seven-layer depth bound. The contract still does not identify later output embeddings with physical-rank port cuts. |
| `PacketRebinning.lean` | The scalar complementary-half rebinning model preserves counts and cannot increase positive/negative spill or squared energy around any common real reference. |
| `PacketSenderCycle.lean` | The 65 shifted boundary cells are distinct whole source packets. Actual child and parent repairs consume complementary halves in a fixed cycle and cover exactly those cells. A fixed ordinary six-layer network sorts all 65 repaired pairs and leaves other wires unchanged. `scheduled_senderRepair_exists` instantiates this on actual ordinary scheduled bags with positive down-flow and shifted half-fringes. |
| `PacketCountBridge.lean` | Enumeration-independent true counts, exact prefix/suffix counts of sorted packets, and pairwise count conservation through parallel execution. `senderRepair_count_exists` gives one fixed six-layer network with sorting, exact cycle counts, sender-centered squared-energy nonincrease for every real reference, and unchanged wires outside the boundary cells. `senderRepair_count_at_threshold` transfers its Boolean count contract to all value thresholds of that same network. This is a local sender result, not a destination or global recurrence. |
| `PacketProfile.lean` | Kernel-checked sorted Boolean packet profile for 4096-wire packets split into 64-wire cells. Actual cell counts have the ideal clamp formula. Across any cohort and fractional common mean, aggregate cell-profile L1 error equals the coarse packet-count L1 error exactly; its square is bounded by cohort size times coarse squared error. Connecting this profile to scheduler ports and destination reassembly remains open. |
| `PacketHalfProfile.lean` | Checked clamp-profile and exact L1 / squared-error transfer for 32-wire halves and arbitrary rank intervals. It identifies actual `WireFlow.blockOf` counts with ideal profiles, and the 66 rank pieces (64 child blocks plus both parent-fringe halves) of each sender form a packet-specific partition. Heterogeneous sender sizes and per-sender means are allowed. `wireFlowReceiver_count_error_actual` instantiates the 65-source parent/children pattern on actual `wireSets` and flow sizes, assuming each sender's post-stage threshold profile is sorted. `wireFlowReceiver_selected_count_eq_register` proves the selected source-piece counts equal the threshold count in the actual `execPlacement` receiver register, using injectivity and disjointness. The corollary `wireFlowReceiver_register_count_error_actual` bounds that register's discrepancy from the selected source-profile means by the sum of the source count errors. The finite-type `sum_receiver_profile_errors_le_source_count_errors` is instantiated on all `KBag 64 d` bags by `wireFlowLayer_profile_error_sum_le`; `wireFlowLayerSelection` has a checked range bound and pairwise disjointness for the actual parent/child piece routing, with root fringe routing excluded. `wireFlowLayerSelection_receiverSource` matches the global selector with the local selector on every receiver neighbor; `wireFlowLayerSelection_eq_empty_of_not_neighbor` and `wireFlowLayerSelection_receiverSum_eq` prove support and exact source-sum reindexing onto its 65 actual neighbors. `wireFlowLayer_receiver_signed_error_eq_register` connects each active receiver's all-bag signed error exactly to its actual register count minus the selected ideal mean. `wireFlowLayer_register_error_sum_le_source_count_error` then aggregates over every interior receiver in the layer and charges each source coarse count error only once. These results are axiom-guarded. `profileIntervalMean_bounds` and `wireFlowReceiverSelectedIdealMean_bounds` prove that each selected target lies between zero and the receiver capacity, using the exact selected-piece capacity sum. Thus heterogeneous port means define a valid next threshold target. `profileIntervalMean_mono_mean` and `wireFlowReceiverSelectedIdealMean_mono` prove that monotone source target profiles induce monotone receiver targets, including across integer-floor changes. `wireFlowLayer_register_error_sum_le_source_count_error_multi` sums the fresh errors across all interior bag levels and any finite threshold family without a level or port factor. `realTarget_has_integer_fraction` re-encodes every bounded receiver target in the strict `q < capacity`, `frac ? [0,1]` form needed at the next layer. Still open: establish the source profile invariant from the scheduler and prove rank-energy contraction through merge/deal. |
| `PacketMergeAxioms.lean` | Compile-time axiom guards for the headline local results. Only `propext`, `Classical.choice`, and `Quot.sound` are permitted by the checked messages. |

`PacketHalfProfile.lean` also proves the exact phase-specific doubled-energy
baseline `oddEvenMerge128_physicalHalf_doubledEnergy`. The finite heuristic
files `alternating_chain_screen.py` and `alternating_chain_128_screen.json`
record a 14-layer candidate sorting two chains on alternating 128-wire
support, checked across all 4,225 Boolean threshold inputs. This is not a
Lean theorem or an optimality result; see `GRANULARITY-GATE.md`.

The active selectors now have an exact interior-source partition theorem:
for source levels `2 ≤ l` and `l + 2 ≤ d`, every one of the 66 sender rank
pieces is assigned once among active receivers. Consequently their additive
ideal piece means sum exactly to `q(source) + frac(source)`, including empty
and full endpoints. For `d ≥ 3`, the boundary partition is also explicit:
levels 0–1 route pieces 1–64, while levels d−1 and d route only pieces 0 and
65. Their missing fringes/middle pieces remain boundary terms whose
startup/termination cost must still be bounded.

The actual omitted-profile error is now bounded by the same capacities:
summed low-fringe error is at most the sum of source up-flows, and summed
upper-middle error at most the sum of `64 * down`. Root fringes and leaf
middle pieces have zero error by the flow boundary conditions, leaving only
level 1 and level `d−1` terms to charge over time.

The correction proof uses adjacent physical wires. It combines the checked
min/max execution identities with the parity front's sortedness, same-rank
order and two-position shift. The terminal pair uses the unchanged final odd
wire. The earlier attempts to identify an infinite extended output sequence
are no longer needed for correctness, although the independent extension
lemma remains proved.

The parent-port correction has a new checked interface:
`parallelDownSetEndpointRepair_exists` takes the packet-grid shift, a child
cut length divisible by 64 and at least 64, and an endpoint-in-register bound.
It constructs all 64 disjoint endpoint repairs in six layers and proves each
repaired support is sorted from the sender's packet-sorted invariant. This
formalizes the per-cut correction family; it does not yet show that the
resulting partial supports plus aligned interior cells form the complete
receiver packet layout for every actual `FlowSizes` node.
`flowA7_scheduled_parent_endpoint_repair` instantiates this result for every
ordinary scheduled sender with positive down-flow and a half-misaligned
up-fringe. The zero-down boundary case has no child cuts and remains a
separate no-op case. The dual `flowA7_receiver_child_up_endpoint_repair`
handles all 64 children of a receiver in one disjoint six-layer family when
their common up-fringe is half-misaligned; it uses the actual scheduled
packet-cardinality and wire-set disjointness theorems. Both scheduled cases
still assume each contributing sender has the packet-sorted invariant.
For parent down-ports, `downSetEndpoint_partition` and
`parallelDownSetEndpointRepair_packetLayout` now prove that the corrected
endpoint pair plus the untouched interior cells form a partition into sorted
64-wire packets. `flowA7_scheduled_parent_endpoint_packetLayout` carries this
through to actual ordinary senders. The child up-port has not yet been given
the corresponding full packet-partition theorem, and the parent/child packet
families have not yet been united into the receiver's complete layout.

## Reproduction

From this worktree's repository root on Windows:

```powershell
powershell -NoProfile -ExecutionPolicy Bypass -File upper-bound/experiments/packets/check-lean.ps1
```

The script builds the required `StageNet`, `ExecPlacement`, and `Untangle` library modules,
then checks the scratch modules in dependency order. Scratch `.olean` files
and logs go to `LLM-helpers/ub25-packets`, outside tracked proof sources.
`-From PacketRepair64`, `-From PacketGenMerge`, or `-From PacketMergeAxioms`
is an incremental development option and assumes earlier scratch imports
were already rebuilt after their latest source changes. The default command
checks all scratch sources.

## Remaining proof gates

1. Carry cut-local packets into global matching rounds
   The checked six-layer shared source-port repair is selected on every
   eligible bag and embedded by `stageNet`; the global stage has depth at most
   six. `flowA7_sourcePortRepairStage_layout` applies the input invariant and
   transports every endpoint, interior, and fringe support through the stage.
   `flowA7_sourcePortRepairStage_downCutFamily` packages every actual child
   down-cut as a disjoint exact cover by sorted 64-wire supports. Still missing
   is identifying the evolving cut-local families with global packet IDs,
   matching edges, and receiver register capacities.
2. Carry the logical packet embeddings through matching rounds and positional
   port cuts. `PacketSortedOn` on the physical rank grid is a sufficient local
   premise, not yet an invariant of that combined scheduler. In particular,
   the six-layer repair sorts crossed supports `suffix_i ∪ prefix_(i+1)`, so
   it does not by itself order the two halves of each same-grid packet after
   execution. The generalized
   join/deal interface avoids a physical interleaving cost, but it still needs
   a full evolving placement map compatible with the scheduled flow. A generic
   matching-round network is now checked: `genPacketRound` runs the seven-layer
   merge on every pair in a list of pairwise disjoint 128-wire embeddings;
   each pair's even/odd outputs remain sorted after the whole network,
   the `genPacketRound_outputPackets` list is pairwise support-disjoint and
   covers exactly the consumed support union, and the network depth is at most
   7. The output list is therefore a valid next-round sorted packet family.
   `genJoinMatching` constructs those supports from explicit embedding pairs.
   More directly, `genIndexedPacketRound` takes a matching edge list on packet
   IDs and an indexed family of disjoint packet embeddings. It proves the
   seven-layer depth, sortedness and pairwise support-disjointness of every
   dealt output packet, and exact support coverage of the matched packets; the support construction attaches each
   endpoint-disjointness proof to its edge. This closes the abstract packet-ID
   adapter. Still missing are the concrete matching schedule extracted from
   the positional `WireFlow` cuts, treatment of unmatched packets in the full
   family, and compatibility of its evolving placements with later cuts.
   As a first concrete instance, `adjacentPacketMatching` gives a perfect
   matching on every even-sized packet-ID family; its no-self-edge,
   vertex-disjointness, coverage, and duplicate-free properties are checked.
3. Supply an unbounded matching family and a uniform rounded-discrepancy bound,
   including exceptional small cohorts. Finite mixing screens do not prove
   this.
4. Close the coupled bag-mean/rank and within-bag variance recurrence across
   the actual selected port fragments and rebinning. The existing tiny-error
   Chvatal invariant cannot simply be reused with the screened packet errors.
   The actual 65-cycle and its exact executed count formula are checked for
   the shifted positive-down sender. They remove its fresh boundary repair
   energy defect. Adding unchanged packets, destination regrouping, the
   degenerate cases, and coarse target drift remain.
   [GRANULARITY-GATE.md](GRANULARITY-GATE.md) records why 4096-packet count
   variance cannot simply be reused as 64-cell variance, and gives a
   sorted-profile L1 transfer estimate to investigate instead.
5. Prove final output order and sorting, apply `Untangle.untangle` to the full
   generalized network, and account for ordinary/frontier/root/terminal depth,
   arbitrary input sizes and the limsup passage.

The number 197.5 is still a conditional cost model:
`(26 * 13 + 57) / 2`. The six-layer local repair and generalized local merging
remove local obstacles; they do not establish the 57-layer receiver budget,
the scheduler's two-bit scale rate, its global quality invariant, or a new
limsup theorem. The full UB-25 construction remains a research lead.

See `MIXING-TAIL.md` for the detailed mathematical history and recurrence
interfaces; this README supersedes its historical statements that the
64-wire odd-even sorting theorem remains open.

The rank-profile obstruction is now explicit: `oddEvenMerge128_physicalHalf_counts` gives the exact clamped counts in the two positional 64-rank cells after a full 128-wire merge. At threshold total 64, `oddEvenMerge128_balanced_deal_vs_physical_halves` proves the physical halves have counts `(0,64)` while the logical even/odd deal has `(32,32)`. `oddEvenMerge128_balanced_inputs_shift_physical_profile` makes this mismatch concrete from two balanced, sorted input packets: physical counts shift from `(32,32)` to `(0,64)` in one merge. A global recurrence must track both rank-profile state and logical-packet state; packet variance alone cannot represent the fixed positional cuts.

`oddEvenMerge128_physicalHalf_doubledEnergy` now kernel-checks the phase-specific baseline: for total threshold count `H`, the two physical halves have doubled centered energy `2*min(H,128-H)^2`. `GRANULARITY-GATE.md` compares this with the logical even/odd packet energy, explaining why a recurrence must correct for the deterministic profile shift before comparing variances.

Temporal frontier accounting (2026-10-15): the actual schedule eliminates the entire high-frontier omitted-middle error at every ordinary stage; level d-1 is inactive and the leaf down-flow is zero. The remaining level-1 up-flow has a formal per-bag time sum bounded by (64/63) * 64^(d-5), from a ratio-1/64 capacity tail. Across 64 level-1 bags this predicts total charge (64/63) * 64^(d-4), about 6.05e-8 of all 64^d wires; the bag-cardinality multiplier is formalized in Lean. This proves a small boundary budget, not a recurrence: sortedness preservation and rank/variance contraction remain open. See MIXING-TAIL.md.


PacketGenMerge.lean now has a checked pairwise energy theorem: a merge-and-deal pair cannot increase the two threshold counts' centered squared error from any real target. This closes a local mixing inequality; uniform global contraction still requires a bounded-degree matching/expander family.

Aligned port packet families (GPT-6.1-astra-high, 2026-10-15): `alignedUpRepairPacket` splits a packet-aligned up-set into prefix and suffix 64-rank cells, while `alignedDownRepairPacket` indexes the consecutive cells of each aligned down-cut. Their union, pairwise disjointness, and exact 64-wire cardinality are checked, and sortedness follows directly from the sender's `PacketSortedOn` invariant when the port origins are aligned. The focused chain through `PacketMergeAxioms` passes with guards. This closes the static aligned partition lemmas, but not yet their uniform instantiation after the correction stage, nor the zero-flow receiver boundary case.

The actual aligned no-repair case is now instantiated. For positive down-flow, both actual port-side theorems prove sortedness after the six-layer stage, exact port coverage, disjointness, and 64-wire packet size. The zero-down up-port is handled separately as the full sender register, avoiding a false assumption that its half-fringe is packet-aligned. `flowA7_receiver_aligned_packetAssembly` combines the aligned parent cut and all 64 aligned child up-ports into the next receiver's sorted packet partition. The focused Lean chain compiles this result; the remaining receiver cases use a repaired parent or child, or an empty parent port.

The two positive-flow mixed cases are now instantiated as well. When the parent fringe is shifted, `flowA7_receiver_repairedParent_alignedChildren_packetAssembly` combines its repaired cut with the aligned child ports. When the child fringe is shifted, `flowA7_receiver_alignedParent_repairedChildren_packetAssembly` combines the aligned parent cut with all repaired child up-ports. Both return canonical `Fin`-indexed packet families: the endpoint-repair `Unit` indices are transported along finite-type equivalences, leaving packet IDs ready for the indexed matching-round adapter. The generic `flowA7_receiver_packetAssembly_fin` performs this reindexing while preserving all partition contracts. `flowA7_receiver_parentPort_canonical` and `flowA7_receiver_childPorts_canonical` now package all zero/aligned/repaired modes into common finite families, and `flowA7_receiver_allCases_canonical` assembles every combination into a canonical partition of the next register. The remaining induction gap is to propagate those packet IDs and rank placements through the concrete matching schedule and into the next layer's port cuts.

Zero-flow sides now have reusable receiver adapters. A zero parent down-flow gives an empty selected parent cut, which composes with any certified child-port family. If the child down-flow is zero, each child up-port is its entire sender register and its original 64-cell grid supplies the packets; this composes with any certified parent cut. These adapters pass the guarded focused chain. All aligned/repaired/zero-side port contracts are available, though a single theorem combining every case and the later global matching-round induction remain open.

The current 4096-to-64 output interface is stronger than support conservation:
`PacketHalfProfile.lean` proves that every 64-wire chunk emitted by the
57-layer 64-run merge has exactly the ideal rank profile of the merged
threshold count. The unresolved transition is its identification with the
next scheduler's physical positional cuts.
The exact merge-output profile theorem has also been lifted to arbitrary
ordered inputs at every value threshold, using comparator/threshold
commutation. This supplies the profile interface needed by the recurrence;
identification with next-stage physical cuts is still open.

The divisible-64 receiver path now also carries exact threshold profiles
through its parallel 57-layer merge batch, composed with the actual correction
stage. The receiver's 63-packet remainder and cross-stage physical-cut
identification are still open.
The `flowA7` divisible-64 receiver wrapper now returns exact threshold
profiles for every merged rank packet, together with sortedness and the
57-layer bound. The residue-63 tail and next-stage physical-cut alignment
remain open.

The local threshold-profile lemma is now parameterized by the number of
64-wire output cells, so the 63-run unequal merge has the same exact profile
interface as the 64-run full merge.

Current follow-up (2026-10-16): the actual receiver packet-count residue is
uniformly 0 or 63, and exact threshold profiles are now proved through both
the divisible full-block batch and the residue-63 full-plus-tail batch.
Grouped 64-run output chunks are proved to preserve their exact source support;
this is lifted all the way to the actual divisible receiver's next-stage
`wireSets`. The residue-63 receiver's full blocks and tail are also proved to
cover its next-stage `wireSets`; the generic full-plus-tail output-support
theorem carries that union through the merge. The critical identification of
logical rank packets with the next fixed physical `WireFlow` cuts remains
open. Consequently there is still no global rank-profile recurrence or
improved limsup coefficient.

The next algebraic interface has been formalized in
`monotoneCountDecomposition_L1_exact` and `assignedRankProfiles_L1_exact`:
for any assignment of each sorted packet rank to a destination, the aggregate
L1 error of the induced scattered rank subsets is exactly the coarse packet
count error, as long as selected suffixes are nested and have the right total
size. The next step is to define those assignments from actual merge-output
wire embeddings and `WireFlow` ports, then connect the resulting counts to the
global receiver recurrence.

The next algebraic layer is also checked: `assignedRankProfiles_aggregate_L2`
and `_var` bound the destination-wise squared signed errors by `c` times the
source packet-count energy, including packet-dependent fractional targets.
This gives a quadratic aggregation inequality compatible with the existing
source-dependent `WireFlow` means. It is still an abstract rank-owner result;
the actual embedding-to-receiver owner map and its active-level energy sum are
not yet proved, so it does not establish a limsup improvement.

Follow-up (GPT-6-astra-high, 2026-10-16): the owner-map bridge is bypassed for
the one-layer recurrence by using the actual `wireFlowLayerSelection`
geometry directly. `wireFlowLayer_register_error_sq_sum_le_source_energy`
and its multi-threshold version prove the active-level squared-error sum is
at most 65 times the preceding source energy. The re-encoded form
`wireFlowLayer_reencoded_profile_energy_recurrence` additionally supplies
monotone, capacity-valid next target codes. This corrects the previous
"active-level energy sum not yet proved" status for that recurrence, but it
does not provide contraction through merge/deal or a limsup coefficient.
The remaining essential gap is a global quantitative mixing estimate for
the actual matching schedule, coupled to routed profile error.

`PacketGenMerge.lean` now also proves the heterogeneous-target form of the
pairwise energy decrement. If source packets carry different targets, assign
both dealt outputs the average target; the exact decrement is controlled by
the squared difference of the two source errors, minus the one-half rounding
allowance. The result is summed over any parallel matching and instantiated
on the actual 128-wire merge-and-deal network, with standard axioms only.
This gives the correct local potential for a moving target profile. To use it
globally, the scheduler must evolve those targets by the same matching
averages, which is not yet proved for the selected-interval recurrence.

`genScatterMergeTree_output_threshold_profile_L1_exact` also proves that a
sorted 4096-wire cohort merged into 64 output packets redistributes its
fractional rank-profile error with exact aggregate L1 conservation. This
removes reassembly as a source of fresh error in that local model; the
remaining challenge is carrying the induced logical rank order into the next
physical scheduler cuts.

The local transfer now also accepts heterogeneous fractional targets on the
64 input packets: `packetPowerTree6GroupNet_heterogeneous_profile_error_le`
bounds the output aggregate L1 profile error by the sum of the input count
errors whenever the target means sum to the batch mean. Its Lean axiom guard
passes in `PacketMergeAxioms`. The global scheduler still needs to align these
logical output packets and targets with the next physical cuts.
