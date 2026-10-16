# UB-25 packet proof workstream

Current local proof checkpoint: 2026-10-15, Codex (GPT-6).

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
| `PacketRepair64.lean` | An input-independent ordinary network repairs two physically separated 32-wire supports in six layers. Actual shifted down-cut/up-fringe fragments are sorted under `PacketSortedOn`, which orders each packet but imposes no inter-packet value order. Disjoint repair families have depth at most six and act as the corresponding local merger on each pair. `flowA7_sourcePortRepairStage_depth_le` chooses the shared-port repair on every eligible source bag and composes these networks through the actual `stageNet`, preserving the six-layer depth bound globally. `flowA7_sourcePortRepairNet_layout` lifts the chosen Boolean repair contract to arbitrary linearly ordered values by thresholding. `flowA7_sourcePortRepairStage_layout` starts from packet-sorted values on the actual sender bag and proves every designated endpoint, interior, and fringe support is sorted on its physical-wire image after correction. `blockOf_register_image` identifies register rank intervals under the bag embedding with the matching actual `WireFlow.blockOf` intervals. Identifying the complete support partition with the next stage's packet family and closing the receiver recurrence remain open. |
| `PacketGenMerge.lean` | An arbitrary injective placement of an ordinary network preserves execution and depth in `Untangle.GenNetwork`. `genMerge_sorts_two_runs` and `genMerge_depth_le` apply at every power-of-two width, including seven layers for 64+64 packets and thirteen for 4096+4096. Dealing has exact floor/ceiling counts, including all value thresholds. Logical packet embeddings can be joined and their fixed parity outputs are disjoint and partition the consumed support. |
| `PacketRebinning.lean` | The scalar complementary-half rebinning model preserves counts and cannot increase positive/negative spill or squared energy around any common real reference. |
| `PacketSenderCycle.lean` | The 65 shifted boundary cells are distinct whole source packets. Actual child and parent repairs consume complementary halves in a fixed cycle and cover exactly those cells. A fixed ordinary six-layer network sorts all 65 repaired pairs and leaves other wires unchanged. `scheduled_senderRepair_exists` instantiates this on actual ordinary scheduled bags with positive down-flow and shifted half-fringes. |
| `PacketCountBridge.lean` | Enumeration-independent true counts, exact prefix/suffix counts of sorted packets, and pairwise count conservation through parallel execution. `senderRepair_count_exists` gives one fixed six-layer network with sorting, exact cycle counts, sender-centered squared-energy nonincrease for every real reference, and unchanged wires outside the boundary cells. `senderRepair_count_at_threshold` transfers its Boolean count contract to all value thresholds of that same network. This is a local sender result, not a destination or global recurrence. |
| `PacketProfile.lean` | Kernel-checked sorted Boolean packet profile for 4096-wire packets split into 64-wire cells. Actual cell counts have the ideal clamp formula. Across any cohort and fractional common mean, aggregate cell-profile L1 error equals the coarse packet-count L1 error exactly; its square is bounded by cohort size times coarse squared error. Connecting this profile to scheduler ports and destination reassembly remains open. |
| `PacketHalfProfile.lean` | Checked clamp-profile and exact L1 / squared-error transfer for 32-wire halves and arbitrary rank intervals. It identifies actual `WireFlow.blockOf` counts with ideal profiles, and the 66 rank pieces (64 child blocks plus both parent-fringe halves) of each sender form a packet-specific partition. Heterogeneous sender sizes and per-sender means are allowed. `wireFlowReceiver_count_error_actual` instantiates the 65-source parent/children pattern on actual `wireSets` and flow sizes, assuming each sender's post-stage threshold profile is sorted. `wireFlowReceiver_selected_count_eq_register` proves the selected source-piece counts equal the threshold count in the actual `execPlacement` receiver register, using injectivity and disjointness. The corollary `wireFlowReceiver_register_count_error_actual` bounds that register's discrepancy from the selected source-profile means by the sum of the source count errors. The finite-type `sum_receiver_profile_errors_le_source_count_errors` is instantiated on all `KBag 64 d` bags by `wireFlowLayer_profile_error_sum_le`; `wireFlowLayerSelection` has a checked range bound and pairwise disjointness for the actual parent/child piece routing, with root fringe routing excluded. `wireFlowLayerSelection_receiverSource` matches the global selector with the local selector on every receiver neighbor; `wireFlowLayerSelection_eq_empty_of_not_neighbor` and `wireFlowLayerSelection_receiverSum_eq` prove support and exact source-sum reindexing onto its 65 actual neighbors. `wireFlowLayer_receiver_signed_error_eq_register` connects each active receiver's all-bag signed error exactly to its actual register count minus the selected ideal mean. `wireFlowLayer_register_error_sum_le_source_count_error` then aggregates over every interior receiver in the layer and charges each source coarse count error only once. These results are axiom-guarded. `profileIntervalMean_bounds` and `wireFlowReceiverSelectedIdealMean_bounds` prove that each selected target lies between zero and the receiver capacity, using the exact selected-piece capacity sum. Thus heterogeneous port means define a valid next threshold target. `profileIntervalMean_mono_mean` and `wireFlowReceiverSelectedIdealMean_mono` prove that monotone source target profiles induce monotone receiver targets, including across integer-floor changes. `wireFlowLayer_register_error_sum_le_source_count_error_multi` sums the fresh errors across all interior bag levels and any finite threshold family without a level or port factor. `realTarget_has_integer_fraction` re-encodes every bounded receiver target in the strict `q < capacity`, `frac ? [0,1]` form needed at the next layer. Still open: establish the source profile invariant from the scheduler and prove rank-energy contraction through merge/deal. |
| `PacketMergeAxioms.lean` | Compile-time axiom guards for the headline local results. Only `propext`, `Classical.choice`, and `Quot.sound` are permitted by the checked messages. |

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

1. Integrate the checked six-layer shared source-port packet-layout network
   The checked six-layer shared source-port repair is now selected on every
   eligible bag and embedded by `stageNet`; the resulting global stage has
   depth at most six. `PacketSortedOn_orderEmb` transfers the input invariant
   into register coordinates, and `stageNet_rankSortedOn_image` transports
   local sorted supports back to global wires. Still missing is applying this
   pair of adapters to the selected repair's complete output layout, then
   identifying those source-rank cells with fixed receiver packet labels and
   capacities.
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

Temporal frontier accounting (2026-10-15): the actual schedule eliminates the entire high-frontier omitted-middle error at every ordinary stage; level d-1 is inactive and the leaf down-flow is zero. The remaining level-1 up-flow has a formal per-bag time sum bounded by (64/63) * 64^(d-5), from a ratio-1/64 capacity tail. Across 64 level-1 bags this predicts total charge (64/63) * 64^(d-4), about 6.05e-8 of all 64^d wires; the bag-cardinality multiplier is formalized in Lean. This proves a small boundary budget, not a recurrence: sortedness preservation and rank/variance contraction remain open. See MIXING-TAIL.md.


PacketGenMerge.lean now has a checked pairwise energy theorem: a merge-and-deal pair cannot increase the two threshold counts' centered squared error from any real target. This closes a local mixing inequality; uniform global contraction still requires a bounded-degree matching/expander family.
