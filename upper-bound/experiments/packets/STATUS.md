# UB-25 packet-balancing status

Current local proof checkpoint (2026-10-15, Codex / GPT-6): the full
power-of-two odd-even merge correctness proof is now kernel checked, including
the 64-wire six-layer theorem. Fixed separated half-packet repair, its
packet-sorted input adapter, and parallel repair families are also checked.
The generalized-comparator adapter merges arbitrary interleaved sorted
64-wire packet supports in seven layers and proves the exact Boolean
floor/ceiling count law. The new [README](README.md) is the current proof map
and gives the reproducible check command and remaining obligations. The
global sorting bound and the projected coefficient near 200 remain open.

Physical merge-tree layout follow-up (2026-10-16): in addition to sortedness,
the 4096-wire merge now has a checked and axiom-guarded physical-order
interface. Ordered disjoint 64-wire input packets induce an increasing group
embedding; every output packet remains internally increasing, and distinct
output packets remain globally separated in index order. A corresponding
input-order lemma is proved for the 63-packet residue group. This removes the
layout-permutation gap between consecutive merge-tree applications when the
incoming packet family already has separated physical supports. That incoming
premise is still not established by the full `WireFlow` induction, and no
target contraction or global coefficient improvement follows yet.

Further checkpoint: `PacketRebinning.lean` proves exact scalar count
conservation and nonincrease of spill and centered quadratic energy under
complementary-half rebinning. `PacketSenderCycle.lean` and
`PacketCountBridge.lean` now prove the actual shifted sender's 65-cycle,
exact executed count identity, simultaneous six-layer sorting, unchanged
outside wires, and zero fresh sender-relative repair energy. The count
contract transfers to every value threshold of the same fixed network.
Whole-source and destination packet partitions, degenerate cases and the
remaining coarse/fine recurrence are still open. `GRANULARITY-GATE.md`
isolates the change-of-scale gap between 64-wire repair cells and the
4096-wire mixing cost model. `PacketProfile.lean` now proves each actual
64-wire cell count of a sorted 4096-wire Boolean packet equals its ideal
sorted-profile value. At any fractional common mean, the aggregate L1 error
across cells and packets equals the coarse packet-count L1 error exactly;
the squared version is bounded by cohort size times coarse squared error.
Placing the ideal profile into the global rank target and destination
recurrence remains open.

`PacketHalfProfile.lean` now gives the same checked exact-L1 and cohort
squared-error transfer for actual 32-wire halves of sorted packets, matching
the units consumed by local repair. The focused Lean check and axiom guards
pass. This removes the granularity mismatch in the profile estimate only;
selected-port discrepancy and destination reassembly recurrence remain open.
The same module now identifies the count in any fixed half-open rank interval
of a sorted packet with its ideal profile and proves that this interval count
is 1-Lipschitz in the total packet count. More strongly,
`sortedPackets_individualIntervalPartitions_L1_exact` allows each sender
packet its own cut sequence and still gives exact aggregate L1 conservation;
`_L1_sq` gives the cohort-size quadratic bound. This removes port-count
amplification at the abstract partition interface. Instantiating full rank
partitions from all actual outgoing WireFlow contributions and carrying
slice targets through receiver reassembly remain outstanding.
The new `trueCountOn_blockOf_profile` and
`sortedSenderOutgoing_profile_error_exact` results close that sender-side
instance: the 64 child down-blocks plus both parent-fringe halves are the
actual 66 rank intervals, and their aggregate L1 profile error is exactly
the coarse sender-count L1 error, with no port-count factor. Receiver-side
target summation, matching contraction and reassembly remain open.

Heterogeneous sender follow-up (2026-10-15): `PacketHalfProfile.lean` now
also proves `sortedSenderOutgoing_profile_error_exact_var` and
`selectedSenderOutgoing_profile_error_le_var`. The source bags may have
different sizes, and each sender may use its own fractional ideal count; the
66-piece L1 identity and selected-subset bound still hold exactly. This fits
the parent/child size asymmetry in actual `WireFlow`. The receiver's required
ideal profile is still not identified with the sum of selected source ideals,
and no reassembly contraction follows yet. The full scratch chain and axiom
guards are checked by `check-lean.ps1`.

Receiver-input count bridge (2026-10-15):
`selectedSenderOutgoing_count_error_le_var` proves that, for any receiver
selection of source rank pieces, its combined Boolean threshold count differs
from the sum of the selected source-ideal interval counts by at most the total
coarse sender count error. It allows heterogeneous bag sizes and sender means
and incurs no factor for the number of incoming pieces. This is the error term
to feed into a local multi-run merge/deal estimate; identifying the selected
ideal sum with the correct destination target is still open.

Receiver-shape specialization (2026-10-15):
`wireFlowReceiver_count_error_le` encodes the scheduler's selection pattern
with 65 sources: one parent contribution at a chosen down-block index and both
up-fringe halves from each of 64 children. It inherits the no-port-loss count
bound for unequal source sizes and means.

Actual source-set instantiation (2026-10-15):
`wireFlowReceiver_count_error_actual` chooses those 65 sources from the real
`wireSets F t` via the receiver's parent and children, and derives source
capacities and even up-flows from `FlowSizes` and `wireSets_inv`. It applies to
post-stage Boolean thresholds `predicate ∘ X(t+1)`, assuming the sender values
are rank-sorted. The subsequent `wireFlowReceiver_selected_count_eq_register`
proves that these selected counts equal the threshold count on the actual
`execPlacement` receiver register, using injectivity and disjoint source bags.
The corollary `wireFlowReceiver_register_count_error_actual` therefore bounds
the receiver's discrepancy from the selected source-profile means by the sum
of the 65 source count errors. This is kernel-checked. The next unresolved
step is to identify or bound that selected ideal total against the receiver's
target profile in a coupled recurrence; sender rank-sortedness and any
multi-run merge/deal contraction also remain separate obligations.

Layerwise aggregation (2026-10-15): `sum_receiver_selected_errors_le_source_pieces`
and `sum_receiver_profile_errors_le_source_count_errors` prove an abstract
finite-layer contraction: if each source rank piece is routed to at most one
receiver, the sum of receiver absolute errors is at most one coarse count error
per source. This removes multiplicity loss in the mathematical recurrence,
conditional on a scheduler incidence partition. It does not yet instantiate
the actual all-receiver WireFlow schedule or establish the target-mean update.

The entries below retain the research history and their original claim levels.

Resumed by Codex (GPT-6), 2026-10-14. Branch/worktree:
`ub-25-packets` / `.claude/worktrees/ub-25`.

The local merge-and-deal primitive remains screened. A new conditional
spectral-cycle lemma bounds each output packet's cohort by
`H*(1/c+rho)+s/2` and gives a bulk leakage estimate; finite random matching
screens look promising through 256 packets. The unbounded matching family and
global port-flow remain open. No whole-network depth improvement exists.
Previous parked checkpoint: `1d52a55`.

## First question

Can a fixed binary comparator network take two sorted packets of length
`m=2^q`, merge their values, and deal alternate merged positions into two
sorted output packets while preserving the exact Boolean threshold-count
identity

```text
(x,y) -> (ceil((x+y)/2), floor((x+y)/2))?
```

The candidate is reverse the second packet, apply a bitonic merge on `2m`
inputs (at most `q+1` layers), then track the fixed even/odd output layout.
The layout permutation is part of the interface and must be charged or
absorbed by the global routing/untangling proof; it is not free physical
routing.

## Status

The checked source provides `Bitonic.bitonicMerge_sorts` for `Window` Boolean
inputs and `Bitonic.bitonicMerge_depth_le`. Reversing the second sorted packet
makes the concatenation a `Window`; after merging, the even and odd
subsequences are sorted and their false counts are the ceiling and floor of
half the total. This gives the local identity at hand-proof level, conditional
on the existing theorem. The independent simulator passed all 22,363 pairs
of sorted Boolean packet inputs through q=7.

At the initial checkpoint, no Lean adapter theorem or matching schedule had
been added. The fixed
deal layout must be carried through the whole generalized network and its
final target order before `Untangle.untangle` applies. Separately, a matching
cycle still needs a useful contraction and a rigorous rare-cohort tail. There
is an exact limitation: a total cohort count of one stays in one packet under
every merge-and-deal matching, since `(1,0)` maps to `(1,0)`. UB-25 therefore
needs the scheduler to tolerate bounded rare cohorts as explicit fringe mass
or add a mechanism beyond pure packet averaging. The q=12/30-round/195 figure
remains only a depth gate from the proposal. See `MERGE-DEAL.md` for details.

Claim level: `conjecture` for the full UB-25 construction; the local count
identity is `hand-proof` conditional on source theorems and `simulation` for
the finite executable check.

Follow-up arithmetic screen: for packet size 4096, the `mid` and `botDesc`
down-block lengths are exactly packet-aligned; their half-fringes are aligned
except at exponent 0 (residue 4064). `topRise` half-fringes align from
exponent 1 (the exponent-0 case is 2048). This weakens the earlier raggedness
concern for bulk nodes, but does not establish sorted packet order or price
the many-run receive. Exact formulas and next gate are in `MIXING-TAIL.md`.

Scheduler audit (2026-10-14): the proposed 64-fragment receive is not the
checked Chvatal flow. Each child receives one variable-size positional
`downSet` block from its parent and the union of up to 64 child `upSet` tails;
the flow proves wire counts, not sorted-run structure. The 57-layer reassembly
and 197.5 gate therefore have no current scheduler realization. See the
port-flow audit in `MIXING-TAIL.md`. First test a scheduler-shaped port
instance before investing in an unbounded matching-family certificate.

Concrete ordinary port instance now passes: at `d=20,t=20`, a level-7
receiver gets one aligned parent packet interval and two aligned fringe
intervals from each of 64 children. Exact packet-count conservation matches
its `mid(g=4)` capacity; see the script and JSON listed in UB-25 evidence.
This suggests no comparator-based repacking is needed in bulk if packet
labels can be carried across placements. The fixed-label proof and frontier
cases remain unproved.

Follow-up: a hand case split of the six `NodeShape` formulas now gives the
uniform 4096-residue table, using `exp_top` for `topDesc` and the omega-frontier
schedule inequalities for `botRise`. Every individual port interval therefore
cuts at most two packet boundaries under the assumed packet ordering. This is
not yet a Lean lemma, and it does not prove that partial packet pieces remain
bounded through repeated stages; merge-and-deal needs equal-size packets.
Details are in the final section of `MIXING-TAIL.md`.

New packet-size screen: at 64 wires per packet, every scheduled bag and
down-block is aligned modulo 64; each up half-fringe is aligned or exactly
half a packet off. That gives at most 128 half-packet fragments per receiver
in the finite schedule screen, repairable by 64 parallel 64-wire merges in
six layers. The resulting conditional local cost is 188 layers per ordinary
node operation, or coefficient 94 under the old 3d operation rate. However,
the rounded-cycle bulk leakage floor is about 10%, so this packet size may
fail the quality invariant. Precision versus repair depth is the next gate.
See `packet64_repair_screen.py` and its JSON.

Finite frontier screen: exact rational enumeration for `7 ≤ d ≤ 40` checked
1,650 ordinary stages and 5,900 active bags; all receiver flow identities
held. The only nonzero residues modulo 4096 were 4032 for bag/down sizes and
2048 or 4064 for up half-fringes. This supports a whole-packets-plus-one
terminal-fragment invariant with at most two boundary fragments per interval,
but is not a universal proof. See `frontier_alignment_screen.py` and its JSON.


Uniform 64-wire alignment case audit (2026-10-14): each RefinedNodeShape case gives 64-divisible bag and down-block sizes and up half-fringe residue 0 or 32. For topDesc, exp_top/exp_nontop rule out small down-block exponents. The interval residue and boundary-fragment count are still hand-checked.

The finite screen checked 46,926 receivers and observed at most 128 fragments. A symbolic argument shows parent and child half-fringe misalignment cannot coincide, so the schedule-level maximum is 128 rather than the crude 130.

Lean adapter (2026-10-14): PacketAlignment.lean contains a refined copy of shape_rat retaining the botRise exponent witness, specializes it to actual integer flows, and proves scheduled_receiver_no_simultaneous_misalignment for all ordinary stages. refined_packet_residues proves packet divisibility and half-fringe residues. blockOf_rank_image proves the actual Finset wire block maps bijectively by rankIn to its exact half-open rank interval; downSet_rank_image and upSet_rank_images specialize this to WireFlow ports. downSet_boundary_fragments and upSet_boundary_fragments derive the exact 0-or-2 partial rank-packet counts. receiver_fragment_budget gives the 128 arithmetic budget. RankSortedOn and parentPart/childPort corollaries show each contribution remains sorted, conditional on its sender bag being sorted by wire index. bitonicMerge64_sorts_two_runs now proves that the 64-wire bitonic merge sorts two arbitrary ascending 32-wire runs when the second is reversed; bitonicMerge64_depth_le gives depth <=6. The focused scratch Lean check passes in upper-bound/best. Still open: prove the packet scheduler establishes the sender-order invariant, pair/place all fragments in parallel through fixed wire labels, and close selected-fragment discrepancy plus rebinning variance.

Fixed-placement gate audit (2026-10-14): wireSets_succ_eq and execPlacement_succ_regs provide unions of contributions; the existing sorted-run lemmas only order values within each sender contribution. They do not put a selected pair in fixed lower/upper 32-wire positions. Interleaving source wire sets can make the receiver's physical order unsorted even when both sources are individually sorted. MIXING-TAIL.md now records this concrete obstruction and the next gate: prove an input-independent slot map with a depth-priced implementation, or redesign the port layout. The 6-layer-per-pair estimate remains unconnected to the scheduler.

Fixed-label follow-up (2026-10-14): arbitrary interleaving does admit an input-independent local fallback: choose each pair of disjoint 32-wire fragments from the fixed flow sets, take their 64-wire union, and scatter-embed a full 64-wire bitonic sorter in increasing physical-wire order. This avoids the false contiguous-halves assumption but costs up to 21 layers, versus 6 for the bitonic merge. Replacing the 6-layer pair repair within the 395-layer gate gives a conditional 410 layers / coefficient 205, already above 200. This is only local; proving a deterministic partition into disjoint fragment pairs and compatibility of the next matching cycle with abstract packet supports remains open. See MIXING-TAIL.md.

Lean adapter added and focused check passes: bitonicSort64_scatter_sorts sorts values on any increasing embedding of 64 physical wires, and bitonicSort64_scatter_depth_le bounds the embedded full sorter by 21 layers. This proves an input-independent fixed-label fallback for a chosen 64-wire support. It does not instantiate a receiver-wide pairing partition or show that the next mixing stage consumes these abstract supports. The 21-layer fallback raises the conditional gate to 205.

Receiver pairing follow-up (2026-10-14): the boundary supports now have generic Lean card/disjointness lemmas. rankInterval_endpoint_pair builds a 64-wire support from the two ends of a shifted parent down-cut; upFringe_endpoint_pair and upFringePairSupport_card build a 64-wire support from the two half-packet ends of one child's up-fringe. scheduledUpFringePairSupport_disjoint proves supports from distinct scheduled senders are disjoint using wireSets_disjoint. This yields the natural fixed pairing: pair the two fragments from each of the 64 child senders, or the two parent-cut fragments in the exclusive parent case. Exact instantiation of all shape premises into one receiver theorem and a cheaper next-cycle adapter remain open. The ordinary 13-layer merge-and-deal is not directly scatter-embeddable on arbitrary interleaved supports. A 28-layer full-sort-and-parity fallback now gives a composable but costly transition; see MIXING-TAIL.md.

General-support next-cycle adapter (2026-10-14): bitonicSort128_scatter_sorts and bitonicSort128_scatter_depth_le certify a fixed 28-layer sort on any 128-wire union. After sorting, assigning even/odd physical ranks to the next two packet supports yields sorted packets with pairwise interleaving; sorted128_even_odd_interleave and bitonicSort128_scatter_parity_profile prove this profile. This creates a composable support transition for arbitrary disjoint packet supports, if the scheduler is redesigned to track those supports. It costs 28 rather than 13 layers per matching edge: 26 rounds cost 728 instead of 338, so with the same 57 reassembly layers the conditional estimate is 785 layers / coefficient 392.5. It is a sound invariant fallback, not competitive with 200. The open target is a cheaper support-aware merge-and-deal.

Scheduled support characterization (2026-10-14): rankInterval_endpoint_pair_ordered and upFringe_endpoint_pair_ordered now prove that the actual paired 32-wire endpoint fragments are ordered by physical wire index because they are separated rank intervals in the same sender support. Each 64-wire union therefore has ordered `A^32 B^32` support and admits an order-preserving scatter embedding. This removes arbitrary interleaving as an obstacle for the local repair pair; a 6-layer odd-even merge of two ascending runs is the new candidate adapter. Its Lean network/correctness and parity-deal composition remain to prove. The characterization is focused on the repair pairs, not arbitrary 64-wire packet matchings.

Scheduled cohort classification (Codex / GPT-6, 2026-10-15): added
`scheduled_bag_size_form`, which classifies each ordinary scheduled bag as
empty, a power of 64 wires, or a power cohort missing a factor `64^-r` with
`2 <= r <= 6`. Restoring the dropped bottom-frontier index in the refined
bottom-rising shape makes the exponent range derivable from the actual
schedule. This narrows the uniform matching problem to bounded-density padded
power-of-64 cohorts; it does not yet show padding preserves a spectral gap.
The checked corollary `flowA7_scheduled_packet_factorization` now states the
actual packet-count quotient directly as either a power of 64 or
`64^h * (64^r - 1)` for `2 <= r <= 6`.

Exact-factor matching lead (Codex / GPT-6, 2026-10-15): near-power packet
sizes are `64^h * (64^r - 1)` for one of five fixed cofactors. A diagonal
product of two matching involutions is a legal matching, but its averaging
operator is `(I + F_A tensor F_B)/2`, not the tensor product of the two factor
averages. Sequential coordinate schedules do realize tensor averaging, at the
cost of adding their rounds. A synchronized diagonal contraction without that
cost is only a conjectural route. Exact factorization is useful, but no
matching family or product spectral estimate is proved.

Receiver target re-encoding (Codex / GPT-6, 2026-10-15): `wireFlowReceiverSelectedIdealMean_has_code` composes the actual receiver-capacity bound with `realTarget_has_integer_fraction`. It proves each selected receiver mean can be carried as a legal next-stage `q + frac`, including zero-capacity receivers (`q=frac=0`) and the strict endpoint convention. Together with the actual-register discrepancy bound and threshold monotonicity theorem, this closes the target representation/coherence adapter. It still does not prove the receiver registers are sorted or that merge/deal contracts the new profile.

Receiver boundary recurrence adapter (Codex / GPT-6, 2026-10-15): `wireFlowReceiver_register_count_error_reencoded` composes the actual-register discrepancy estimate with the selected-mean encoding. For each active receiver it produces a valid next `q + frac` target and bounds its threshold-count error by the total coarse error of the 65 parent/child sources, with no port multiplicity. The focused chain from PacketHalfProfile through PacketMergeAxioms passes, including the new guard. This is now a usable one-receiver recurrence input; it still assumes sorted source registers and does not prove destination sortedness or mixing contraction.

Dynamic receiver-profile recurrence (Codex / GPT-6, 2026-10-15): `wireFlowLayer_reencoded_profile_recurrence` simultaneously chooses next `q + frac` codes for all thresholds and active receiver bags. The target is the sum of selected source interval means, is monotone across thresholds, obeys capacity and endpoint constraints, and the total actual-register error is bounded by the prior source-count error with no factor for receiver level or port count. This resolves target re-encoding by making the selected mean the next state target, rather than requiring equality to a separately prescribed target. It assumes source threshold-sortedness and proves neither the next sortedness invariant nor quantitative mixing contraction.

Parent-cut endpoint correction (Codex / GPT-6, 2026-10-15): `parallelDownSetEndpointRepair_exists` proves that when a sender has a 32-mod-64 half-fringe, each of its 64 child cuts has a fixed pair of endpoint half-packets; if the cut length is a multiple of 64, at least 64, and all endpoints fit inside the sender, these 64 repair supports are disjoint. One fixed network repairs every pair in six layers and leaves each support sorted under the sender's packet-sorted premise. `flowA7_scheduled_parent_endpoint_repair` instantiates divisibility and endpoint capacity from `refined_packet_residues` and `FlowSizes.hsplit`, for every ordinary scheduled sender with positive down-flow and a half-misaligned up-fringe. Both results have axiom guards and the focused chain through `PacketMergeAxioms` passes. The zero-down case has no child cuts and is intentionally outside this repair theorem. Proving the corrected pieces form the complete receiver packet layout remains open.

Child-fringe correction (Codex / GPT-6, 2026-10-15): `parallelUpFringeEndpointRepair_exists` groups the two endpoint half-packets of each sender in a finite disjoint cohort into one six-layer repair network. `flowA7_receiver_child_up_endpoint_repair` instantiates this for all 64 child senders of an actual receiver under a common half-misaligned up-flow; it derives packet-multiple child capacities, fringe parity, and pairwise source-wire disjointness from the checked `FlowSizes7`/`WireFlow` lemmas. This closes both scheduled endpoint correction families at the support-sortedness level. It still does not reassemble the repaired endpoint supports with each cut's aligned interior packets into the receiver's complete sorted 4096-wire packet layout, nor establish the packet-sorted invariant for the senders.

Parent down-cut packet layout (Codex / GPT-6, 2026-10-15): `downSetEndpoint_partition` exactly partitions each shifted child cut into its corrected endpoint pair and the aligned interior 64-cells. `downSetInteriorCell_sorted` identifies those interior cells with the original packet grid; `parallelDownSetEndpointRepair_packetLayout` proves the entire 64-cut repair network leaves them untouched while sorting every endpoint pair. `flowA7_scheduled_parent_endpoint_packetLayout` instantiates this for every ordinary scheduled sender with positive down-flow and half-misaligned up-flow. The full focused chain through `PacketMergeAxioms` passes with guards. This closes the sorted packet partition on each parent down-port, but not the child up-port packetization, the union of parent and child contributions into a complete receiver layout, or propagation of `PacketSortedOn` through future stages.

Child up-port packet layout (GPT-6.1-astra-high, 2026-10-15): `rankPacketCell` and `blockOf_packetCell_partition` express any aligned rank interval as its consecutive 64-cells. `upSetEndpoint_partition` proves that an up-flow `64*(2*q+1)` on a packet-multiple sender is exactly its two repair endpoints plus aligned prefix/suffix cell cohorts. `rankPacketCell_sorted`/`bounds` and the prefix/suffix endpoint-exclusion lemmas establish that these cells start sorted and lie outside all endpoint repair supports. `parallelUpFringeEndpointRepair_packetLayout` proves preservation for any disjoint cohort sharing the odd half-packet fringe, and `flowA7_receiver_child_up_packetLayout` instantiates the result on all 64 actual scheduled children. The focused chain through `PacketMergeAxioms` passes. Together with `flowA7_scheduled_parent_endpoint_packetLayout`, this closes both local port-side sorted packet partitions. It still does not identify those source-rank cells with the receiver's fixed physical 64-wire cells after placement, prove receiver assembly, or propagate `PacketSortedOn` through the scheduler.

Shared source-port packet layout (GPT-6.1-astra-high, 2026-10-15): `downSetEndpointSupport_rank_bounds` locates all 64 outgoing down-cut endpoint pairs in the sender's middle rank interval, and `downSetEndpointSupport_disjoint_upFringe` proves that region disjoint from the sender's two up-fringe endpoints. `parallelSourcePortPacketLayout` puts the 64 down-pairs and the up-fringe pair into one pairwise-disjoint family, so a single six-layer odd-even merge family repairs both interfaces while preserving all aligned interior cells. `flowA7_scheduled_source_port_packetLayout` derives its exact capacity/divisibility conditions from `FlowSizes7` and gives the complete local packet-layout statement. `flowA7_source_port_packetLayout_register` now expresses the same construction on local register indices, matching the type expected by `stageNet`. The focused axiom-guarded check passes. Selecting these local networks across all nodes, transporting the rank cells into fixed receiver packet labels, and propagating the invariant through future stages remain open. No coefficient follows yet.

Generalized matching round (Codex / GPT-6, 2026-10-15): `genPacketRound` scatters the seven-layer 128-wire odd-even merge onto every embedding in a finite list of disjoint pair supports. `genPacketRound_exec_inside` and `genPacketRound_exec_outside` prove locality for arbitrary linearly ordered values; `genPacketRound_dealt_lanes_sorted` proves every even/odd output packet stays sorted after the complete round; `genPacketRound_dealt_supports_disjoint` proves outputs from each pair are mutually disjoint and outputs across distinct pair supports remain disjoint; `genPacketRound_depth_le` proves the combined round costs at most 7 layers. `genPacketRound_outputPackets_sorted`, `_disjoint`, and `_support` package the outputs as a pairwise-disjoint sorted packet list whose union is exactly the consumed support. Each public theorem has an axiom guard, and the focused check from `PacketGenMerge` through `PacketMergeAxioms` passes. This closes the finite disjoint-pair round interface. Still open: generate these pair embeddings from a matching on packet IDs and relate the dynamically evolving packet family to actual positional `WireFlow` cuts and the full round schedule. It proves no global sorting theorem or improved coefficient yet.

Packet-edge matching adapter (Codex / GPT-6, 2026-10-15): `joinPacketEmbedding_range` identifies a joined 128-wire support with the union of its two 64-wire packet supports. `genJoinMatching` lifts an explicit edge list of packet-embedding pairs; if each edge's endpoints are disjoint and different edges use pairwise disjoint packet supports, the joined supports are disjoint and Nodup. Theorems `genJoinMatching_round_depth_le`, `_outputPackets_sorted`, `_outputPackets_disjoint`, and `_outputPackets_support` then give the full checked seven-layer round contract directly from those packet-edge premises. All new results have axiom guards; the focused chain through `PacketMergeAxioms` passes. The remaining scheduler gap is now extracting such an edge list from packet IDs / an actual matching schedule and proving those support premises through positional `WireFlow` transitions.

Indexed packet-matching round (Codex / GPT-6, 2026-10-15): `genIndexedPairSupports` constructs joined 128-wire supports directly from an edge list on packet IDs, attaching each edge's endpoint-disjointness proof. Pairwise vertex-disjointness of the edge list and disjointness of the packet embeddings imply that these joined supports are pairwise disjoint and duplicate-free. `genIndexedPacketRound_depth_le` proves depth at most seven; `_output_sorted` proves all dealt output packets sorted from the sortedness of each indexed input packet; `_output_disjoint` proves the dealt output family remains pairwise support-disjoint; `_output_support` proves the output support union is exactly the union of packets incident to the edge list, with explicit edge coverage. The focused chain through `PacketMergeAxioms` passes, including axiom guards. This closes the abstract packet-ID-to-round adapter. It does not yet handle unmatched packets, construct the concrete matching schedule from `WireFlow` cuts, carry the placement through later rounds, or yield a global coefficient.

Adjacent packet-ID matching (Codex / GPT-6, 2026-10-15): `adjacentPacketMatching k` is the canonical perfect matching on `Fin (2*k)`, pairing each even ID with its successor. Kernel-checked lemmas prove no self-edges, edge-list Nodup, pairwise vertex-disjointness, and coverage of every ID. This provides a concrete sanity instance for the indexed round adapter; it is not yet a matching on the scheduler's actual evolving packet placements and adds no global sorting bound.

Source correction stage integration (Codex / GPT-6, 2026-10-15): `flowA7_sourcePortRepairNet` selects the checked six-layer shared-port repair for each actual shifted ordinary sender and the empty network otherwise; `flowA7_sourcePortRepairStage` composes these local choices on the actual `wireSets` through `stageNet`, with `flowA7_sourcePortRepairStage_depth_le` proving a global depth bound of six. `PacketSortedOn_orderEmb` transfers the packet invariant from physical wires into each bag's register order, and `stageNet_rankSortedOn_image` transports locally sorted register supports back to global wires after stage execution. These interfaces are kernel checked with guards. The remaining correction induction is to apply them to every endpoint and interior packet support of the chosen local network and reassemble those rank cells into the receiver's next packet family.

Value-generic layout and stage induction (Codex / GPT-6, 2026-10-15): `rankSortedOn_of_thresholds` proves that sortedness of every lower-threshold Boolean profile implies sortedness for arbitrary linearly ordered values. Applying it to the Boolean-chosen shared-port network proves `flowA7_sourcePortRepairNet_layout` for the actual endpoint, interior, and fringe supports. `PacketSortedOn_orderEmb_of_card_eq` transfers packet sortedness into register coordinates using the proved physical bag cardinality. `stageNet_rankSortedOn_image_of_card_eq` handles local network indices propositionally equal to that cardinality. Together with `flowA7_sourcePortRepairStage_transport`, these results give `flowA7_sourcePortRepairStage_layout`: from packet-sorted values on an actual eligible source bag, the complete repaired endpoint/interior/fringe support family is rank-sorted on its physical-wire image after the global correction stage. The remaining induction gap is now the identification/reassembly of these output supports with the next stage's packet family and receiver rank profile. No coefficient improvement follows yet.

The map is now explicit at the rank-interval level: `rankIn_univ_eq_val` and `blockOf_register_image` show that embedding a register `blockOf` through the actual bag's increasing enumeration gives the same physical `WireFlow.blockOf`. This lets later proofs rewrite the physical images in `flowA7_sourcePortRepairStage_layout` directly to the scheduler's actual rank-cut fragments.

Child-cut packet family (Codex / GPT-6, 2026-10-15): `downSetRepairPacket` indexes one repaired endpoint pair and all untouched interior cells by `Unit ⊕ Fin m`. Its union is exactly the actual `WireFlow.downSet`, distinct supports are pairwise disjoint, and every support has cardinality 64. `flowA7_sourcePortRepairStage_downCutFamily` combines these facts with the physical stage-layout theorem: for every eligible actual sender and each of its 64 child cuts, the correction stage outputs an exact partition into sorted 64-wire packets. This supplies the concrete finite packet family for the next matching-round construction. The remaining obstruction is to join these per-cut families across senders/receivers into the global evolving packet IDs and show that the chosen matching and receiver register layout consume exactly those supports.

Parent up-set packet family (GPT-6.1-astra-high, 2026-10-15): `upSetRepairPacket` indexes the sender's corrected fringe endpoints and aligned prefix/suffix cells. These supports are pairwise disjoint, each has 64 wires, and their union is the actual `WireFlow.upSet`. `flowA7_sourcePortRepairStage_upSetFamily` instantiates this for actual scheduled senders and proves each cell sorted after correction.

Unified corrected sender family (GPT-6.1-astra-high, 2026-10-15): `sourcePortRepairPacket` combines the up-set packets and all 64 down-cut packet families under one finite index. `sourcePortRepairPacket_union`, `_pairwise_disjoint`, and `_card_eq_64` prove these are a partition of the complete sender register into 64-wire packets. `flowA7_sourcePortRepairStage_sourcePackets` proves every packet is sorted after the global six-layer correction stage. The focused chain through `PacketMergeAxioms` passes with guards allowing only `propext`, `Classical.choice`, and `Quot.sound`. The next gap is identifying these source packets with the next stage's fixed receiver register blocks and carrying the packet invariant through global matching and reassembly; no coefficient improvement follows yet.

Receiver packet assembly interface (GPT-6.1-astra-high, 2026-10-15): `receiverPacketFamily_union`, `_sorted`, `_pairwise_disjoint`, and `_card_eq_64` combine one parent packet partition with 64 child packet partitions, preserving their respective properties under explicit port-disjointness premises. `receiverPacketFamily_wireSets_union` proves that if the parent family covers the actual parent `downSet` and each child family covers its actual `upSet`, then their combined union is exactly `wireSets F (t+1) receiver`. These results are axiom-guarded and the focused `PacketMergeAxioms` check passes. The remaining work is to instantiate the premises uniformly, including zero-flow/aligned frontier cases, then track the resulting packet IDs through matching rounds; this theorem alone gives no coefficient improvement.

No-repair source case (GPT-6.1-astra-high, 2026-10-15): `flowA7_sourcePortRepairStage_noRepair_packetCells` proves that whenever the selector chooses no repair (aligned up-fringe or zero down-flow), every existing 64-rank cell stays sorted after the global correction stage. Together with `flowA7_sourcePortRepairStage_sourcePackets`, the local output packet proof covers both repaired shifted senders and all no-op cases.

Actual receiver packet assembly (GPT-6.1-astra-high, 2026-10-15): `flowA7_receiver_packetAssembly` derives cross-port disjointness from actual `wireSets_disjoint`, identifies the assembled union with the next-time receiver `wireSets`, and carries the source sortedness, pairwise-disjointness, and 64-wire cardinality premises to the complete receiver packet family. The theorem is axiom-guarded, and the focused chain through `PacketMergeAxioms` passes. Its remaining assumptions are precisely the parent down-port and 64 child up-port packet partitions, so the next proof task is to instantiate those premises in the aligned, shifted-repair, and zero-flow frontier cases.

Aligned port packet families (GPT-6.1-astra-high, 2026-10-15): `alignedUpRepairPacket` splits an aligned up-set into prefix/suffix 64-rank cells; `alignedDownRepairPacket` indexes each aligned down-cut by consecutive cells. Both families now have checked exact-union, pairwise-disjointness, and 64-wire-cardinality theorems; sortedness follows from the source `PacketSortedOn` invariant when their origins are 64-aligned. The focused chain through `PacketMergeAxioms` passes with explicit axiom guards. The next proof should turn these static layouts into actual post-stage port families, then case-split the parent and 64 children by repair/no-repair to discharge `flowA7_receiver_packetAssembly`.

Actual no-repair ports and aligned receiver step (GPT-6.1-astra-high, 2026-10-15): `flowA7_sourcePortRepairStage_alignedUpFamily` and `_alignedDownCutFamily` instantiate both aligned port layouts on actual scheduled senders, deriving sortedness after the correction stage from the no-repair packet-cell theorem. `flowA7_sourcePortRepairStage_zeroDownUpFamily` handles the distinct zero-down case: the up-port is the whole sender register, so the original grid is retained even when a half-fringe is offset by 32. `flowA7_receiver_aligned_packetAssembly` combines the positive-flow aligned parent and all 64 aligned children into an exact sorted 64-wire partition of the next receiver register, including actual cross-port disjointness. The focused chain through `PacketMergeAxioms` passes with guards. Remaining: parent/child repair branches, zero-flow parent empty port, mixed cases, and induction from the initial packet invariant through the global matching rounds.

Mixed receiver correction cases (GPT-6.1-astra-high, 2026-10-16): `flowA7_receiver_repairedParent_alignedChildren_packetAssembly` assembles a repaired selected parent down-cut with all 64 aligned child up-ports. `flowA7_receiver_alignedParent_repairedChildren_packetAssembly` handles the converse: an aligned parent cut with all 64 repaired child up-ports. Both return an explicit existential packet-family witness for the receiver's next register, preserving sortedness, exact coverage, disjointness, and 64-wire size; both pass the focused axiom guard chain. These are the two non-simultaneous-misalignment branches with positive flows. Remaining are zero-flow parent/child boundary combinations and packaging the branches into a single induction theorem, followed by global matching-round propagation.

Zero-flow receiver adapters (GPT-6.1-astra-high, 2026-10-16): `flowA7_zeroDownSet_empty` proves the selected parent cut is empty when its down-flow is zero. `flowA7_receiver_zeroParent_packetAssembly` assembles that empty parent port with any already-certified child packet partitions. Conversely, `flowA7_receiver_zeroDownChildren_packetAssembly` builds each zero-down child's up-port from its preserved whole-register 64-cell grid and assembles it with any certified parent cut family. These adapters pass the focused `PacketMergeAxioms` chain with guards. The receiver port partition cases are now modularly available across positive repaired/aligned and zero-flow sides; still needed are a single global branch theorem and packet-ID/matching-round propagation.

Canonical receiver packet IDs (GPT-6.1-astra-high, 2026-10-16): `packetFamily_reindex_contract` transports exact coverage, sortedness, disjointness, and 64-wire size across an equivalence of finite indices. `flowA7_receiver_packetAssembly_fin` applies this to both receiver ports and returns `Fin (card parent)` and `Fin (card child)` IDs. The two positive mixed receiver cases now use this canonical form, eliminating their repair-specific `Unit` sum IDs at the induction boundary. The focused checker through `PacketMergeAxioms` passes, including an axiom guard for the canonical assembly theorem. This prepares these cases for the indexed matching-round layer but does not yet combine all zero/aligned/repaired modes or identify the canonical IDs across successive `WireFlow` levels.

All-case local receiver induction (GPT-6.1-astra-high, 2026-10-16): `CanonicalPacketFamily` packages any finite 64-wire partition with a `Fin` index, and `CanonicalPacketPortContract` records sortedness, exact port coverage, disjointness, and packet size. `flowA7_receiver_parentPort_canonical` covers zero, aligned, and repaired parent cuts; `flowA7_receiver_childPorts_canonical` does the same for all 64 child up-ports. `flowA7_receiver_packetAssembly_canonical` composes these port contracts, and `flowA7_receiver_allCases_canonical` proves that every local receiver mode yields a canonical sorted packet partition of its actual next-time `WireFlow` register. Source module and guarded focused chain pass. This closes the local receiver case split, but it does not yet maintain packet-ID embeddings through matching rounds or prove that the resulting next-stage supports coincide with the scheduler's required positional cuts.

Canonical matching-round output (GPT-6.1-astra-high, 2026-10-16): `PacketInduction.lean` adds `genIndexedPacketRound_canonicalOutput`. Given a covered vertex-disjoint matching and pairwise-disjoint input embeddings, it reindexes the dealt output list by `Fin`, proving logical sortedness, pairwise disjointness, exact preservation of the full matched support union, and depth at most seven. The focused chain including `PacketMergeAxioms` passes. The new adapter composes abstract matching rounds, but a logical embedding's index order need not be physical-wire order; the unresolved global step is to carry these embeddings through each receiver's rank cuts and show the scheduler consumes the packets the prior round produced.

Receiver-to-matching adapter (GPT-6.1-astra-high, 2026-10-16): `canonicalPacketFamily_toEmbeddings` turns the all-case receiver theorem's physical-rank-sorted `Finset` packets into increasing embeddings for `genIndexedPacketRound`. It proves those embeddings are logically sorted, pairwise support-disjoint, and preserve the exact receiver-register support. The theorem is axiom-guarded. This closes the typed handoff from one actual receiver transition into an abstract matching round; it still does not show that matched output embeddings agree with the next scheduled receiver's parent/child rank cuts.

The handoff is now packaged as `flowA7_receiver_allCases_embeddingFamily`, which directly returns the canonical embedding family from the actual all-case receiver step. It passes the focused guarded chain. This gives an explicit composition point for a multi-round proof; reconciling later logical embeddings with physical positional cuts remains open.

Receiver packet-count bridge (GPT-6.1-astra-high, 2026-10-16): a canonical
disjoint partition into 64-wire packets has packet count exactly the support
cardinality divided by 64. Applying this to the all-case receiver proves its
actual output family has `flowA7 d hd b.l (t+1) / 64` members; for every
nonterminal next stage, that count satisfies the existing full-64-block or
63-tail shape theorem. The count interface is guarded in
`PacketMergeAxioms.lean`. The terminal stage is deliberately excluded from the
shape adapter because `flowA7_packet_count_block_shape` assumes a strict
preterminal time; terminal occupancy is handled separately by `flowA7_tf`.
This makes receiver packet arity scheduler-compatible, but does not yet give
the matching schedule or identify logical output supports with next-stage
physical rank cuts.

Terminal arity (GPT-6.1-astra-high, 2026-10-16): imported the existing final
occupancy theorem `flowA7_tf` to show that the terminal packet count is zero
or divisible by 64 as well. Thus no 63-packet tail remains at the terminal
time; the receiver-to-block-shape interface now covers every next-stage time.
This only resolves the arity cases. Parallel application of all 64-packet
group networks, tail handling, and the stage-to-stage physical-port
identification remain open.

Interleaved-support synthesis screen (GPT-6.1-astra-high, 2026-10-16): inspected the retained `two_chain_greedy.py`, which greedily chooses disjoint comparator layers to reduce inversions simultaneously over every Boolean threshold pair for two sorted chains with a fixed support word. On equal-size chains, it finds a 7-layer sorter for the worst of 362 symmetry-reduced 12-wire support words, and a 9-layer sorter for the worst of 1320 such 14-wire words. These are constructive upper bounds from a heuristic search only: they do not prove optimality or rule out a 6-layer uniform construction. They do show that a general arbitrary-interleaving repair should not be assumed to fit the six-layer allowance. The next useful screen is the actual finite family of support words generated by the scheduled correction/reassembly cuts, followed by synthesis or a structural network for that restricted family. The 7-layer matching round itself is already support-agnostic; this issue belongs to fixed positional reassembly between rounds.

Alternating 64-wire support screen (GPT-6-astra-high, 2026-10-16): ran the same heuristic on the fixed word `(AB)^32`. It produced a 32-layer network that sorts all 33×33 threshold states of two sorted 32-wire chains, hence a valid finite Boolean-family candidate by the 0-1 principle. This is only a greedy upper bound, not a lower bound or a Lean proof, and this alternating word has not been shown to occur in the actual scheduled support family. The result says the current greedy search is not a route to the <16-layer positional repair needed to move the 205 fallback below 200; the actual support words or a stronger synthesis/construction are needed.

Small motif refinement: the same search finds depth 6 for `ABABABABABAB`, depth 4 for `AABBAABBAABB`, and depth 6 for the contiguous `AAAAAABBBBBB` at 12 wires; the alternating pattern `ABABABABABABAB` takes 7 greedy layers at 14 wires. The input is two independently sorted chains, and the goal is sorted values in the fixed support-word order. These data are only small exact-input-family synthesis evidence, not asymptotic bounds. They suggest the useful structural question is whether the actual post-deal support pairs have a restricted, repeated motif admitting a uniform ≤6-layer positional reassembly network; unrestricted interleavings are not the right first target.

Partial matching execution adapter (GPT-6.1-astra-high, 2026-10-16): `genIndexedPacketRound_output_support_incident` proves that a non-perfect indexed matching round outputs exactly the support belonging to matched packet IDs, with no coverage premise. `genIndexedPacketRound_unmatched_unchanged` proves each nonincident packet is pointwise untouched by the round. Both have axiom guards and the focused chain through `PacketMergeAxioms` passes.

Partial matching family contract (GPT-6.1-astra-high, 2026-10-16): `genIndexedPacketRound_withSingletons_contract` composes those results. Given a partial vertex-disjoint matching and an explicit pairwise-disjoint singleton list covering its nonincident IDs, it proves the combined dealt-output/singleton list remains sorted after the round, is pairwise support-disjoint, and covers the entire original packet support exactly. `genIndexedPacketRound_withSingletons_canonicalOutput` then reindexes the family by `Fin`, proving the same support/sortedness contract and depth at most seven. Both theorems are axiom-guarded, and the focused Lean chain from `PacketInduction` through `PacketMergeAxioms` passes. Matching schedules may now use and compose partial edge colors at the logical packet layer; physical `WireFlow` placement compatibility is still open.

Shorter-cycle numerical follow-up (GPT-6.1-astra-high, 2026-10-16): `matching_cycle_screen.py --packets 256 1024 --rounds 17 18 19 20 21 22 --trials 8` sampled median product norms decreasing from about 0.0165/0.0176 at 17 rounds to 0.00313/0.00365 at 22 rounds; the largest sampled norm at 22 was 0.00385. At 26 rounds, the previous 10-trial screen gave about 0.0010 at 1024 packets. This suggests testing whether 22 rounds suffice for the coupled invariant. If so, unchanged remaining depth costs would give a conditional gate `(22*13+57)/2 = 171.5`, and the coarse fresh spill term drops from `26/256 = 10.16%` to `22/256 = 8.59%` of `N*K` per stage. These are independent finite floating-point screens, not a uniform matching family, outward-rounded certificates, or a proved coefficient.

Positional-vs-logical count profile (GPT-6.1-astra-high, 2026-10-16): `oddEvenMerge128_physicalHalf_counts` uses the sorted-Boolean interval-profile theorem to prove that the physical halves of a fully merged 128-wire support have counts `min 64 (H-64)` and `min 64 H`. Its corollary `oddEvenMerge128_balanced_deal_vs_physical_halves` specializes to total count `H=64`: physical halves are `(0,64)`, while the logical even/odd dealt packets are `(32,32)`. Both are kernel-checked with guards. This is a concrete obstruction to closing the global recurrence on logical packet variance alone; any usable induction state must retain the physical rank profile together with logical packet counts.

Balanced-input witness (GPT-6.1-astra-high, 2026-10-16): `oddEvenMerge128_balanced_inputs_shift_physical_profile` packages the same obstruction with explicit input counts: two sorted 64-wire packets each begin with 32 ones, while after their full merge the positional halves have counts `(0,64)` and the logical dealt packets still have `(32,32)`. Its focused Lean check and axiom guard pass. This rules out a recurrence whose state identifies the physical half-count vector with the logical packet-count vector, even on balanced input; it does not quantify the full rank profile across stages.

Phase-specific energy baseline (GPT-6-astra-high, 2026-10-16): `oddEvenMerge128_physicalHalf_doubledEnergy` now kernel-checks the closed formula `2*min(H,128-H)^2` for the doubled centered energy of the two physical halves at total count `H` (`H≤128`), using only `propext` and `Quot.sound`. The even/odd logical packets have energy 0 or 2 according as `H` is even or odd, by the existing parity-count theorem. The discrepancy is deterministic in `H`, so a viable recurrence can subtract this baseline instead of comparing raw physical and logical variances. This isolates a candidate state correction; no cross-stage contraction or 4096-wire transfer is proved.

57-layer reassembly candidate (GPT-6-astra-high, 2026-10-16): a balanced merge tree on 64 sorted 64-wire runs uses `oddEvenMergeNet 7` through `oddEvenMergeNet 12`, once per tree level in parallel, for depth `7+8+9+10+11+12=57`. Correctness follows inductively from the existing two-run merge theorem, and disjoint intervals permit parallelism. This makes the budget structurally plausible, but the tree is not yet formalized and the actual receiver's parent-plus-64-child packet family has not been shown to match 64 contiguous runs. Tracked in `GRANULARITY-GATE.md` as the next interface test, not as a proved 57-layer receiver network.

Alternating two-chain correction screen (GPT-6-astra-high, 2026-10-16): the new `alternating_chain_screen.py --pairs 64` constructs a 14-layer comparator network on the fixed `AB` repeated 64 times support. Its finite state space is exactly the `65*65=4225` independent Boolean thresholds of the two sorted chains; all output states are sorted. The full layers are saved in `alternating_chain_128_screen.json`. This is constructive finite evidence for a 128-wire correction motif, not an optimality result, Lean proof, or 65-run receiver construction. It raises the concrete next test: check whether actual matching outputs induce this motif and whether the 14-layer correction can be scheduled inside the existing 57 layers.

Alternating-chain screen follow-up (2026-10-16): the deterministic greedy
network for the alternating two-chain support sorts all 4,225 threshold states
in 14 layers. Randomized tie-breaking was tested for 40 total seeds (the
original deterministic construction plus 8 and 32 randomized trials); none
found a shallower construction. This is heuristic evidence only and does not
prove a 14-layer lower bound. The script accepts `--trials` and `--seed` for
replay. The corresponding Lean exhaustive-certification attempt was abandoned:
expanding the generated comparator evaluation in the kernel exceeded practical
elaboration/resource limits, so no Lean claim is made. The focused
`PacketMergeAxioms` check passed on 2026-10-16. The primary structural test
is now the arbitrary-support 4096-wire merge-tree lemma plus its incomplete
final block and output re-packetization interface. `flowA7_receiver_allCases`
already supplies disjoint sorted 64-wire supports, so physical contiguity is
not needed: `genScatter` supports arbitrary injective placements. Grouping
complete sets of 64 packets by ID is therefore available; handling the fewer
than 64 leftover packets within budget remains open. See `GRANULARITY-GATE.md`.

Scheduled packet-tail gate (Codex / GPT-6-astra-high, 2026-10-16):
`flowA7_packet_count_block_shape` and `flowA7_packet_tail_fraction_le` are
kernel-checked. For the actual scheduled packet count `C = flowA7/64`, the
only nontrivial remainder modulo 64 is exactly 63, and then `C >= 4095`; hence
that tail is at most `7/455` of the cohort. This follows from the existing
exact packet-count factorization and isolates the bounded exception to the
64-run merge-tree tiling. The new claims are guarded in `PacketMergeAxioms.lean`.
They do not yet sort the tail or bound its contribution in the coupled rank and
variance recurrence. See `GRANULARITY-GATE.md`.

Unequal-run tail construction screen (Codex / GPT-6-astra-high, 2026-10-16):
`unequal_run_merge_screen.py` implements recursive odd/even merging for
arbitrary two sorted-run lengths. It passes all Boolean threshold cuts for all
run lengths 1 through 16, plus the actual first two tail pairs (128+64 and
256+192 wires). For the five unequal pairs in the 63-run tree, computed depths
are exactly 8, 9, 10, 11, and 12; with the initial 7-layer pair-merge level,
the 63-run merge tree fits 57 layers. This is still finite computation, not a
Lean correctness theorem. The formal obligation is the unequal-lane
correction-layer invariant for the recursive network.

Unequal correction formal step (Codex / GPT-6-astra-high, 2026-10-16):
`PacketUnequalMerge.lean` now includes the unequal `(L,L-1)` min/max
correction formula and proves its output is monotone from the lane monotonicity,
same-rank ordering, and two-position cross-rank bound. It also defines the
intended disjoint comparator layer and proves its depth is at most one. Both
claims are guarded in `PacketMergeAxioms.lean`; the focused chain from
`PacketUnequalMerge` through `PacketMergeAxioms` passes. The odd and even
comparator endpoints are now proved to execute the corresponding min/max
outputs on the interleaved lanes. `unequal_cross_bounds_of_threshold_gap`
proves that sorted lane profiles with threshold-count difference at most one
imply the exact same-rank and two-position inequalities needed by that layer.
The full pointwise execution-equality theorem, including the untouched first
wire, is also proved. `unequalCorrectionLayer_sorts_of_threshold_gap` now
packages the correction proof as a sorting theorem for the concrete layer.
At that stage the recursive submerge threshold-count invariant was still open;
the following progress note records its invariant-transport component. This
does not complete the 63-run merge.

Threshold-profile induction progress (Codex / GPT-6-astra-high, 2026-10-16):
`PacketUnequalMerge.lean` now proves `unequalSourceParityThresholdGap`: for
two monotone source runs of lengths `2m` and `2m-1`, their even and odd
projections (concatenated in source-run order) have threshold counts differing
by at most one. The proof reduces each threshold to a sorted Boolean string;
the even-length source uses the existing even/odd count lemmas, and in the
odd-length source injections account for its unpaired final even position.
The new `unequalThresholdCount_exec` states that every comparator network
preserves each threshold count. Consequently
`unequalSourceParityThresholdGap_exec` proves the same gap after arbitrary,
independent comparator networks act on the two lanes. These theorem statements
are guarded in `PacketMergeAxioms.lean`; the focused check through that guard
passes. This closes the *invariant transport* step, not the induction itself:
we still need to instantiate the networks with the actual recursive merge
networks, establish lane sortedness inductively, reconcile the `m + (m-1)` and
`2*m-1` size casts, prove the base cases, and account for the resulting depth
recurrence. No improved limsup coefficient follows yet.

Follow-up: the size-cast portion of that list is now closed for threshold
counts. `unequalThresholdCount_cast` proves profile counts invariant under the
canonical `Fin` equivalence, and `unequalSourceParityThresholdGap_exec_cast`
states the transported gap directly at the exact `2*m` / `2*m-1` dimensions
used by the correction layer. Both are axiom-guarded and the focused Lean
chain passes. Remaining: instantiate the actual recursively defined networks,
prove their outputs monotone by induction, handle base cases, and formalize
their scheduled depth.

Induction-step package: `unequalParityMerge_step_sorts` now combines these
pieces. Given any comparator networks whose outputs sort the even and odd
parity subproblems, it proves that the unequal correction layer sorts the
parent; the theorem explicitly handles the lane-size casts and is included in
the axiom guard. Thus the mathematical induction step is formalized. The
remaining work is to define and verify the recursively embedded networks
(including their parity-wire placements), establish their base cases, and
derive the `q+7` scheduled depth bound for the five tail levels.

Outer-level profile progress: `evenSourceParityThresholdGap` proves that for
two even sorted runs, the even-lane threshold count is at most the odd-lane
count, while the odd-lane excess is at most two. This is the right asymmetric
invariant for the repeated even/even splits above the 32+31 core;
`evenSourceParityThresholdGap_exec` transports it through arbitrary lane
networks, and `equal_cross_bounds_of_threshold_gap` turns it into the same-rank
and two-rank inequalities for a one-layer equal-lane correction. These results
are axiom-guarded. The remaining construction gap is to formalize the general
even-size correction network and combine it recursively with the 32+31 core.

Correction-layer closure: the equal-lane one-layer correction is now a
concrete comparator network, implemented as the unequal correction layer
scattered onto the first `2L-1` wires of `2L`. Its depth is at most one, its
execution is proved equal to the equal-length min/max interleave, and that
output is proved sorted under the asymmetric `0/2` threshold-profile gap.
`evenParityMerge_step_sorts` packages the even/even induction step, just as
`unequalParityMerge_step_sorts` packages the odd-sized step. These declarations
are added to the axiom guard. This closes the local correction-layer gap for
both parities.

Recursive-step progress: `equalParityFront` now physically scatters two
same-size recursive lane networks onto even and odd wires, and its execution
is proved to be the intended interleave of their outputs. The theorem
`equalParityFront_depth_le` proves those lanes run in parallel, and
`equalParityMergeNet_depth_le` adds only the one-layer correction cost:
`depth(parent) ≤ max(depth(evenLane), depth(oddLane)) + 1`. The composed network
`equalParityMergeNet` is proved to sort whenever its lane outputs are sorted
and have the transported `0/2` threshold gap. Focused runs have checked both
`PacketUnequalMerge` and `PacketMergeAxioms`, including axiom guards for the
depth and sorting results. `equalParityMerge64_sorts_two_runs` now instantiates
the interface on two 32-wire source runs: if the recursive networks sort the
32-wire even and odd parity lanes, then the composed 64-wire network sorts.
Its profile gap follows from source monotonicity, and explicit index lemmas
identify those parity wires with the two 16-wire pieces. The companion
`equalParityMerge64_depth_le` gives a six-layer bound when both lane networks
have depth at most five. `standard64Merge_sorts_two_runs` discharges those
hypotheses using the verified 32-wire odd-even merge, and
`standard64Merge_depth_le` closes the six-layer bound for this concrete
network. This closes the standalone 64-wire equal-run merge proof, although
it recovers the standard odd-even merge bound and by itself gives no
improvement. The novel remaining work is to replace that standard lane choice
with the proposed unequal 32+31 core, connect it to the five tail levels, and
prove the resulting global depth recurrence. No improved limsup constant
follows yet.

Unequal recursive correctness progress: the concrete 3-, 7-, 15-, 31-, and
63-wire networks now each sort arbitrary sorted source runs of lengths
`2^k` and `2^k - 1`. The 7- and 15-wire steps use standard equal-run merges
on their even lanes and the already proved smaller unequal network on their
odd lanes. The 31- and 63-wire steps reuse the physical-lane transport
lemmas for 16+15 and 32+31. The existing depth chain gives respective upper
bounds 2, 3, 4, 5, and 6. New axiom guards cover the concrete sorting theorems
and 63-wire depth. This closes the recursive correctness proof for the
32+31 merge core, but not its integration into the 64-wire global construction
or the five tail levels, and it yields no improved coefficient by itself. A
parameter-generic physical lane identity remains desirable; the first attempt
needed explicit casts between different `Fin` length expressions and was
removed after its focused check exposed type mismatches.

Even/even tail-lift interface: `equalEvenRuns_lane_eq` and
`equalOddRuns_lane_eq` now identify the physical parity wires of arbitrary
even-length source runs `2m` and `2n` with their two `m`- and `n`-wire parity
subruns, including the required `Fin` casts. The guarded theorem
`equalParityMergeNet_sorts_two_even_runs` packages the outer induction step:
any verified merger for sorted `m+n` runs lifts to a merger for sorted
`2m+2n` runs with one additional correction layer. This is the reusable
interface needed to wrap each `2^k+(2^k-1)` core six times for the five
scheduled tail pairs. The next entries record completed sixfold compositions
for the two largest pairs; three smaller compositions and the 57-layer tree
composition remain open.

Largest scheduled tail pair closed: six explicit equal/even lifts of the
verified 32+31 core now give a concrete 4032-wire network that merges sorted
2048- and 1984-wire runs. `unequalTail63Lift6_sorts_two_runs` proves
correctness, and `unequalTail63Lift6_depth_le` proves depth at most 12, the
required `j+7` cost for the `j=5` tail level. Both are axiom-guarded, and the
focused guard chain passes. This discharges the largest of the five unequal
merge gates in the 63-run tree; the corresponding four smaller tail pairs,
the rest of the tree proof, and all global recurrence/coefficient obligations
remain open.

Second scheduled tail pair closed: six equal/even lifts of the 16+15 core now
give a concrete 1984-wire merger for sorted 1024- and 960-wire runs. Its
correctness and depth-at-most-11 results are axiom-guarded. Together with the
2048+1984, depth-12 merger above, this formally closes the two largest of the
five special tail merges. The 128+64, 256+192, and 512+448 pairs and the
surrounding 64-run tree composition remain.

Middle scheduled tail pair closed: six lifts of the 8+7 core give a concrete
960-wire merger for sorted 512- and 448-wire runs, with a checked depth bound
of 10. Its correctness and depth theorems are guarded. Three of the five
special merges in the 63-run tree are now proved at their target costs 10, 11,
and 12. The 256+192 pair is also closed at depth 9, and 128+64 is closed at
depth 8. All five scheduled unequal merges are now proved at their target
costs. The remaining local network gate is composing them with the 57 full
64+64 pair merges into the complete 63-run tree and showing its output is the
required packet layout.

Smallest scheduled tail pair closed: six lifts of the 2+1 core give a
192-wire merger for sorted 128- and 64-wire runs, with a checked depth bound
of 8. Its correctness and depth claims pass the axiom guard. This completes
the five individual unequal merge networks at costs 8 through 12; the complete
tree composition and packet-stage recurrence remain open.

63-run merge tree closed locally: `PacketMergeTree` defines a reusable tree
composition theorem for parallel child networks followed by a checked merger.
It instantiates the 57 equal 64+64 joins and the five unequal joins (at costs
8 through 12) into a concrete network on 4032 wires. `packetOddTree6_sorts`
proves it merges 63 sorted 64-wire runs, and `packetOddTree6_depth_le` proves
depth at most 57; both declarations pass `PacketMergeAxioms` guards and the
focused checker. This closes the local 63-run merge-tree gate. It does not yet
prove the resulting 4032-wire layout is the packet-stage layout needed by the
global scheduler, nor the packet recurrence, global depth sum, or a coefficient
improvement. The next mathematical gate is to identify the tree's run order
with the scheduler's packet order and transport the packet support/profile
invariant through this merge stage.

The generic `PacketMergeTree.scatter_sorts` theorem transports any checked
merge tree through an increasing wire embedding, and `scatter_depth_le`
preserves its depth budget. `PacketMergeTreeGen` now gives the stronger
generalized-comparator interface: `packetOddTree6GroupNet` takes any 63
pairwise-disjoint sorted 64-wire embeddings, constructs their logical 4032-wire
order, and merges them at depth at most 57. `packetOddTree6_runsSorted_of_packets`
derives the recursive tree precondition directly from the 63 input sortedness
hypotheses. The sorted output is re-packetized as 63 sorted 64-wire embeddings;
these supports are pairwise disjoint and cover exactly the input support.
These composed declarations pass the axiom guard. The remaining integration
is to construct the actual scheduler's 63-packet groups across receiver and
matching rounds, carry their evolving support/rank invariant, and close the
global recurrence.

Update to the preceding next-step note: the merge-tree adapter now accepts the
63 packets in any supplied logical order and derives the recursive run premise
from individual packet sortedness. The outstanding group-order obligation is
therefore scheduler bookkeeping: identifying which 63 packets are processed
together at each receiver/matching stage and keeping the resulting packet IDs
compatible with later cuts.

Full 64-packet block closed as well: `packetPowerTree6` merges 64 sorted
64-wire runs on 4096 wires using odd-even merge costs 7 through 12, for depth
57. `packetPowerTree6GroupNet` accepts arbitrary pairwise-disjoint sorted
64-wire embeddings, derives the tree's recursive precondition, and returns 64
sorted 64-wire output embeddings on the same support. Its sorting, depth, and
re-packetization interfaces are axiom-guarded. Together with the 63-packet
remainder network, the local block and exceptional-tail networks required by
the packet-count factorization are now available. They are not yet composed
across all groups in an actual receiver or matching stage.

Parallel merge batches and exact receiver arity (GPT-6.1-astra-high,
2026-10-16): generalized `genScatterBatch` applies one fixed local comparator
network to a finite list of pairwise-disjoint supports. Its axiom-guarded
depth is at most the local depth, and its execution on every member support
equals that support's independent local execution. `genScatterMergeTreeBatch`
instantiates this for any `PacketMergeTree`; the 64-run tree therefore sorts
and re-packetizes every full group simultaneously in at most 57 layers. The
receiver-family cardinality is also now derived exactly as
`flowA7 d hd b.l (t+1) / 64`, with count shape for nonterminal times and the
terminal empty-or-multiple-of-64 case. This closes the isolated-block parallel
depth concern and the receiver arity lookup. The divisible and residue-63
receiver wrappers now transport the canonical existential family into the
corresponding arithmetic indexing forms. Still open: package the sorted
post-merge outputs as an exact receiver partition and show their supports
match the next physical scheduler cuts. No stage-to-stage recurrence or
improved global coefficient follows yet.

Divisible receiver cohorts (GPT-6.1-astra-high, 2026-10-16):
`packetFamily_divisible64_merge` now converts any disjoint sorted
`Fin m`-indexed packet family with `64 ∣ m` into consecutive 4096-wire blocks,
proves the block supports disjoint, runs the 64-run tree on all blocks in
parallel at depth at most 57, and proves every output packet sorted.
`flowA7_receiver_allCases_divisible64_batch` applies this directly to an
actual corrected receiver register whenever its scheduled packet count is
divisible by 64. These results are included in `PacketMergeAxioms.lean` and
the focused guard chain passes. The remaining scheduled arities are empty or
singleton bags (trivial/no full merge) and residue-63 cohorts. Their actual
receiver wrapper is recorded below; physical next-cut identification remains.

Residue-63 mixed batch now closed (GPT-6.1-astra-high, 2026-10-16):
`packetFamily_residue63_merge` accepts any disjoint sorted cohort indexed by
`Fin (64*q+63)`, groups the first `64*q` packets into consecutive 64-packet
blocks, assembles the last 63 packets as one unequal merge tree, proves the
tail support is disjoint from every full block, and combines both families of
merge networks at depth at most 57. It also proves all full-block and tail
output packets sorted. Its result and the mixed network's depth/sorting
theorems pass the axiom guard. `flowA7_receiver_allCases_residue63_batch`
reindexes the actual all-case receiver family using its exact packet count and
applies this mixed batch directly. Together with
`flowA7_receiver_allCases_divisible64_batch`, this closes the local
all-arities merge-cost gate. Still open: package the output embeddings into an
exact next-stage partition, identify them with the scheduler's physical cuts,
and prove the global rank/energy recurrence needed for any coefficient
improvement.

Exact local output support partition (GPT-6.1-astra-high, 2026-10-16):
`genScatterMergeTreeOutputEmbedding_support_iff` proves that a merge tree's
output chunks cover exactly the input embedding's wire support. The new
`genMergeTreeFullTailBatch_output_support` combines this with disjointness:
output chunks within a tree, across distinct full blocks, and between full
blocks and the 63-packet tail are pairwise disjoint, and their union is exactly
the union of full-block and tail input supports. The theorem is axiom-guarded.
This closes support conservation for the local mixed batch; it does not yet
enumerate the outputs in the scheduler's next canonical rank order or identify
them with its positional cuts. The next useful step is an adapter from this
support-certified output family to those actual next-stage cuts, rather than
more local merge lemmas.

Exact output rank-profile transfer (GPT-6-astra-high, 2026-10-16):
`genScatterMergeTree_output_profile` proves that if a merge tree sorts 4096
Boolean wires into 64 sorted 64-wire runs, then each output run has exactly
the ideal 64-cell profile for the total number of ones. The specialized
`packetPowerTree6GroupNet_output_profile` applies this to the 57-layer merge
of 64 sorted 64-wire packets. Both results are kernel checked and added to the
axiom guard. This gives a rigorous local scale-transfer interface: the full
merge preserves global rank and materializes each canonical rank cell. It
still does not identify those abstract chunk embeddings with the physical
rank intervals used by the next scheduler stage; that alignment plus the
cross-stage recurrence remains the main obstruction to deriving a global
coefficient improvement.

Arbitrary-value threshold profile transfer (GPT-6-astra-high, 2026-10-16):
`genScatterMergeTree_output_threshold_profile` lifts the exact local profile
law from Boolean inputs to every threshold of any linearly ordered input. It
uses threshold-commutation of comparator execution, so the statement is ready
for the value-threshold recurrence rather than requiring a separate Boolean
input invariant. The focused module check passes; the complete axiom chain is
being rerun with a guard for this theorem. The physical next-cut alignment and
rank/energy contraction remain unproved.
Concrete all-threshold 4096-to-64 interface (GPT-6-astra-high,
2026-10-16): `packetPowerTree6GroupNet_output_threshold_profile` specializes
the preceding result to the actual 57-layer 64-run merge, for arbitrary
linearly ordered values and every threshold. Both arbitrary-value theorems
pass the focused `PacketHalfProfile` check and are included in the axiom-guard
chain. This makes the local profile law directly consumable by the existing
threshold recurrence. No physical-cut identification or global contraction
has been established, so this does not yet improve the proved limsup bound.


Divisible-receiver profile integration (GPT-6-astra-high, 2026-10-16):
`genScatterMergeTreeBatch_output_threshold_profile` and
`packetFamily64BlockList_merge_output_threshold_profile` lift the exact
per-run threshold profile through the actual parallel full-block batch.
`flowA7_receiver_allCases_divisible64_batch_profiles` then composes this with
the checked all-case receiver correction and packet decomposition: for each
full block and every threshold, its output rank packets have the exact ideal
profile, and the same witness retains the established disjointness,
sortedness, and 57-layer bound. The focused check passes; guards are added.
This closes the full-block local receiver invariant only. Residue-63 tails and
identification with the next stage's physical `WireFlow` cuts remain open.

Actual divisible receiver profile contract (GPT-6-astra-high, 2026-10-16):
`flowA7_receiver_allCases_divisible64_batch_profiles` now combines the
all-case source correction, canonical receiver packet family, consecutive
64-packet block decomposition, and exact threshold profiles of every output
rank packet. It returns one witness preserving block disjointness, sorted
output packets, and the 57-layer depth ceiling. The theorem and its generic
batch/profile helpers are axiom-guarded; direct compilation of
`PacketMergeAxioms.lean` succeeds. This closes the divisible-cohort local
invariant transfer. It does not handle the scheduled residue-63 tail or prove
that these logical output packets are the next stage's fixed physical port
cuts, so no global coefficient follows.


Variable-cardinality and residue-63 profile integration (GPT-6-astra-high,
2026-10-16): `genScatterMergeTree_output_threshold_profile_k` gives exact
all-threshold profiles for a merge tree with any number of 64-wire leaves.
`genMergeTreeFullTailBatch_output_threshold_profile` lifts that law through a
disjoint batch of full blocks plus one unequal tail, using execution locality
to show the full batch leaves the tail unchanged. Finally,
`flowA7_receiver_allCases_residue63_batch_profiles` composes it with the actual
all-case receiver correction and residue-63 packet decomposition. The witness
retains disjointness, sorted output packets and the 57-layer ceiling, while
giving exact threshold profiles for all 64-wire full-block packets and the
63-wire tail packet. The focused module compilation succeeds. This closes the
local profile-transfer gap for both divisible and residue-63 receiver sizes.
`PacketReceiverResidue.lean` now proves that these two cases cover every
nonzero active receiver in the actual schedule. Matching the logical output
packets to the next stage's fixed physical `WireFlow` cuts and proving a global
rank-profile contraction remain open. No improved limsup coefficient is
established yet.

Receiver-residue classification (GPT-6-astra-high, 2026-10-16):
`flowA7_receiver_packetCount_residue` proves for every `d >= 7`, every actual
transition `2 <= t < tf7 d`, and every nonroot receiver level `1 <= l`, that
the next receiver's packet count has remainder 0 or 63 modulo 64. The proof
classifies the `NodeShape` forms: an active node has either zero wires or at
least 128, which excludes the exceptional 64-wire top-descending case; all
remaining power and power-difference forms yield residue 0 or 63. At the
terminal time, the only occupied level has `64^6` wires and is divisible. The
theorem compiles in the focused packet check and is axiom-guarded. The finite
screen in `FlowReceiverResidueScreen.lean` was the diagnostic that suggested
this classification; it is no longer the evidence for the uniform claim.

Grouped merge support conservation (GPT-6-astra-high, 2026-10-16):
`packetFamily64BlockList_support` proves that consecutive full 64-packet
blocks cover exactly the input cohort's wires. Its output-strengthening,
`packetFamily64BlockList_output_support`, proves the merge tree's output rank
chunks cover that same set. `flowA7_receiver_allCases_divisible64_batch_support`
then lifts this to the actual divisible receiver and its exact next-stage
`wireSets` support. The generic grouped-block lemma passes its focused check;
the receiver theorem passes the focused `PacketHalfProfile` check. This closes
support conservation for the divisible case alongside its sortedness/profile
contracts. `flowA7_receiver_allCases_residue63_batch_support` now proves the
analogous exact cover of the actual receiver by full-block and tail supports.
Together with `genMergeTreeFullTailBatch_output_support`, this supplies exact
support conservation through both merge configurations. Neither route
identifies logical output ranks with the next scheduler's physical cuts; the
global recurrence and any coefficient improvement remain open.

Scattered rank-partition L1 interface (GPT-6-astra-high, 2026-10-16):
`monotoneCountDecomposition_L1_exact` proves the exact L1 identity for any
finite collection of monotone count profiles whose total is the packet count.
`assignedRankProfiles_L1_exact` instantiates it for an arbitrary map assigning
each rank position to a destination: destination rank sets need not be
contiguous, provided the selected suffixes are nested and have the expected
cardinalities. This removes contiguity as a mathematical requirement for the
profile transfer. The remaining formal bridge is to define the actual owner
map from the merge-output wire embeddings and next-stage `WireFlow` ports,
identify its suffix counts with the concrete routed Boolean values, and then
sum the resulting errors at each receiver. No global rank contraction or
improved limsup coefficient is proved.

Scattered-profile squared-error aggregation (GPT-6-astra-high, 2026-10-16):
`assignedRankProfiles_aggregate_L2` and its source-dependent-target extension
`assignedRankProfiles_aggregate_L2_var` prove that when each source packet's
rank positions are assigned to destinations, summing signed profile errors
at each destination costs at most `c` times the sum of source count energy,
where `c` is the number of contributing packets. The proof uses the exact
scattered-rank L1 identity packet-by-packet, then Cauchy-Schwarz over
destinations within each packet and over packets at each destination. Both
declarations have axiom guards and compile through `PacketMergeAxioms`. The
variable-target form matches the source-dependent ideal means already used by
the `WireFlow` recurrence. The remaining bridge is concrete: define the owner
map from actual merge-output wire embeddings to next-stage receiver ports,
prove its suffix counts agree with routed Boolean counts, and sum the result
over active levels without losing the energy contraction needed for a global
coefficient. No limsup improvement is established by this lemma alone.

Actual active-layer squared-error recurrence (GPT-6-astra-high, 2026-10-16):
`wireFlowLayer_profile_error_sq_sum_le_source_energy` uses the actual
`wireFlowLayerSelection` parent/children routing. For each receiver, Cauchy
charges its at-most 65 source contributions; across receivers, the selected
pieces from each sender are disjoint and their absolute errors sum exactly to
that sender's coarse count error. This proves the all-active-receiver bound
with factor 65, including actual register counts and any finite family of
thresholds. `wireFlowLayer_reencoded_profile_energy_recurrence` also chooses
the selected ideal means as monotone, capacity-valid next fractional codes,
giving the same squared-error recurrence at every threshold and active level.
Both theorems pass the focused axiom guard. This closes the one-layer
aggregation/re-encoding gap, but the factor-65 estimate is not a contraction:
it does not compose with merge/deal to give a coefficient. The next decisive
test is a schedule-level operator/potential bound that exploits the actual
matching geometry and quantifies the mixing decrement against these routed
profile errors; the local matching energy lemma alone does not supply that
bridge.

Heterogeneous-target matching energy (GPT-6-astra-high, 2026-10-16):
`floorCeilAverage_energy_drop_ge_targetAverage` proves that if two packet
targets are μ₁ and μ₂, and both dealt outputs take target (μ₁+μ₂)/2, then
the squared target-relative energy drop is at least
`((e₁-e₂)^2-1)/2`, where eᵢ is countᵢ−μᵢ. The summed theorem
`mergeDealMatching_energy_drop_ge_targetAverage` handles any parallel
matching, and `genMerge128_dealt_energy_drop_ge_targetAverage` instantiates
it on the checked 128-wire merge-and-deal network. The full axiom guard passes.
This removes the common-target hypothesis from the local mixing interface and
identifies the right edge discrepancy for a moving target profile. It applies
to a global recurrence only if the scheduler's targets evolve by the same
pairwise averages; the current selected-interval target recurrence has not
been shown to do so, and no contraction or improved coefficient follows yet.

Exact merge reassembly error (GPT-6-astra-high, 2026-10-16):
`genScatterMergeTree_output_threshold_profile_L1_exact` combines the checked
4096-to-64 threshold-profile law with `profileCellMean_L1_exact`. For any
fractional target `q+frac` and sorted 64-run input, the sum of the absolute
errors across all 64 output packets equals exactly the input cohort's total
count error. Thus a complete 57-layer local reassembly introduces no fresh
aggregate L1 error at that scale. The theorem passes `PacketHalfProfile`; its
axiom guard is included in the current full-chain check. This local exact
transfer still depends on a rank-coherent target and does not identify the
logical output packet order with the next physical `WireFlow` cuts.

Heterogeneous merge-to-profile transfer (GPT-6-astra-high, 2026-10-16):
`packetPowerTree6GroupNet_heterogeneous_profile_error_le` removes the common
input-target restriction at this interface. For 64 disjoint sorted packets,
arbitrary real targets `μ j`, and any threshold, if their targets sum to the
batch target `q+frac`, then the sum of absolute output-cell errors is at most
the sum of the 64 input count errors. The grouped embedding's threshold count
is exactly the sum of source counts; the sorted 4096-to-64 merge then transfers
the aggregate discrepancy exactly. Both lemmas have axiom guards, and the
`PacketMergeAxioms` check passes. This closes local heterogeneous target
accounting, but does not prove that the next physical `WireFlow` stage uses
these output-cell targets or cuts. No global recurrence or coefficient below
1419 follows from this lemma alone.

Concrete scattered-rank ownership (GPT-6-astra-high, 2026-10-16):
`wireSetOwner` chooses the unique register containing each physical wire,
using the checked completeness and disjointness of the actual `WireFlow`
partition. `wireSetPacketRankOwner` assigns every rank slot of an arbitrary
scattered packet embedding to that register, and
`assignedRankCount_wireSetPacketRankOwner` identifies the abstract assigned
rank count exactly with the packet slots physically lying in each register.
The `PacketHalfProfile` check and full `PacketMergeAxioms` guard chain pass.
This closes the owner-map existence/counting interface for the scattered-rank
L2 lemma. It does not yet identify the induced fractional destination targets
with `wireFlowLayer_reencoded_profile_recurrence`, nor prove contraction for
the actual matching schedule; the global coefficient is unchanged.

Full-partition threshold realization (GPT-6-astra-high, 2026-10-16):
`packetRankOwner_trueCountOn_eq_of_partition` strengthens the individual
slot identity: for any disjoint packet family covering all wires, summing its
rank-owner threshold counts over packets equals the exact Boolean threshold
count in each actual `WireFlow` register. The proof constructs a bijection
from selected `(packet, rank)` pairs to selected wires in the destination
register. `PacketHalfProfile` compiles, and the full `PacketMergeAxioms` guard
chain passes with standard axioms. This closes the counting half of applying
the scattered-profile recurrence to a global packet partition; it still does
not identify the destination fractional targets or prove energy contraction.
The owner-map and partition theorems now accept any finite packet-ID type, so
they compose with receiver families whose packet counts differ by bag.

Packet-target monotonicity bridge (GPT-6-astra-high, 2026-10-16):
`natProfileInterp_mono_mean` establishes monotonicity of the interpolated
destination count as its real packet target increases, including the adjacent
floor-boundary case. `assignedRankCount_mono` and
`assignedRankInterp_sum_mono` lift this to arbitrary fixed scattered-rank
owner maps and finite packet families, assuming nested rank-prefix selectors
and monotone per-packet targets. `profileIntervalSelectedMean_eq_interp`
shows that any selected family of ideal rank-piece means is exactly the
interpolation of its integer interval-count profile.
`wireFlowReceiverSelectedIdealMean_eq_intervalProfile` instantiates this for
the actual 65-source receiver, while
`wireFlowReceiver_selected_count_eq_register` identifies the corresponding
actual count with the receiver register count. The concrete
`wireSetPacketRankInterp_sum_mono` corollary applies this directly to the
unique owners in the actual current `WireFlow` partition. Both modules compile and the complete
`PacketMergeAxioms` guard chain passes. This closes the monotonicity-under-
ownership subgap, so fixed ownership itself is compatible with coherent
threshold targets. Still open: identify the routed intervals with the sorted
output packet embeddings at the next physical cuts, and prove that these
targets evolve by the matching averages required by the
heterogeneous energy-drop lemma. No global recurrence or coefficient
improvement follows yet.

Incidence-sensitive composition (GPT-6-astra-high, 2026-10-16):
`packetized_source_errors_sq_sum_le_of_degree` proves that when each receiver
is incident to at most `k` source cohorts, each source's routed packet errors
have total L1 mass at most its batch error, and errors vanish off the incidence
graph, aggregate receiver squared error is at most `k` times the sum of source
batch-error squares. `packetized_merge_owner_errors_sq_sum_le_of_degree`
composes this with the local merge L1 bound and exact L1 conservation under
packet ownership. Both are kernel checked with standard axioms and registered
in the full `PacketMergeAxioms` guard. This is a reusable invariant interface,
not a new UB-25 recurrence: the actual active-level WireFlow factor-65 bound
was already proved directly. The missing step remains to identify the merge
outputs and their averaged targets with the next physical WireFlow cuts, so
that the pairwise merge/deal energy decrement applies across stages. No global
coefficient improvement follows.

Divisible-cohort signed energy (Codex, 2026-10-16):
`packetFamily64BlockList_merge_heterogeneous_profile_energy_le` lifts the
64-packet signed-error projection to the actual `packetFamily64BlockList` of
disjoint 4096-wire cohorts. Summing the per-cohort estimate gives output
rank-profile energy at most the sum of squared cohort net errors, so
within-cohort zero-sum modes are eliminated before any recurrence-level
bookkeeping. `PacketHalfProfile` and the full `PacketMergeAxioms` guard chain
pass. This closes a sound batch interface only: cohort-mean modes remain, and
the next critical gap is matching these logical cohorts/targets to actual
successive WireFlow cuts so the proved matching-family energy decrement can
be applied. The coefficient is unchanged.

Fixed-count matching-round adapter (Codex, 2026-10-16):
`genIndexedPacketRound_canonicalOutput_fixedCount` reindexes the checked
perfect-matching output family from its list length back to the original
`Fin m` packet IDs, assuming `2 * edges.length = m`. It preserves sortedness
after the actual seven-layer merge-and-deal network, pairwise support
disjointness, and exact support-union conservation. This removes the varying
existential packet-count type as an obstacle to iterating perfect matching
rounds. `PacketInduction` and the full `PacketMergeAxioms` guard chain pass.
Still open: build the uniformly contracting matching schedule with these
length/coverage contracts, iterate its state-dependent supports, and reconcile
the resulting logical packets with physical WireFlow cuts. No coefficient
improvement follows from this adapter alone.

Two-round composition (Codex, 2026-10-16):
`genIndexedPacketRounds_twoStep` now applies the fixed-count adapter twice,
showing sortedness, disjointness, support conservation, and separate seven-
layer costs after two perfect matching rounds. Follow-up
`IndexedPacketRoundState` packages these invariants, and
`indexedPacketPerfectMatching_preservesState` proves a generic one-round
induction step for any perfect matching. The noncomputable
`iterateIndexedPacketPerfectMatchings` now iterates any supplied infinite
schedule, and its step theorem gives the exact network/value recurrence plus
depth at most seven per round. Thus logical sortedness, disjointness, and
support are genuinely closed under arbitrary schedule iteration. This proves
no contraction for any particular schedule and does not establish the
physical WireFlow correspondence; the coefficient is unchanged. The
iteration-step result is included in the `PacketMergeAxioms` guard chain.

Odd-count induction (Codex, 2026-10-16): the fixed-count adapter is now
generalized to partial matchings with an explicit singleton list and length
equation `2 * edges.length + singles.length = m`. `IndexedPacketMatching`
packages exactly this case, and `iterateIndexedPacketMatchings` iterates an
arbitrary schedule on fixed `Fin m`, including odd `m`, preserving sortedness,
disjointness, and support while leaving unmatched packets unchanged. This
removes the even-count/perfect-matching restriction in the logical invariant
transport. It does not certify a contracting schedule, account for residual
singleton energy, or align the supports with physical `WireFlow` cuts.

Physical-order local gate (Codex, 2026-10-16): `joinPacketEmbedding_strictMono`
proves that concatenating two increasing packet embeddings remains increasing
when every wire of the first support precedes every wire of the second.
`dealEvenEmbedding_strictMono` and `dealOddEmbedding_strictMono` show that the
two dealt output embeddings inherit physical increasing order from the joined
embedding. These local facts are kernel checked and guarded. They make explicit
the ordering premise needed for a round to preserve physical-rank packet
embeddings; no theorem yet shows the UB-25 matching schedule satisfies that
premise across rounds.

Round-level order transfer (Codex, 2026-10-16):
`genIndexedPacketRound_output_strictMono` lifts the ordered-pair condition to
every dealt packet in a matching output; the singleton-aware corollary also
retains increasing embeddings for unmatched packets. This is checked and
guarded. It gives a direct reusable gate for adding physical-rank monotonicity
to the iterative state, but the present matching iterator does not impose the
ordered-pair hypotheses at each step.

Physical-state induction (Codex, 2026-10-16): `IndexedPacketPhysicalRoundState`
extends the fixed-count logical state with strict physical monotonicity of
every packet embedding. `indexedPacketMatching_preservesPhysicalState` proves
that any singleton-aware seven-layer matching step preserves this strengthened
state when every edge is oriented so the first support lies wholly below the
second. The theorem is kernel checked and included in `PacketMergeAxioms`.
Together with `packetEmbedding_eq_supportOrderEmbedding`, the next logical
packets are therefore exactly their supports' physical rank enumerations. This
closes the local invariant transport. `iterateIndexedOrderedPacketMatchings`
now packages an adaptive matching policy depending on the current physical
state; its guarded step theorem gives exact value evolution and depth at most
seven per round under the policy's ordered-edge condition. Schedule existence
is still open: a global construction must find an ordered matching at every
evolving state and prove the same schedule contracts the rank-profile
potential. The coefficient is unchanged.

Exact sender-cycle dissipation (Codex, 2026-10-16):
`halfRebin_centered_energy_drop_exact` proves that complementary-half
rebinning at target `h` loses exactly
`2 * sum_i (h - min(h,x_i)) * (x_(sigma i) - h)_+` in centered squared
energy. `senderRepair_centered_energy_drop_exact` instantiates this for the
actual 65 boundary cells, fixed six-layer repair, and cyclic pairing. This
identifies the local mixing mechanism precisely: only a deficit paired with
an incoming surplus dissipates energy. The theorem is guarded and kernel
checked. The exact dead-zone lemmas `halfRebin_eq_self_of_le` and
`halfRebin_centered_energy_eq_of_le` show that when every count is at most 32,
this 65-cycle acts as the identity and contracts no common-target energy.
`senderRepair_lowCount_count_identity` transports this conclusion to the
actual repaired pair counts at every boundary cell. Thus it must be combined
with a distinct phase that mixes low counts, or an invariant must route such
profiles through a different operation with an explicit cost. The near-200
coefficient remains conditional.

Canonical-rank identification (Codex, 2026-10-16):
`packetEmbedding_eq_supportOrderEmbedding` proves that any strictly increasing
64-wire embedding is exactly the order embedding obtained by enumerating its
support in physical order. Combined with the ordered-round result, this
identifies each output's logical embedding with its canonical rank embedding
whenever the matched input supports are separated in physical wire order. The
lemma is in the full axiom guard; it still does not prove the required edge
separation for the actual multiround schedule.

Adjacent matching output block contract (GPT-6-astra-high, 2026-10-16): `adjacentPacketMatchingOutputBlock_contract` packages the two dealt lanes of each adjacent edge as one indexed output block. Each lane is a member of the actual round output, sorted after execution, and strictly increasing on physical wires. Lanes from different output blocks remain fully separated; the two same-block lanes are disjoint and partition the joined 128-wire support. The enclosing perfect-matching round has depth at most 7. The final `PacketGenMerge` through `PacketMergeAxioms` chain passed. This closes one abstract grouped transition, but it neither provides a recursively compatible block matching schedule nor links block placement to later `WireFlow` cuts; there is no contraction or coefficient improvement yet.
