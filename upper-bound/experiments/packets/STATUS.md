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
4096-wire mixing cost model. `PacketProfile.lean` now checks a fractional
sorted-profile L1 transfer: the aggregate error across 64-wire cells of a
4096-wire packet equals its coarse count error, with no scale loss. It sums
over packet cohorts and gives the Cauchy bound by cohort size times coarse
squared error. Placement of the ideal profile into the global rank target
and destination recurrence remain open.

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
