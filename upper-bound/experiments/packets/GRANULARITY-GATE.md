# The 64-cell / 4096-packet interface

Research audit by Codex (GPT-6), 2026-10-15. The calculation below is
hand-derived, not a global sorting theorem.

The conditional 197.5 accounting uses 26 merges of two **4096-wire** sorted
packets (13 layers each) and 57 layers of reassembly. The checked sender
repair uses **64-wire** rank cells, with their two 32-wire halves. These
contracts cannot be identified without a change-of-scale argument.

In particular, small variance of large-packet threshold counts does not
imply small variance of the 64-cell counts inside their sorted outputs.
Suppose each sorted large packet has exactly 2048 ones. Large-packet count
variance is zero. Its 64 consecutive 64-cells have counts

```
0, ..., 0, 64, ..., 64       (32 copies of each).
```

Their common mean is 32 and their centered squared-count energy is 65536
per large packet. The new sender repair does not increase this energy, but
it does not make it small either. Thus its zero fresh repair-energy defect
does not itself pass the 4096-packet mixing estimate into the next stage.
This example is an interface obstruction, not a counterexample to the
proposed sorting construction.

More generally, split a sorted `64*K`-wire Boolean packet with `X=64*q+r`
ones, `0<=r<64`, into `K` consecutive 64-cells. Their counts have sum `X`
and sum of squares `64*X-r*(64-r)`. Their energy about `X/K` is exactly

```
64*X - X^2/K - r*(64-r).
```

The next useful mathematical interface should therefore preserve the
**sorted profile**, rather than treating all small cells as approximately
equal to the large-packet mean. Two possible routes are:

1. Carry 4096-packet labels through ports, explicitly price partial large
   packets, and compare their selected counts to the ideal sorted profile
   with the same source mean. Charge perturbations to mixed large-packet
   count deviations, not to the intrinsic 0/64 small-cell variation.
2. Define phase-specific potentials before splitting and after reassembly,
   with an explicit transfer operator between them. Its deterministic
   baseline must account for sorting within each large packet.

There is a simple candidate estimate for route 1. In a sorted `m`-wire
Boolean packet with `X` ones, the number selected by a rank interval
`[a,b)` is

```
f_[a,b)(X) = min(b-a, max(0, X-(m-b))).
```

It is monotone and 1-Lipschitz in `X`. For any partition of the packet into
fixed rank intervals, and `X>=Y`, all selected-count differences are
nonnegative and sum exactly to `X-Y`. Consequently their aggregate absolute
deviation is exactly `|X-Y|`; splitting a sorted profile creates no new L1
perturbation relative to the corresponding ideal sorted profile. The same
holds for unions of partition pieces assigned to destination ports.

`PacketProfile.lean` now kernel-checks the ideal cell-count formula and the
exact L1 identity for these equal 64-rank cells (`profileCell_formula`,
`profileCell_L1_exact`). `sortedBool_prefix_trueCount` and
`sortedBool_profileCell_trueCount` connect that formula to the actual cells
of any sorted Boolean packet. For any cohort of such packets,
`sortedPackets_cellProfile_L1_exact` handles a fractional common mean by
interpolating the profiles at its floor and ceiling: the aggregate absolute
error across all actual 64-wire cells equals the aggregate coarse packet-count
error exactly. `sortedPackets_cellProfile_L1_sq` then bounds the squared
fine-profile error by cohort size times the coarse squared count error. This
is the norm conversion needed to feed the finite matching-cycle L2 estimate
into an aggregate fine-profile budget, with no change-of-scale loss for
sorted packets. The scheduler still needs to carry this ideal profile through
its selected ports and destination reassembly, and the profile target must
match the global bag/rank invariant. This does not supply the unbounded
matching family or global rank contraction.

The repair support uses two 32-wire halves, so the profile transfer is now
also formalized at that exact granularity in `PacketHalfProfile.lean`.
`sortedBool_profileHalf_trueCount` identifies every actual 32-wire rank
fragment of a sorted `32*K`-wire Boolean packet with its ideal clamp profile.
For any cohort, `sortedPackets_halfProfile_L1_exact` gives exact equality
between aggregate fragment-profile L1 discrepancy and coarse packet-count
L1 discrepancy; the squared aggregate is at most cohort size times coarse
count energy. The focused Lean check and axiom guards pass. This closes the
cell-size mismatch in the profile comparison; it still does not show that
the scheduler's selected fragments are compared against those targets, or
that destination reassembly preserves the target profile.

The interval extension is also checked: `sortedBool_rankInterval_trueCount`
identifies the actual count in every half-open interval `[a,b)` of a sorted
Boolean packet with `profileInterval`; `profileInterval_change_le` proves
that any one fixed interval's count changes by at most the change in total
packet count. Thus source-port slices of differing fixed ranks can each be
compared to their own ideal targets without a factor for interval length.
`sortedPackets_individualIntervalPartitions_L1_exact` closes that next
algebraic step: every packet may have its own monotone rank partition, and
the aggregate absolute error across all actual slices is still exactly the
coarse packet-count L1 error. Its squared version bounds aggregate fine
error by cohort size times coarse squared energy. Thus arbitrary port counts
and different per-sender cut locations incur no norm-conversion loss,
provided the routed slices form a full rank partition of each sender packet
and are compared with the induced ideal slice targets. The remaining gap is
to verify those partition hypotheses for the actual scheduled senders and
show destination reassembly/matching uses the corresponding targets to
contract global rank error.
The abstract partition theorem now has a concrete sender instance.
`trueCountOn_blockOf_profile` turns any sorted Boolean threshold on a wire
bag into the ideal count on each actual rank block. `senderOutgoingPiece`
splits the sender's up-fringe into its two disjoint intervals and lists its
64 down blocks; `senderOutgoingPieces_are_WireFlow_ports` identifies those
pieces with the actual `upSet` and `downSet` ports. The checked
`sortedSenderOutgoing_profile_error_exact` theorem then gives exact aggregate
L1 transfer across all 66 routed pieces for cohorts with a common bag size,
even when each sender has its own up/down parameters. Therefore the full
sender's routing introduces no port-count loss in the threshold profile
error. The remaining issue is receiver-side selection and reassembly: prove
that the selected pieces' ideal profiles add to the required receiver rank
target and that merge-and-deal contracts the resulting global rank error.
The checked `selectedSenderOutgoing_profile_error_le` makes the first part
of selection quantitative: any subset of routed pieces has aggregate
absolute source-profile error at most the cohort's coarse sender-count L1
error. This bound is independent of how many pieces the receiver selects.
It controls deviations around the senders' ideal targets; the unresolved
term is the difference between the sum of those selected ideal targets and
the receiver's required target profile.

The size and mean restrictions are now removed. The checked
`sortedSenderOutgoing_profile_error_exact_var` and
`selectedSenderOutgoing_profile_error_le_var` permit a different source
length and fractional ideal count for every sender, matching the actual
parent/child size asymmetry in `WireFlow`. More directly,
`selectedSenderOutgoing_count_error_le_var` bounds the absolute error of the
receiver's combined selected threshold count relative to the sum of its
selected ideal interval counts by the total coarse sender error. The estimate
has no port-count factor. The destination-target identification and the
multi-run merge/deal contraction are still open.

Dynamic receiver target (2026-10-15): the checked `wireFlowLayer_reencoded_profile_recurrence` chooses the selected interval-mean sum as the next target profile for every active receiver and every threshold. It proves the codes remain monotone and within receiver capacity, and the summed actual register error is charged to source coarse errors exactly once. Thus target identification is no longer a mismatch with a preselected target; the remaining main gap is proving sortedness of the source registers at each cycle and proving the reassembly/mixing contraction for the resulting dynamic profile.

## Exact 128-wire phase baseline

The checked physical-half formula and parity-count theorem determine the exact
energy transfer for each Boolean threshold. If a fully merged 128-wire block
has `H` ones, its physical half-counts are
`a=min(64,max(0,H-64))` and `b=min(64,H)`. The doubled centered energy of
these two counts is

```text
(2a-H)^2 + (2b-H)^2 = 2 * min(H,128-H)^2.
```

The logical even/odd dealt counts are `floor(H/2)` and `ceil(H/2)`, whose
doubled centered energy is 0 for even `H` and 2 for odd `H`. In particular,
at `H=64`, logical energy is zero while physical energy is 8192 in this
normalization. A recurrence that changes between logical packet counts and
physical rank-cell counts must subtract this deterministic, `H`-dependent
baseline before comparing errors. The identity is an immediate arithmetic
consequence of the checked count formulas; it is a candidate phase-specific
potential, not a contraction theorem for the 4096-wire stages or scheduler
reassembly.

## A concrete 57-layer merge-tree target

There is a simple structural way to spend exactly the conditional 57-layer
reassembly budget, if the actual receiver can be reduced to 64 sorted
64-wire runs. Merge adjacent pairs first (128 wires, `oddEvenMergeNet 7`),
then merge adjacent 128-wire runs (256 wires, `oddEvenMergeNet 8`), continuing
through the 4096-wire output (`oddEvenMergeNet 12`). At each tree level, the
component merges act on disjoint intervals and run in parallel. Inductively
each component emits one sorted run, and the depth is

```text
7 + 8 + 9 + 10 + 11 + 12 = 57.
```

The local correctness and depth lemmas for every two-run merge already exist
in `OddEvenMerge64.lean`; this is a concrete candidate construction for the
57 layers, rather than an unexplained allowance. It is not yet instantiated
as a 4096-wire merge-tree theorem, and the actual `WireFlow` receiver assembly
has not been shown to present exactly 64 contiguous sorted runs of 64 wires.
Proving that interface (or finding its actual run count and widths) is the
next test of whether this structural use of all 57 layers is viable.

There is a useful refinement to the interface test: physical contiguity of the
64 input runs is not necessary in the generalized-comparator model. The
receiver assembly theorem gives an arbitrary disjoint family of sorted
64-wire supports, and `genScatter` can place a fixed comparator network on any
injective support map. Thus the receiver's family can be grouped by packet ID
into blocks of 64 and each full block treated as 64 concatenated logical runs.
The exact obstacle is now the incomplete final block (fewer than 64 packets)
and proving/instantiating the 4096-wire merge-tree on arbitrary disjoint packet
supports. A complete UB-25 stage also needs the output re-packetization to
agree with the next scheduler's required ports. In particular, the earlier
wording that asks for “64 contiguous runs” is unnecessarily restrictive, but
the 57-layer budget is not yet justified for the actual receiver.

The exact scheduled packet-count factorization narrows the incomplete-block
case. For packet count `C = flowA7/64`, `flowA7_packet_count_block_shape`
proves that `C` is zero, one, divisible by 64, or has `C % 64 = 63` with
`C >= 4095`. In the last case, the ungrouped tail is exactly 63 packets and
at most `63/4095 = 7/455` of the cohort. The theorem
`flowA7_packet_tail_fraction_le` verifies that ratio in Lean. This makes the
tail bounded and sparse, but does not yet prove that its sorting/rebinning cost
fits the depth budget or that its error can be absorbed by the global
recurrence.

Padding the 63-run tail to 64 runs with sentinel wires and then deleting those
wires is not automatically valid. The generic wire-deletion rule fails even
for the 3-wire sorting network `(0,1),(1,2),(0,1)`: deleting its middle wire
and incident comparators leaves no comparator on the two remaining wires.
The 63-run case therefore needs an actual unequal-run merge construction (or
a proved projection theorem tailored to the 64-run merge tree), with depth at
most 57. This is the next local network gate before charging the tail in the
global recurrence.

The alternating two-chain microcase has now been screened separately. On the
128-wire support word `AB` repeated 64 times, `alternating_chain_screen.py`
produces an explicit 14-layer comparator network that sorts every one of the
`65*65 = 4225` legal Boolean threshold inputs. The comparator layers are
stored in `alternating_chain_128_screen.json`; `sorts_all_threshold_states`
is checked by the script. The network is a valid finite upper-bound candidate
for this fixed support pattern, but the greedy search proves neither minimum
depth nor correctness for any other support pattern or the whole receiver.
It shows that the earlier six-layer allowance cannot simply be assumed for
an alternating support, while leaving open whether this 14-layer repair can
be absorbed into the 57-layer budget by a receiver-wide construction.
