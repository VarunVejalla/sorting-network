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
| `PacketRepair64.lean` | An input-independent ordinary network repairs two physically separated 32-wire supports in six layers. Actual shifted down-cut/up-fringe fragments are sorted under `PacketSortedOn`, which orders each packet but imposes no inter-packet value order. Disjoint repair families have depth at most six and act as the corresponding local merger on each pair. |
| `PacketGenMerge.lean` | An arbitrary injective placement of an ordinary network preserves execution and depth in `Untangle.GenNetwork`. `genMerge_sorts_two_runs` and `genMerge_depth_le` apply at every power-of-two width, including seven layers for 64+64 packets and thirteen for 4096+4096. Dealing has exact floor/ceiling counts, including all value thresholds. Logical packet embeddings can be joined and their fixed parity outputs are disjoint and partition the consumed support. |
| `PacketRebinning.lean` | The scalar complementary-half rebinning model preserves counts and cannot increase positive/negative spill or squared energy around any common real reference. |
| `PacketSenderCycle.lean` | The 65 shifted boundary cells are distinct whole source packets. Actual child and parent repairs consume complementary halves in a fixed cycle and cover exactly those cells. A fixed ordinary six-layer network sorts all 65 repaired pairs and leaves other wires unchanged. `scheduled_senderRepair_exists` instantiates this on actual ordinary scheduled bags with positive down-flow and shifted half-fringes. |
| `PacketCountBridge.lean` | Enumeration-independent true counts, exact prefix/suffix counts of sorted packets, and pairwise count conservation through parallel execution. `senderRepair_count_exists` gives one fixed six-layer network with sorting, exact cycle counts, sender-centered squared-energy nonincrease for every real reference, and unchanged wires outside the boundary cells. `senderRepair_count_at_threshold` transfers its Boolean count contract to all value thresholds of that same network. This is a local sender result, not a destination or global recurrence. |
| `PacketProfile.lean` | Kernel-checked sorted Boolean packet profile for 4096-wire packets split into 64-wire cells. Actual cell counts have the ideal clamp formula. Across any cohort and fractional common mean, aggregate cell-profile L1 error equals the coarse packet-count L1 error exactly; its square is bounded by cohort size times coarse squared error. Connecting this profile to scheduler ports and destination reassembly remains open. |
| `PacketHalfProfile.lean` | Checked clamp-profile and exact L1 / squared-error transfer for 32-wire halves and arbitrary rank intervals. For any cohort, even with packet-specific rank partitions, aggregate routed-slice L1 error equals coarse packet-count L1 error exactly; squared error is bounded by cohort size times coarse energy. Applying this interface to actual sender-flow partitions and proving destination reassembly contraction remain open. |
| `PacketMergeAxioms.lean` | Compile-time axiom guards for the headline local results. Only `propext`, `Classical.choice`, and `Quot.sound` are permitted by the checked messages. |

The correction proof uses adjacent physical wires. It combines the checked
min/max execution identities with the parity front's sortedness, same-rank
order and two-position shift. The terminal pair uses the unchanged final odd
wire. The earlier attempts to identify an infinite extended output sequence
are no longer needed for correctness, although the independent extension
lemma remains proved.

## Reproduction

From this worktree's repository root on Windows:

```powershell
powershell -NoProfile -ExecutionPolicy Bypass -File upper-bound/experiments/packets/check-lean.ps1
```

The script builds the required `StageNet` and `Untangle` library modules,
then checks the scratch modules in dependency order. Scratch `.olean` files
and logs go to `LLM-helpers/ub25-packets`, outside tracked proof sources.
`-From PacketRepair64`, `-From PacketGenMerge`, or `-From PacketMergeAxioms`
is an incremental development option and assumes earlier scratch imports
were already rebuilt after their latest source changes. The default command
checks all scratch sources.

## Remaining proof gates

1. Instantiate the parallel half-packet repair family on every actual receiver,
   including the exclusive parent/child misalignment cases, and prove that the
   resulting packets partition its registers with the required capacities.
2. Carry the logical packet embeddings through matching rounds and positional
   port cuts. `PacketSortedOn` on the physical rank grid is a sufficient local
   premise, not yet an invariant of that combined scheduler. The generalized
   join/deal interface avoids a physical interleaving cost, but it still needs
   a full evolving placement map compatible with the scheduled flow.
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
