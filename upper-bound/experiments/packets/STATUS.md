# UB-25 packet-balancing status

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

No new Lean adapter theorem or matching schedule has been added. The fixed
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
