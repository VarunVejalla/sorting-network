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

Scheduler audit (2026-10-14): the proposed 64-fragment receive is not the
checked Chvatal flow. Each child receives one variable-size positional
`downSet` block from its parent and the union of up to 64 child `upSet` tails;
the flow proves wire counts, not sorted-run structure. The 57-layer reassembly
and 197.5 gate therefore have no current scheduler realization. See the
port-flow audit in `MIXING-TAIL.md`. First test a scheduler-shaped port
instance before investing in an unbounded matching-family certificate.
