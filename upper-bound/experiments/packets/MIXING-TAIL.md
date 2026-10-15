# Rounded matching-cycle bulk and tail interface

Current proof status (2026-10-15): see [README.md](README.md). The complete
odd-even merge sorting induction, fixed-support six-layer repair, parallel
repairs, and support-independent generalized packet merge/deal adapter are
now kernel checked. Historical statements below that call the 64-wire merge
proof open are superseded. The unbounded mixing/discrepancy family, evolving
packet/port placement and global rank recurrence are still open; no improved
limsup coefficient is claimed.

The new [sender-local energy note](REBINNING-ENERGY.md) gives a stronger
rebinning interface: its scalar model preserves counts and cannot increase
spill or variance around any common sender reference. Those inequalities
are kernel checked. The 65-cycle representation and exact executed count
formula for the shifted sender's actual half-packet pairing are now checked
in `PacketSenderCycle.lean` and `PacketCountBridge.lean`. The complete
evolving packet partition and its use in the global recurrence remain open.

Status: hand-derived conditional lemma plus a finite floating-point screen.
No explicit unbounded matching family or sorting-network improvement is
proved.

## A uniform per-packet estimate from a spectral cycle

Let `c` equal-size sorted packets be mixed by `s` fixed perfect matchings.
On each matched pair, merge and deal maps Boolean threshold counts by
`(x,y) -> (ceil((x+y)/2), floor((x+y)/2))`. Write `A_t` for exact real
averaging on matching `t`, `P=A_s...A_1`, and assume

```text
||P z||_2 <= rho ||z||_2   for every zero-sum z.
```

For one threshold, let `x_j` be the input count in packet `j`, with
`H=sum_j x_j`. One rounded matching is `x' = A_t x + e_t`: on each pair the
rounding errors are `(+1/2,-1/2)` or `(0,0)`. Thus `sum e_t=0`,
`||e_t||_2 <= sqrt(c)/2`, and `||e_t||_infinity <= 1/2`. Expanding all `s`
rounds gives

```text
x_out = P*x + sum_(t=1..s) A_s...A_(t+1)*e_t.
```

Each averaging matrix is doubly stochastic and contracts `L2` and `Linf`.
Therefore, with `z=x-(H/c)1`,

```text
||x_out-(H/c)1||_2 <= rho*||z||_2 + s*sqrt(c)/2,
max_j |x_out[j]-H/c| <= rho*H + s/2.
```

For the second inequality, `P` is doubly stochastic and every entry differs
from `1/c` by at most `rho`: apply the spectral hypothesis to
`e_j-(1/c)1`, whose norm is at most one. Each propagated rounding-error
coordinate is at most `1/2`. The bound applies independently to every
Boolean threshold and therefore to both orientations of rank error. It
handles the singleton obstruction by allowing an explicit additive fringe
of `s/2` per packet; it does not claim a singleton spreads.

For `0<=x_j<=m`, `||z||_2^2 <= mH`. Since `sum z=0`, the one-sided bulk
leakage satisfies

```text
sum_j (x_out[j]-H/c)_+
  <= (sqrt(c)/2)*||x_out-(H/c)1||_2
  <= (rho/2)*sqrt(c*m*H) + s*c/4.
```

This gives a two-regime interface: square-root bulk control for larger
cohorts, and a per-packet `rho*H+s/2` upper tail for small cohorts. A
scheduler can use it only if it explicitly carries or repairs the `s/2`
fringe at every packet boundary and accounts for it across all active rank
thresholds.

## Finite cycle screen

`matching_cycle_screen.py` samples independent random perfect matchings and
computes the top singular value of `P-J/c` in binary64. With ten trials per
size, all sampled 26-round products for `c=16,32,64,128,256,512,1024` had
measured `rho < 0.0011`; the largest observed median was `0.0009668` at
`c=1024`. The
fixed reproducible PCG64 seeds and measured norms are saved in
`matching-cycle-screen.json`. Thirty rounds measured still smaller norms.

These measurements are an encouraging finite feasibility screen only. They
are not outward-rounded spectral certificates and do not give a family for
unbounded `c`. In particular, a random sample for each finite size cannot be
substituted for the uniform explicit matching family in the ticket.

## Depth gate and remaining scheduler test

For packet length `m=2^12`, the merge-and-deal operation costs 13 layers.
Twenty-six matching rounds cost 338 layers. If the 64-fragment receive pattern
can be implemented with six balanced merge levels, the previously derived
57-layer reassembly cost gives 395 total layers, or coefficient 197.5 at two
bits of scale per cycle. This leaves only 2.5 coefficient units before any
other work. The additive 13-key-per-packet fringe from the rounded cycle is
not a comparator-depth charge by itself, but may force extra repair or larger
fragments; that cost is not included in 197.5.

The next decisive result is either an explicit unbounded matching family with
a certified `rho` strong enough for the coupled cohort invariant, plus a
complete ordinary/frontier port-flow proof charging that fringe and all
reassembly, or an obstruction showing those costs exceed the gate. The
existing 26-round figure and this finite screen do not establish either.

## Audit against the checked Chvatal port flow

The “64-fragment receive” in the depth gate is not currently an interface in
the checked scheduler. `WireFlow.parentPart` selects one `downSet` block from
the parent, indexed by the child number, while `childPart` unions the `upSet`
tails from all 64 children. The child’s register set is exactly this union
(see `ExecPlacement.execPlacement_succ_regs`). These are positional rank
blocks of arbitrary cardinalities prescribed by `FlowSizes`, not 64 equal
sorted packets of length `2^q`. In particular, the existing identity
`a = up + 64*down` only counts wires; it does not assert sorted runs, nor
that the parent block or each child tail is a sorted fragment.

Consequently the 57-layer balanced merge estimate has no proved application
to this receive set. Even if packet labels were carried through the ordinary
network, the current receive has a variable parent middle block plus up to 64
child tails, with frontier cases where one side vanishes. The current
stranger invariant controls how many keys lie outside ancestor rank intervals;
it does not give within-block sortedness. This is the concrete global gap
behind the earlier phrase “trace sorted packets through a complete routing
cycle.”

The 197.5 coefficient gate therefore cannot be interpreted as a modification
of one existing Chvatal stage. It would require a new node/port contract that
simultaneously (i) emits sorted runs aligned to the prescribed `downSet` and
`upSet` rank blocks, (ii) bounds the rounded mixing fringe for every active
threshold, and (iii) receives those differently sized runs with a priced
merge/repacking network. No such contract follows from the current
`StageKernel`; replacing its stranger estimates with the spectral estimates
alone would leave the placement and sortedness obligations unproved.

## Fixed-label placement gate (2026-10-14)

The direct application of the six-layer 32+32 merge to each proposed fragment
pair is not yet justified by `wireSets_succ_eq`. That identity gives a union of
the parent's `downSet` and the children's `upSet`s; `execPlacement_succ_regs`
then gives the corresponding union of their key images. The packet lemmas
establish that each contributing fragment is sorted in its own sender's wire
order, but do not establish that a pair occupies the lower/upper 32 positions
of a fixed 64-wire block in the receiver's physical wire order.

This distinction is essential: for example, source wire sets `{0,2}` and
`{1,3}` can each carry increasing values (`0,3` and `1,2` respectively), while
their union in physical wire order carries `0,1,3,2`, which is not a single
sorted run. Thus set union, rank-interval alignment, and per-source sortedness
alone do not give the input layout assumed by `bitonicMerge64`. A fixed
comparator network could still route/merge these fragments, but its cost and
correctness need a separate proof.

There is a fixed-label fallback for the local pairing step. Once two disjoint
32-wire fragments are selected by a deterministic rule from the flow sets,
their union is a fixed 64-wire Finset. Embed the ordinary 64-wire bitonic
sorter into that union in increasing physical-wire order. This needs no
assumption about how the two fragments interleave and sorts all 64 values;
the mapping is input-independent. Its depth is at most 21 (`6*7/2`), rather
than the six layers of the bitonic merge that presumes two contiguous sorted
halves. Pairwise-disjoint fragment unions can be processed in parallel, subject
to proving the actual pairing partitions all half-fragments and the whole
packets are left compatible with the next operation.

The generic Lean adapter is now in `PacketAlignment.lean`:
`bitonicSort64_scatter_sorts` proves sorted output on any increasing embedding
of 64 physical wires, and `bitonicSort64_scatter_depth_le` proves the 21-layer
bound. This certifies the local construction independently of any contiguous
layout. It does not yet instantiate that embedding for all fragments of an
actual receiver or prove the embeddings are pairwise disjoint.

The natural pairing is sender-local and is now captured by additional generic
Lean lemmas. For a shifted parent down-cut, pair the 32 ranks at the left end
with the 32 at the right end (`rankInterval_endpoint_pair`). For each shifted
child up-fringe, pair the final 32 ranks of its prefix with the first 32 ranks
of its suffix (`upFringe_endpoint_pair`, `upFringePairSupport_card`). Each such
pair support has exactly 64 wires. `scheduledUpFringePairSupport_disjoint`
proves that supports belonging to distinct scheduled senders are disjoint,
using the checked `wireSets_disjoint`; hence all 64 child pairs can execute in
parallel. The receiver misalignment exclusivity says the active alternative
is either these 64 child pairs or the single parent-cut pair.

This closes the combinatorial pairing choice and pairwise support-disjointness
at the reusable lemma level. The endpoint-pair lemmas still take the flow
shape premises as hypotheses; a single theorem instantiating them for every
ordinary receiver is not yet present. More seriously, this does not compose
with the next 13-layer matching operation: that operation expects two sorted
packets in its ordered lane layout, while these fixed supports can be
interleaved in physical wire order.

There is a sound general-support transition, but its price is high. For any
two disjoint 64-wire supports, sort their 128-wire union in physical order and
define the next two supports to be its even- and odd-ranked wires. The new
packets are sorted and interleave rank-by-rank, so the construction composes
with another arbitrary support matching. `PacketAlignment.lean` now proves
`bitonicSort128_scatter_sorts`, its 28-layer bound, and
`bitonicSort128_scatter_parity_profile`, which certifies the interleaving
profile. This is input-independent and gives an invariant interface for a
redesigned support schedule. Replacing each 13-layer matching operation by a
28-layer sorter changes 338 cycle layers to 728; retaining the 57-layer
reassembly budget gives a conditional 785-layer total, coefficient 392.5 at
two bits per cycle. It is a correctness fallback, not a route to 200.

The practical next research gate is to find a cheaper merge-and-deal network
for two arbitrary interleaved sorted supports and prove that its output
supports feed the next matching round, or else redesign the initial port
layout so the ordinary 13-layer operation remains applicable.

This fallback closes only local label placement. If it replaces the six-layer
pair repair inside the 395-layer gate (338 mixing + 57 reassembly), the
conditional total becomes 410 layers, or coefficient 205 at two bits per
cycle. So the straightforward robust fix misses the 200 target, before other
costs. The six-layer saving requires an actual layout-aware merge network for
the interleaved supports, or a port design that places each pair in ordered
halves. In addition, the following mixing cycle must consume the resulting
abstract packet sets at fixed labels; local sorting alone does not establish
that global adapter.

The next decisive gate is therefore to prove the fixed deterministic pairing
and test whether a comparator network can merge each pair at a price below 6
layers (or redesign packet supports to be physically ordered), then show the
next matching operation is compatible with those supports. If not, the
current 197.5 gate is not salvageable by simply adding a routing lemma; a
layout-aware port construction is needed.

This changes the early gate: before spending effort on an unbounded spectral
matching-family certificate, first find a finite scheduler-shaped port
instance and demonstrate the required sorted-run decomposition and receive
merge cost. If the exact `downSet`/`upSet` shapes do not admit that interface,
UB-25 needs a redesigned flow (and likely a new rate analysis), not just a
better matching cycle. This is a structural compatibility finding from the
checked definitions, not an impossibility theorem for redesigned schedules.

### Fixed-packet boundary arithmetic (m = 4096)

There is a favorable refinement: the positional ports are not arbitrary with
respect to a 4096-wire packet grid. In every non-frontier `mid` node,
`down = (64^3-1)·64^(g+2)` is divisible by 4096. Its half-fringe is
`up/2 = 4095·32·64^g`, which is divisible by 4096 for `g ≥ 2`; at `g=0` it
has residue 4064 modulo 4096, and at `g=1` residue 2048. Similarly, `botDesc` has
`down = 64^g-64^(h+2)`, divisible by 4096, and
`up/2 = 4095·32·64^h`, aligned for `h ≥ 2`, residue 2048 at `h=1`, and
residue 4064 at `h=0`.
For `topRise`, `up/2 = 32·64^(1+f)`, aligned for `f ≥ 1` and equal to
2048 at `f=0`. `topDesc` has no up-fringe. Thus most ordinary bulk cuts
preserve packet boundaries exactly; the exceptional exponents create a
bounded packet-boundary defect (at most one partial packet at a given cut),
not arbitrary raggedness.

This makes the next port test materially more promising: assume each node's
register order is partitioned into contiguous sorted 4096-wire packets, then
check how `parentPart` and the 64 child `upSet`s split those packets using the
exact residues above. It should first establish a run-level transport lemma,
including the few frontier residues, before pricing any merging. It still
does not validate the 57-layer estimate: a receiver can inherit many packet
runs (two fringe intervals from each child plus a parent middle interval),
and their count/length profile must be fed into a real repacking network.
Nor does the current separator theorem provide the assumed packet ordering.
This is an exact divisibility calculation from the `NodeShape` formulas in
`FlowSizes7.lean`, not a kernel-checked new theorem.

### One exact ordinary-stage port instance

For `d=20`, `t=20`, take a receiver at level 7 at time `t+1`; its parent is
level 6 and its 64 children are level 8. The source `NodeShape` cases are a
parent `mid(g=3)`, each child `botDesc(g=11,h=7)`, and the receiver
`mid(g=4)`. With packet size 4096, exact integer arithmetic gives:

```text
parent down block:       64^7 - 64^3       = 4,398,046,248,960 packets
each child's up fringe:  4095*64^6         =   281,406,257,233,920 packets
all 64 child up fringes: 4095*64^7         = 18,010,000,462,970,880 packets
receiver capacity:       64^9 - 64^3       = 18,014,398,509,219,840 packets
```

Here “packet” in the display means one 4096-wire packet: the child number
uses the exact `FlowSizes7.NodeShape` wire count divided by 4096. Both
half-fringes of every child and the parent block are packet-aligned, and the
packet counts add exactly to the receiver capacity. Thus this concrete
ordinary port transports intact packet objects; the 129 source intervals
(one parent interval and two per child) can be assigned packetwise without
comparison-based merging, assuming each source node already has the packet
invariant. The machine-readable exact check is
`port_alignment_instance.py` / `port-alignment-instance.json`.

This is substantially better than a 129-run merge estimate: an interval can
contain a long sequence of packet objects, but aligned boundaries mean the
objects need not be merged just to restore packet height. What remains is a
fixed-label/placement proof that packets from those intervals can occupy the
receiver's packet slots and that each subsequent matching cycle uses those
labels consistently. The instance is only a source-formula model, not an
instantiated Lean `wireSets` theorem; top/bottom exceptions and the complete
ordinary/frontier induction are still open. It does, however, pass the first
bulk port gate and makes a no-repacking bulk variant worth pursuing.

### Finite top/bottom frontier screen

`frontier_alignment_screen.py` mirrors the exact rational schedule formulas
and checks every active level at ordinary times `2 ≤ t < tf7(d)` for
`7 ≤ d ≤ 40`. Across 1,650 stages and 5,900 active bag instances, all
receiving-flow identities passed. The only observed residues modulo 4096
were:

```text
bag sizes:       5,628 residue 0; 272 residue 4032
down intervals:  5,628 residue 0; 272 residue 4032
up half-fringes: 5,067 residue 0; 561 residue 2048; 272 residue 4064
```

The count by shape role is also informative: every nonaligned down interval
was a top-frontier case; nonaligned bag sizes occurred at the low-exponent
mid or bottom frontier; fringe residues came from top, bottom, and the
smallest mid exponents. In all these cases the remainder is within 64 wires
of a packet boundary, except the half-fringe residue 2048, which is exactly
half a packet. Thus the data support a stronger candidate interface than
“all intervals aligned”: each port interval is a sequence of complete
4096-packet positions plus at most two partial boundary pieces. Bag
capacities have a canonical arithmetic decomposition into full packet
positions and at most one terminal remainder; the screen does not show that
source packet contents assemble into this decomposition intact.

The finite screen is not itself a universal theorem. A hand case split over
the schedule's `NodeShape` formulas gives the uniform residue classification
below. The JSON still records only the finite enumeration.

### Hand derivation of the residue classes

The universal modular calculation itself is short. Modulo `M=64^2=4096`,
`64^k` is `1` for `k=0`, `64` for `k=1`, and `0` for `k≥2`. The `topDesc`
shape has `g≥2` in the actual schedule: `exp_top` gives capacity exponent at
least 3, while this shape's exponent is `g+1`. Substituting the source
`NodeShape` formulas therefore gives this complete table (all entries are
residues modulo 4096):

| shape | bag size `a` | half fringe `up/2` | child block `down` |
|---|---:|---:|---:|
| off | 0 | 0 | 0 |
| topDesc (`g≥2`) | 0 | 0 | 0 |
| topRise | 0 | 2048 if `f=0`, else 0 | 4032 if `f=0`, else 0 |
| mid | 4032 if `g=0`, else 0 | 4064 if `g=0`; 2048 if `g=1`; else 0 | 0 |
| botDesc | 4032 if `h=0`, else 0 | 4064 if `h=0`; 2048 if `h=1`; else 0 | 0 |
| botRise (`h≥2`) | 0 | 0 | 0 |

For `botDesc`, `g≥h+2` makes the `64^g` term vanish modulo `M`. For `botRise`,
the shape constructor only records `h≤g`, but schedule constraints improve
this to `h≥2`: since `omega` does not rise, parity and the unit-step property
give `omega(t+1)=omega(t)-1`; applying `t+2≤3ω(t)≤t+6` at both times forces
`3ω(t)=t+6`. Then `t<3d-20` gives `3d≥t+21`, so
`h=d+2ω(t)-t-9≥2`. Similarly, `topDesc` has `g≥2` by `exp_top` as noted
above. These two schedule side conditions make the table valid for every
active ordinary stage covered by `shape_rat`. This is a hand derivation, not
yet a Lean lemma.

It yields a precise wire-layout consequence. Each `downSet` is one contiguous
interval of length `down`, and each `upSet` is two contiguous intervals of
length `up/2`. Their endpoints can be off the 4096-grid, but each interval
intersects at most two partial 4096-packets; its interior consists of whole
packets. A receiving bag's wire count has a canonical arithmetic
decomposition into full 4096-wire slots plus (only when its residue is 4032)
a final 4032-wire slot. The residue calculation does not show that incoming
sorted packet objects can actually be assembled into those slots intact.
Existing partial pieces may also be carried through later ports, so their
count needs its own recurrence; merge-and-deal currently expects equal-size
inputs. That fragment-flow invariant is now the decisive gap, ahead of the
spectral-family certificate.

### A cleaner candidate: 64-wire packets

The same shape formulas are unusually clean modulo 64. With the schedule
side conditions `topDesc.g≥2` and `botRise.h≥2`, every active bag size and
every down-block is divisible by 64. Every up half-fringe is either divisible
by 64 or congruent to 32. In the latter case the source bag length is a
multiple of 64, so each of its two fringe intervals contains exactly one
32-wire partial packet; all other packets in those intervals remain whole.
The residues by shape are: `topDesc`, `topRise`, and `botRise` give
`(a,up/2,down)=(0,0,0)`; `mid` gives `(0,32,0)` exactly at `g=0` and
`(0,0,0)` otherwise; `botDesc` gives `(0,32,0)` exactly at `h=0` and
`(0,0,0)` otherwise; `off` is `(0,0,0)`. These follow by reducing powers
of 64 modulo 64 in the displayed shape formulas.

For a receiver, let `εp` indicate that its parent half-fringe is 32 mod 64,
and `εc` the same for each child half-fringe. The 64 siblings have identical
flow sizes. The parent down interval starts at `up_parent/2 + j*down_parent`,
and `down_parent` is a multiple of 64, so it contributes `2 εp` sorted
32-wire pieces. The child `upSet`s contribute `2·64·εc` such pieces. Thus
the receiver gets

```text
F = 2 εp + 128 εc ∈ {0, 2, 128, 130}
```

half-packets. Pair them in a fixed order. Each pair consists of two sorted
32-runs; reverse one and apply the 64-wire bitonic merge, yielding one sorted
64-packet in at most 6 layers. `F` is even, and flow conservation plus the
receiver's 64-divisible capacity ensures that the untouched full packets and
the `F/2` repaired packets fill the receiver exactly. This gives a clean
one-stage port repair interface, conditional on the packet labels being
carried through the node networks.

`packet64_repair_screen.py` checked 46,926 receiver instances from 1,650
ordinary stages for `7≤d≤40`; all flow identities and packet-count checks
passed. The observed fragment counts were 0, 2, or 128 (the symbolic bound
allows 130). The script is an exact rational model of `FlowTable`/`NodeShape`,
not a Lean placement proof. The hand residue proof is the same six-case
calculation as above, reduced modulo 64; the output data are in
`packet64-repair-screen.json`.

The local cost model is enticing: a merge-and-deal round on two 64-wire
packets costs 7 layers, so 26 rounds plus at most 6 repair layers costs 188
per scheduled node operation. If the existing `3d` ordinary-operation rate
and all rank obligations survived, this would price to coefficient
`3·188/6 = 94`, leaving substantial room below 200. This is only a cost gate;
it does not account for root/terminal work or prove any global sorting bound.

There is a serious precision tradeoff. With `m=64` and `s=26`, the rounded
cycle's additive bulk-leakage floor from the earlier inequality is
`s/(4m(1-rho))`, about `0.102` of the normalized packet mass for `rho≈0`
(the L1 deviation floor is about twice that). This may be far too large for
a useful rank-profile recurrence.
The next gate should therefore compare the coupled global rank budget against
this exact rounding floor, and then search for the largest packet size whose
finite fragment pieces still admit a cheap deterministic repair. Port
compatibility is no longer the main obstacle; precision versus repair depth
is.

### Exact integer-cycle check (14 October 2026)

The preceding `0.102` estimate is a worst-case perturbation bound, not a
measured floor. To check its scale, `integer-rounding-screen.py` applies the
exact oriented update `(a,b) -> (ceil((a+b)/2), floor((a+b)/2))` to seven
threshold-count profiles under the reproducible 26-round schedules from
`matching_cycle_screen.py`. For packet counts 64 through 1024, all tested
profiles ended with coordinate range at most 2. The largest observed
positive-spill fraction was about `0.0039` (uniform random at 256 packets),
versus the crude bound `0.102`; the singleton profile also mixed to a spill
fraction below `0.004` in these schedules. Data are in
`integer-rounding-screen.json`.

This is finite numerical evidence only. It neither bounds all initial profiles
nor establishes an unbounded family of schedules. It does remove the measured
10% leakage as a reason to reject packet size 64: the next mathematical gate is
a pathwise or profile-aggregate discrepancy theorem for integer merge-and-deal,
strong enough to close under the coupled rank recurrence. In particular, the
singleton tail remains present and must be charged explicitly; the screen does
not solve that tail problem.

### Adversarial profile search (14 October 2026)

To test whether the seven hand-picked profiles understated the leakage,
`adversarial-rounding-search.py` runs single-coordinate simulated annealing on
both Boolean endpoint profiles `{0,64}^c` and unrestricted integer profiles
`{0,…,64}^c` for the fixed 26-round schedule at each packet count. Five
restarts of 6,000 proposals each were run for `c=64,128,256,512`. The largest
found spill fractions were respectively `0.3906%`, `0.3906%`, `0.3937%`, and
`0.3922%`; all best profiles ended with coordinate range at most 2. At `c=64`
the best spill is exactly `16/(64·64)`, attained with final range 1.

This search did not raise the observed spill materially, and repeated restarts
converged to the same small values. It is still only a heuristic search on one
fixed cycle per size, so it is not a worst-case certificate. The next rigorous
step remains proving a uniform final discrepancy bound for every initial
profile under these cycles (or an explicit bound on their rounding error
operator), then checking that bound against the rank-profile recurrence.

### Uniform finite-cycle discrepancy bound (14 October 2026)

A deterministic all-profile bound is available for each fixed schedule. Write
one rounded update as `x[t+1] = A[t] x[t] + e[t]`, where `A[t]` averages each
matched pair and the two coordinates of `e[t]` on an edge are opposite, each
of magnitude at most `1/2`. For output coordinates `i,j`, let `P` be the full
exact-averaging product and `Q[t]` the exact suffix after update `t`. Then for
all integer profiles `x[0] in [0,64]^c`,

```text
|x[s]_i - x[s]_j|
 <= 32 * ||P_i - P_j||_1
    + (1/2) * sum_t sum_(l,r in matching[t])
        |(Q[t]_i,l - Q[t]_i,r) - (Q[t]_j,l - Q[t]_j,r)|.
```

The first term maximizes the initial-profile contribution over the box; each
later term maximizes the oriented pair-rounding error independently. For the
fixed seeded cycles, `rounding-error-bound.py` evaluates the right side with
exact integer numerators over `2^26`. The resulting maximum pairwise bounds
are `239852089/33554432` (about 7.148), `70057751/8388608` (about 8.352),
`76324557/8388608` (about 9.099), and `335730353/33554432` (about 10.006)
for 64, 128, 256, and 512 packets. Since final coordinates are integers,
their ranges are at most 7, 8, 9, and 10. A vector with range `R` has positive
spill at most `cR/4`; normalized by the `64c` total packet mass, this gives
caps `R/256`, or 2.73%, 3.13%, 3.52%, and 3.91%.

This is a valid uniform bound for every initial profile under each listed finite
cycle, and it materially improves the earlier 10.2% estimate. It is still too
loose to explain the 0.39% search results, and it does not establish a uniform
family of schedules as `c` grows. The selector MILP attempt to prove actual
range at most two did not close in the time budget. The next proof target is to
exploit the dependence and sign structure of the rounding errors, rather than
bounding each error independently, and then sum the resulting threshold
leakage through the global rank recurrence.

### Proof boundary and old-kernel comparison (14 October 2026)

A bit-vector SMT query over all 64-packet inputs asking whether any final
profile has range at least 3 timed out after 120 seconds. A query for the
single output pair attaining the largest perturbation envelope also timed out
after 45 seconds. Thus the finite perturbation calculation above is currently
the strongest all-profile statement; the range-1/2 observed in searches is not
proved.

The spill caps `R/256` (2.7% or more here) cannot be inserted into the existing
Chvatal `StageKernel`: its bulk and fringe allowances are `1/59,000,000` and
`1/86,000,000`. The packet-cycle route therefore needs a new rank invariant
that aggregates cancellation and leakage across thresholds/stages. A
per-threshold worst-case range bound alone misses that structure by over six
orders of magnitude. This comparison is a design constraint, not a no-go for
UB-25, whose target scheduler is allowed to use a different invariant.

### Aggregate fresh-error budget and missing recurrence

For a scheduled node operation `v` acting on `c_v` sorted 64-wire packets, let
`T_v` be the set of Boolean thresholds that the proposed global rank profile
actually tracks. The finite exact-cycle bound gives, for each tracked threshold,
positive spill at most `c_v R(c_v)/4`, where `R(c)` is the integer final-range
bound (currently computed only for `c=64,128,256,512`). Thus the fresh error
for that operation is bounded by

```text
Fresh(v) <= |T_v| * c_v * R(c_v)/4.
```

For the tested `c=64` cycle this is 112 count-units per active threshold, or
2.734% of that operation's 4096 wires; for the generic 26-round spectral
perturbation estimate it is `6.5*c_v` per threshold, or 10.156% of its wire
capacity. For an entire stage `t`, the corresponding budget is
`sum_(v active at t) Fresh(v)`. Across the actual `3d-21` ordinary operations
on a Chvatal path, the raw sum is

```text
sum_(t=1..3d-21) sum_(v active at t) |T_v| * c_v * R(c_v)/4.
```

This is the correct fresh-error sum interface, but it is not yet a closed rank
recurrence: the UB-25 proposal does not define `T_v`, a state `E_t` measuring
rank-profile error, or the propagation/contraction inequality relating
`E_(t+1)` to `E_t` and `Fresh(t)`. If one simply adds a fixed relative allowance
`eta` at every ordinary operation, the budget grows like `(3d-21)*eta`; that
cannot yield a bounded asymptotic rank profile. A valid coupled inequality
would need a proved contraction or a summable scale weight, e.g.
`E_(t+1) <= lambda_t*E_t + Fresh(t)` with an explicit product/sum bound.

The existing Chvatal invariant is not that missing recurrence: it tracks
per-bag order-`r` stranger counts with `mu*delta^r*capacity`, and its fresh
allowances are constrained to `1/59,000,000` and `1/86,000,000`. The packet
spill estimates do not satisfy those bounds. Also, the finite `R(c)` table
cannot be applied to the actual unbounded bag sizes without a uniform matching
family and discrepancy theorem. Therefore no numeric total over actual active
thresholds can honestly be reported yet. The next UB-25 deliverable should be
the explicit state, active threshold set, and one-stage recurrence; then the
formula above can be instantiated against the actual scheduler levels rather
than guessed.

### Aggregate two-scale state on the actual active bags

The rank-profile candidate should separate coarse bag means from within-bag
packet variance. For one Boolean threshold `theta`, let `c_b` be the number of
64-wire packets in active bag `b`, `x_{b,p}` its packet counts, and
`mu_b = (1/c_b) sum_p x_{b,p}`. Track

```text
M_t(theta) = vector of bag-mean errors mu_b - target_b(theta),
V_t(theta) = sum_b sum_p (x_{b,p} - mu_b)^2.
```

`M` is a candidate rank-scale error: for a bag with native rank interval `I_b`, use target density `pi_b(theta) = 64*|I_b intersect [0,H_theta)|/|I_b|`, where `H_theta` is the global zero-prefix length. This interpretation still requires that the live packet slots represent that interval density. `V` carries local packet irregularity.
For `K_t` simultaneously tracked Boolean thresholds, define
`W_t = sum_theta V_t(theta)`. In one merge-and-deal cycle per active bag, if
all active packet counts have a common certified spectral factor `rho`, then
Minkowski and the per-bag rounded-cycle estimate give the aggregate fine-scale
recurrence

```text
sqrt(W_mix) <= rho*sqrt(W_t) + (s/2)*sqrt(C_t*K_t),
C_t = sum_b c_b.
```

The source allocation has `sum_b |regs(b)| = N` at every ordinary stage, so
for 64-wire packets `C_t=N/64`. The exact-rational screen checked this
partition identity at all 1,650 ordinary stages for `7<=d<=40`. With `s=26`,

```text
sqrt(W_mix) <= rho*sqrt(W_t) + (13/8)*sqrt(N*K_t).
```

By Cauchy, the aggregate positive spill is at most
`(rho/2)*sqrt(C_t*K_t*W_t) + (s/4)*C_t*K_t`. The fresh additive part is
`(s/4)*C_t*K_t = 10.15625% * N*K_t` before any port transfer. This recovers
the coarse floor but now sums over all active bags without an erroneous extra
factor for the number of bags. The heuristic/exact finite `R(c)` table cannot
replace this at actual scheduler widths: active bags have unbounded packet
counts as `d` grows.

The port step needs two explicit terms. If whole source packets could be
assigned to destination bags with a known incidence matrix `A_t`, bag means
would satisfy `mu_(t+1) = A_t mu_mix + xi_t`, where `xi_t` records the
within-bag deviations of the selected source fragments and the repair of
partial packets. Repacking also changes within-bag variance by a port defect
`Pi_t`. The candidate full recurrence is therefore

```text
M_(t+1) = A_t M_mix + target_drift_t + xi_t,
sqrt(W_(t+1)) <= rho*sqrt(W_t) + (13/8)*sqrt(N*K_t) + Pi_t.
```

This is a usable invariant interface, but it is not closed: the checked
`parentPart`/`childPart` flow gives wire counts, not the packet incidence
matrix, sorted-fragment labels, `xi_t`, or a bound for `Pi_t`. The finite
alignment calculation verifies only that most cuts are packet aligned. If one
simply sums the coarse per-stage spill over the 98 interior stages at `d=40`,
the allowance is `9.953125*N` per threshold, already larger than the whole
wire mass; boundedness must come from contraction of `M` and control of port
rebinning, not from adding stage errors.

`aggregate-energy-budget.py` and its JSON check the exact active-mass identity
and reproduce these conditional constants. They do not establish the
incidence matrix or the two-scale recurrence. The next concrete scheduler
lemma is to construct that matrix (including the boundary fragments) for one
ordinary transition and bound `xi_t` and `Pi_t`; only then is there a numeric
rank-profile slack to test.

### One actual port transition: `d=20, t=20, level=7`

For this concrete ordinary transition, `WireFlow.blockOf` selects contiguous
intervals in each source register's wire-rank coordinate, and all relevant
endpoints are multiples of 64. The level-7 receiver at time 21 has
`1,152,921,504,590,069,760` 64-wire packets. Its exact incoming packet map is:

* one parent interval starting at source rank `34,351,349,760`, with
  `18,014,397,435,740,160` wires = `281,474,959,933,440` packets;
* two end intervals from each of 64 children, each of length
  `576,320,014,815,068,160` wires = `9,005,000,231,485,440` packets.
  For each child, these are its first and last intervals of that length in
  source wire-rank order.

The exact count is `281,474,959,933,440 + 128 * 9,005,000,231,485,440 =
1,152,921,504,590,069,760`, so the receiver's packet slots have an exact
0/1 incidence map from source packet slots; no partial-packet repair is needed
in this instance. But packet alignment does not make the mean-error term
`xi_t` vanish: it is the deviation of the selected parent block and child
fringes from their respective source-bag means. Nor does the map contract that
error: it aggregates 129 source runs whose threshold profiles can differ.
This one instance therefore closes the combinatorial map at one bulk port,
but not the needed `xi_t`/`Pi_t` bounds, a uniform frontier lemma, or the
rank-profile recurrence. The next gate is to prove uniform alignment from the
`NodeShape` cases and bound selected-fragment discrepancy for the actual
129-run incidence pattern.

### Uniform 64-wire alignment from `NodeShape`

The shape formulas give a short symbolic residue proof for every ordinary
scheduled node. In each case, `a` (bag size) and `n` (down-block length) are
multiples of 64, while `u/2` (half-fringe length) is 0 or 32 modulo 64:

| Shape | `a`, `n` divisibility | `u/2 mod 64` |
| --- | --- | --- |
| `off` | both zero | 0 |
| `topDesc g` | `a=64^(g+1)`, `n=64^g`; scheduled `g≥2` | 0 |
| `topRise f` | all terms contain `64^(1+f)` | 0 |
| `mid g` | `a=64^(7+g)-64^(1+g)`, `n=16777215*64^(2+g)` | 32 if `g=0`, otherwise 0 |
| `botDesc g h` | `g≥h+2`, so both powers in `a,n` have exponent at least 2 | 32 if `h=0`, otherwise 0 |
| `botRise g h` | `h≤g`, so both powers in `a` have exponent at least 1; `n=0` | 32 if `h=0<g`, otherwise 0 |

The only extra schedule argument is for `topDesc`: if `i=0`, `exp_top`
gives `d≥t+5`, hence `g≥2` from `d+2i=t+3+g`; if `i>0`, parity and
`Inner` give `alpha+2≤i`, so `exp_nontop` gives `g≥6`. Every scheduled
source bag is therefore an integral sequence of 64-wire packets. A down
interval starts at `u/2 + j*n`, so it is packet-aligned or shifted by 32 and
has exactly two 32-wire boundary fragments. The up prefix and suffix have the
same alternatives because `a` is packet-aligned. Thus every individual port
interval has at most two half-packet boundary fragments, uniformly in `d`.
Adding these independent worst cases gives at most 130 fragments per
receiver (two from the parent plus two from each child fringe). The finite
screen's sharper maximum of 128 uses a schedule-level incompatibility between
the parent and child misalignment cases; that incompatibility still needs a
uniform proof before retaining the proposed 64-pair repair bound.

The first two special stages are aligned directly from their definitions:
the initial root down-flow is `64^(d-1)`, and the nonzero `t=1` flows contain
`64^(d-5)`, `64^(d-2)`, or `64^(d-6)` factors (`d≥7`). The finite exact
schedule check remains corroboration: 46,926 receiver instances for
`7≤d≤40` had aligned bag/down sizes and half-fringe residues only 0 or 32;
the observed maximum was 128 fragments per receiver. This symbolic result is
a hand derivation from `NodeShape`, not yet a Lean theorem. It does not prove
sortedness of packet runs or bound selected-fragment discrepancy `xi_t` and
rebinning variance `Pi_t`.

### Why parent and child misalignment cannot coincide

For a positive scheduled sender, every 32-mod-64 half-fringe case has the
same exponent signature `d + 2*i = t + 9`, where `i` is the sender level.
In `mid`, this is exactly `g=0`; in `botDesc`, it is `h=0`; in `botRise`, it
is `h=0<g`. The other shapes have aligned half-fringes. Thus if the parent
sender at level `L-1` is misaligned, `d+2*(L-1)=t+9`; if the child senders
at level `L+1` are misaligned, `d+2*(L+1)=t+9`. These equations differ by
4 on the left and cannot both hold. The special `t=0,1` sends are aligned
directly. Therefore the parent contributes at most two half-packet fragments
or the 64 children contribute 128, but never both: the uniform receiver
maximum is 128, repairable as 64 pairs.

An independent exact search through `d=80` also found no simultaneous
misalignment (442,526 receiver instances); this is supporting finite evidence.

The arithmetic core and its schedule adapter are formalized in the scratch
module `PacketAlignment.lean`. Its refined copy of the `shape_rat` case split
retains the `botRise` exponent witness, and `node_shape_refined` specializes
that classification to the actual integer flows. The checked theorem
`scheduled_receiver_no_simultaneous_misalignment` proves that the actual
parent and child flow fringes cannot both be live and 32-mod-64 shifted at any
ordinary stage. `refined_packet_residues` proves the per-shape packet
divisibility and half-fringe residues. `blockOf_rank_image` proves that the
concrete `Finset` wire block maps under `rankIn` onto exactly its half-open
interval of rank labels; `downSet_rank_image` and `upSet_rank_images` expose
this for the actual `WireFlow` ports. `downSet_boundary_fragments` proves that
each positive packet-multiple child cut has zero partial rank-packets when
aligned and exactly two when shifted by 32. `upSet_boundary_fragments` proves
the two parent-fringe intervals together contribute zero or two. Finally,
`receiver_fragment_budget` and its scheduled specialization combine the
two-piece parent charge with the 64 two-piece child charges to obtain 128,
using the proved incompatibility.

This closes the rank-coordinate fragment-count interface for `blockOf` and
the port interval formulas. A value interface is now in the scratch module:
`RankSortedOn` expresses that values increase with wire index on a source
bag; its subset theorem shows each `downSet` and `upSet` remains a sorted
run, and `rankSortedOn_parentPart` / `rankSortedOn_childPort` apply this to
the actual parent and each child contribution. This is conditional on the
source bag already being sorted; the full scheduler has not yet established
that invariant for the packet merge-and-deal labels.

The local repair lemma is now checked: `bitonicMerge64_sorts_two_runs` proves
that the 64-wire bitonic merge sorts any input whose lower 32 wires are
nondecreasing and whose upper 32 are nonincreasing, precisely the layout
obtained by reversing the second of two ascending 32-wire fragments. Its
depth is at most 6 by `bitonicMerge64_depth_le`. The 128-fragment case can
therefore be repaired by 64 such pairwise merges, and the parent-only case
by one, if a fixed placement pairs the fragments into these layouts. The
global parallel placement, label composition, and proof that it is compatible
with the full scheduler are still open. The scheduler source-order invariant,
selected-fragment discrepancy, and rebinning-variance recurrence also remain
open. No improved sorting-depth coefficient follows from this local result
alone.

### Heuristic screen for arbitrary two-chain support words (2026-10-14)

To test whether a much cheaper support-aware replacement is plausible, the
script `two_chain_greedy.py` fixes a physical support word over two chains,
enumerates all `(a+1)(b+1)` legal Boolean inputs (one threshold per sorted
chain), and greedily chooses disjoint comparator layers maximizing aggregate
inversion reduction. This is only a heuristic network search; it proves
neither minimality nor a uniform theorem.

The search sorts every legal state in the reported cases, but it does not
beat the generic bitonic-sort fallback. Representative greedy depths are 8
for `AB` repeated 8 times at width 16, 14 for `AAAABBBB` repeated twice, and
16 for `AB` repeated 16 times at width 32. A fully contiguous `A^m B^m`
support is much easier (depth 4 at width 16 and 5 at width 32), consistent
with the existing merge layout. Sparse unbalanced words can be worse still,
but those are not the equal-cardinality packet pairs needed here. These data
show that arbitrary support interleaving is a real obstacle to transferring
the 13-layer contiguous merge-and-deal; they do not establish a lower bound.

For the actual equal 64-wire pair, the checked 28-layer full-sort-plus-even/
odd-deal construction remains the only proved support-independent adapter
here. The heuristic screen gives no reason to expect a simple uniform
support-aware network to close the depth gap. A worthwhile next gate is a
formal characterization of the actual packet support words from scheduled
rank intervals: if they reduce to a small family (for example, bounded-run
or periodic words), synthesize and prove a network for that family. If the
family contains arbitrary alternating patterns, this search direction has
not found a plausible route to the required per-edge depth.

### The scheduled repair pairs are not arbitrary interleavings

The preceding screen was too broad for the actual endpoint-repair pairs. In
`PacketAlignment.lean`, `rankInterval_endpoint_pair_ordered` now proves that
the two 32-wire pieces taken from the ends of one rank interval are strictly
ordered by physical wire index. `upFringe_endpoint_pair_ordered` proves the
same for the two endpoint pieces of one sender's shifted up-fringe. The proof
uses only that `rankIn` is strictly increasing on the sender support and that
the two rank intervals are separated. Thus, on the 64-wire union, the input
support word is exactly `A^32 B^32` in increasing wire order, even if the
selected wires are sparse in the ambient `Fin (64^d)`.

This is precisely the order-preserving embedding needed to scatter a merge
network onto the fixed supports. The 28-layer sorter remains useful for
arbitrary 128-wire packet pairs, but it is unnecessary for these 64-wire
repair pairs. A Batcher odd-even merge of two ascending runs has the right
input orientation and recursively uses depth `log2(64)=6`; unlike the existing
bitonic merge theorem, it does not require reversing the second run. Formal
construction/correctness of that odd-even merge and its parity-deal adapter
are the next proof gate. If those pass, the earlier six-layer repair estimate
has a sound local fixed-label basis, though the full scheduler's packet
profile and discrepancy/variance proof still remain open.

### Odd-even merge network formalization (2026-10-14)

The width-64 candidate is now constructed in scratch Lean as
`oddEvenMergeNet 6` in `OddEvenMerge64.lean`. The recursive definition embeds
the two smaller merges on even and odd physical positions, then appends the
parallel correction comparators `(1,2), (3,4), ..., (61,62)`. A kernel-checked
induction proves `oddEvenMergeNet_depth_le`; hence the 64-wire network has
depth at most 6. Given a sorted output, `oddEvenMergeNet64_parity_profile`
proves the adjacent even/odd rank interleaving needed for the dealt packets.

The independent screen `odd_even_merge64_screen.py` checks all 33² Boolean
threshold pairs from two ascending 32-wire inputs. It confirms sorting for
all cases, with 161 comparators arranged in six disjoint layers. The full
sorting theorem for two arbitrary ascending runs is still open in Lean, so
this finite screen is not yet a formal merge-and-deal theorem. Direct
exhaustive kernel reduction was too costly; next is a structural induction
over the even/odd submerges, or a compact verified Boolean simulation that
can feed the restricted zero-one argument.

### Odd-even merge network formalization (2026-10-14)

The width-64 candidate is now constructed in scratch Lean as
`oddEvenMergeNet 6` in `OddEvenMerge64.lean`. The recursive definition embeds
the two smaller merges on even and odd physical positions, then appends the
parallel correction comparators `(1,2), (3,4), ..., (61,62)`. A kernel-checked
induction proves `oddEvenMergeNet_depth_le`; hence the 64-wire network has
depth at most 6. Given a sorted output, `oddEvenMergeNet64_parity_profile`
proves the adjacent even/odd rank interleaving needed for the dealt packets.

The independent screen `odd_even_merge64_screen.py` checks all 33² Boolean
threshold pairs from two ascending 32-wire inputs. It confirms sorting for
all cases, with 161 comparators arranged in six disjoint layers. The full
sorting theorem for two arbitrary ascending runs is still open in Lean, so
this finite screen is not yet a formal merge-and-deal theorem. Direct
exhaustive kernel reduction was too costly; next is a structural induction
over the even/odd submerges, or a compact verified Boolean simulation that
can feed the restricted zero-one argument.

The structural induction has now been reduced to a sharper interface. The
recursive even and odd submerges each receive two sorted runs, so the induction
hypothesis sorts their outputs. Their inputs are coordinatewise ordered (even
wire values are at most the following odd wire values within each original
ascending run); comparator-network execution preserves this pointwise order.
The latter fact is kernel checked as `exec_mono_input` in `OddEvenMerge64.lean`.
The parity-subnetwork execution identities are now kernel checked as
`oddEvenFront_exec_even` and `oddEvenFront_exec_odd`; the recursive network's
front/correction decomposition is `oddEvenMergeNet_exec_succ_succ`. The
remaining Lean work is to show sorted parity outputs plus that pointwise
relation make the final odd/even correction layer globally sorted. No full
merge correctness theorem has been proved yet; the six-layer depth and threshold
simulation remain the strongest checked evidence.

### Correction-layer invariant (2026-10-14)

The final correction layer needs more than sorted even/odd outputs and
`E_i <= O_i`. Between neighboring correction comparators its output has
`max(O_(i-1), E_i)` followed by `min(O_i, E_(i+1))`; ordering these requires
the shifted inequality `O_(i-1) <= E_(i+1)`. The abstract Lean lemmas
`correction_pair_ordered` and `correction_pairs_interleave` now verify that
these same-pair and between-pair conditions suffice. The critical remaining
inductive obligation is to derive the shifted inequality for the recursively
merged parity outputs from the two-run input hypothesis. Until that is proved
and connected to the actual correction network execution, merge correctness
remains open.

The shifted inequality has a promising Boolean counting proof. If the sorted
Boolean parity outputs are `E` and `O`, failure of `O_(i-1) <= E_(i+1)` forces
`O_(i-1) = true` and `E_(i+1) = false`. Then `O` has at least `m-i+1` true
entries and `E` at most `m-i-2`, so `trueCount(O) >= trueCount(E)+3`. But before
the recursive merge, the even and odd subsequences of two ascending runs have
true counts differing by at most two: each run contributes a parity imbalance
of at most one. Comparator execution preserves Boolean-value counts, so that
gap survives the recursive submerge. Thus `trueCount(O) <= trueCount(E)+2`,
ruling out failure. This reduces the shifted invariant to three Lean components:
count preservation for networks, the at-most-two parity count bound for two
monotone Boolean runs, and the sorted-Boolean suffix/prefix counting argument.
This derivation has not yet been formalized; it is a proof plan, not a checked
theorem.

Update: `boolTrueCount_exec` in `OddEvenMerge64.lean` now kernel-checks the
network count-preservation component for every Boolean comparator network. The
at-most-two parity count bound and the sorted-Boolean suffix/prefix argument
remain to be formalized; the shifted invariant is not yet proved.

Update: the at-most-two parity-count estimate is now kernel checked as
`two_monotone_runs_parity_count_gap` in `OddEvenMerge64.lean`. It is stated for
the sum of the two runs' even/odd subsequence counts, matching the physical
parity split when the run length is even. The count preservation lemma
`boolTrueCount_exec` is also kernel checked. The remaining step for the shifted
invariant is to relate these input counts to the recursively sorted parity
outputs, then formalize the sorted-Boolean suffix/prefix contradiction.

Update: `oddEvenFront_preserves_parity_count_gap` now kernel-checks that any
at-most-two true-count gap between the input even/odd parity subsequences is
preserved on the recursive submerge outputs. It uses the checked parity
execution identities and `boolTrueCount_exec`. The remaining bridge is to
instantiate the two-run count lemma on the actual two halves of a `twoRuns`
input and identify those summed counts with the full even/odd projections.

### Global depth accounting for the width-64 merge (2026-10-14)

The 6-layer `oddEvenMergeNet 6` is a candidate for the *local 32+32 fragment
repair*, not a drop-in replacement for one 13-layer merge-and-deal round on
4096-wire packets. A 13-layer round acts on the entire two 4096-wire packets;
the width-64 network only sees one pair of 32-wire fragments. Replacing the
whole round would require a blocked recursive merge/deal construction and a
proof that its output packet labels compose through all 26 matching rounds.
No such construction is present, so that substitution cannot currently be
credited with a depth saving.

For the existing conditional gate, 26 full-packet rounds cost `26*13 = 338`
layers and the assumed receiver reassembly costs 57, giving 395 layers, or
197.5 at two bits of scale per cycle. The width-64 merge can make the
six-layer fragment-pair step in that reassembly estimate plausible only when
the actual receiver fragments are paired as ordered `A^32 B^32` supports,
processed disjointly, and repacked into the next required runs. Thus it
validates a local ingredient of the 57-layer allowance; it does not lower 395
by itself. If the six-layer operation turns out to be an additional stage
outside that allowance, the total is 401 and the coefficient is 200.5, already
over the target. Using the robust 21-layer arbitrary-support sorter in place
of that six-layer step gives 410 / 2 = 205, as previously recorded.

The immediate global gate is therefore not more optimization of the local
network: prove its two-run sorting theorem and parity/deal profile, instantiate
the deterministic fragment pairing for every ordinary receiver, then show
the resulting supports meet the inputs of the next scheduled round. Only if
those fit within the stated 57 layers does the candidate retain the
sub-200 conditional coefficient; the unresolved matching-family, tail, and
rank-recurrence obligations remain after that.

Update (2026-10-14): the finite-index count split is now kernel checked as
`boolTrueCount_append` in `OddEvenMerge64.lean`, using the subtype-of-sum
equivalence and `finSumFinEquiv`. This closes the cardinality reindexing gap
for decomposing a concatenated Boolean vector into its two runs. The merge
sorting theorem is still open: the recursive step must identify the full
even/odd projections with appendings of the source-run projections, then use
the preserved count gap to discharge the shifted correction inequality.

The scheduled support side is partly ready: `rankInterval_endpoint_pair_ordered`
and `upFringe_endpoint_pair_ordered` establish the required physical order of
each pair of 32-wire fragments, and `scheduledUpFringePairSupport_disjoint`
allows distinct child repairs to run in parallel. These facts supply the
ordered support and disjointness premises, but the width-64 merge theorem has
not yet been proved and there is no receiver theorem assembling all pairs and
proving the resulting labels feed the next scheduled round.

Update (2026-10-14): `evenProjection_append` and `oddProjection_append` now
prove the projection identities for arbitrary equal-length runs, and
`boolTrueCount_evenProjection_add` / `boolTrueCount_oddProjection_add` give
the corresponding exact count decompositions. `evenEmbed_eq_evenIndexFull`
and `oddEmbed_eq_oddIndexFull` identify these index maps with the recursive
power-of-two parity embeddings, with explicit `Fin.cast`s. Thus the index and
cardinality reindexing pieces are checked. The follow-up theorem
`concatenated_two_run_parity_count_gap` now transports the monotone-run
imbalance to the full even/odd projections of the concatenated input: even
has no more true entries than odd, while odd exceeds even by at most two.
This is stronger in one direction than the symmetric ±2 invariant required
by `oddEvenFront_preserves_parity_count_gap`, and supplies its missing
threshold-count premise after the recursive parity embeddings are identified.
The finite-count step is now kernel checked as
`monotone_bool_shift_of_count_gap`: for equal-length monotone Boolean
sequences `E,O`, pointwise `E≤O` and `count(O)≤count(E)+2` imply
`O(i-1)≤E(i+1)` at every valid index. Its proof injects the true support of
`E`, together with the three positions `i-1,i,i+1`, into the true support of
`O`; a crossing would therefore force a surplus of at least three. The value-level lift `monotone_value_shift_of_threshold_counts` converts
thresholdwise count bounds into the corresponding value inequality, and
`oddEvenFront_shift` states that result directly for the recursive front's
even/odd outputs. Its hypotheses are now an explicit interface. They have not
yet been derived from the two sorted input runs, nor has the resulting local
inequality been composed with the correction layer into a full sortedness
theorem. The pointwise-order hypothesis is now discharged at the reusable
submerge level: `two_monotone_runs_even_le_odd` compares the parity inputs
inside each of the two sorted source runs, and
`common_submerge_even_le_odd` transports that inequality through a common
comparator network using `exec_mono_input`. The remaining recursive proof
now has its input-side induction lemma:
`two_monotone_runs_parity_segments_sorted` proves that each parity projection
of two sorted source runs is itself two sorted runs. Thus the recursive
sorting induction can be applied to each parity submerge. The actual
power-of-two induction theorem is not yet established; it must still transport
the threshold count gap to the recursive embedding indices and prove that the
correction layer produces a globally monotone output. The full 64-wire merge
theorem remains open.

Update (2026-10-15): `recursive_parity_outputs_sorted` now kernel-checks the
generic recursive induction step: if the same submerge network maps every
concatenation of two sorted runs to a sorted output, then applying it to each
full even/odd projection of two sorted source runs yields sorted recursive
outputs. The proof combines the checked parity-segment lemma with that
induction hypothesis. This isolates the recursive sorting part, but is not yet
instantiated to `oddEvenMergeNet`; the remaining work is to align the actual
recursive embeddings and count-gap invariant, then prove the correction layer
makes the interleaving globally sorted.

Further update (2026-10-15): `oddEvenFront_recursive_outputs_sorted` packages
the actual network's scatter embeddings and execution identities with its
recursive sorting hypothesis. It proves both parity outputs of the front are
sorted when each actual embedded parity input splits into two sorted runs.
Those four run-monotonicity premises have not yet been derived from the
original two sorted runs; nor are the shifted count hypotheses yet composed
with the correction layer. Thus this closes the network-output identification
step, but not the full induction step.

Further update (2026-10-15): `oddEven_parity_inputs_sorted` proves the four
actual parity-input run monotonicity facts by explicit power-of-two casts and
wire-index equalities: each parity sequence restricted to either source half
is the corresponding every-other-wire subsequence of that sorted half.
`oddEvenFront_recursive_outputs_sorted_of_two_runs` composes this with the
actual-network recursive step. Thus, assuming the level-`k+1` merge induction
hypothesis, the two parity outputs before correction are now proved monotone
from the original two sorted runs. The remaining merge proof is the threshold
count gap and same-rank comparison for those outputs, followed by applying the
correction layer and proving the complete output monotone.

Further update (2026-10-15): `oddEvenFront_same_rank_order` now proves the
actual front's same-rank inequality from the two sorted source runs. It shows
even and odd inputs are ordered within the relevant source half, then
transports that pointwise order through the shared recursive comparator
network. `oddEvenFront_shift_of_two_runs` packages this with the recursive
sortedness induction and the existing threshold-count argument: if the odd
front outputs have at most two more entries above each threshold than the even
outputs, the required two-position shifted inequality follows. The actual
threshold count-gap premise is still to be derived, and the correction layer
has not yet been composed into a global sortedness theorem.

Further update (2026-10-15): the same-rank front inequality is now
kernel-checked as `oddEvenFront_same_rank_order`, derived from the two sorted
source halves and monotonicity of the shared recursive submerge. The
conditional aggregator `oddEvenFront_shift_of_two_runs` combines that order,
recursive output monotonicity, and the shifted threshold lemma. Deriving the
required threshold-count bound for the actual front outputs remains open; the
present result does not yet complete the correction-layer proof.

Further update (2026-10-15): `oddEvenFront_threshold_count_gap` now derives the
actual recursive front's threshold-count bound from the original two sorted
runs. It thresholdizes the input, applies the proved even/odd parity-count gap,
and uses threshold commutation plus parity-count preservation through the
recursive submerge. `oddEvenFront_shift_from_two_runs` packages this with the
recursive sortedness and same-rank hypotheses to obtain the needed shifted
inequality directly from the original runs. These results close the front's
count-gap and shift obligations under the recursive merge induction
hypothesis. The correction-layer composition and resulting full merge
sortedness theorem remain open.

Further update (2026-10-15): `correction_output_monotone` packages the local
correction facts into global monotonicity of the alternating corrected-value
sequence. Its adjacent steps are exactly the pair-order and pair-interleaving
bounds. This closes the value-level sorting argument for the idealized
correction formulas. The remaining formal bridge is to prove that execution of
the concrete `oddEvenCrossLayer` has those per-wire corrected values; after
that, the two-run hypotheses and recursive induction can be composed into the
actual merge theorem.

Further update (2026-10-15): the concrete correction layer is now factored
through named comparators, and `foldl_parallel_at_comparator` proves that a
wire touched by a disjoint layer receives exactly the value of its unique
comparator on the original input. The checked `oddEvenCrossLayer_exec_odd`
and `oddEvenCrossLayer_exec_even` identify the actual odd-wire minimum and
noninitial even-wire maximum with the parity inputs. This closes the main
per-wire execution bridge. The untouched endpoint wires and the adjacent-wire
case split still need to be composed with the front's same-rank and shifted
inequalities before the full 64-wire merge theorem is complete.

Correction to that update: `oddEvenCrossLayer_exec_first` and
`oddEvenCrossLayer_exec_last` now also prove the two untouched endpoint
identities. The remaining step is the finite adjacent-wire case split that
combines these endpoint facts and the min/max formulas with the front profile;
the full merge theorem is still not proved.

Endpoint composition route (2026-10-15): extend the front's finite even and
odd profiles to Nat by assigning every rank beyond the final one the last
odd value. The extension makes the otherwise unpaired final odd wire equal to
the idealized correctedRight value at that rank. The actual correction
formulas then match the alternating correctedLeft/correctedRight sequence
on every physical wire. The existing correction_output_monotone theorem can
therefore discharge all adjacent comparisons at once, provided the extension
is shown monotone and its corrected-pair inequalities are split into the
interior shifted case, the final-rank endpoint case, and the constant tail.
This is a proof plan only; the Lean composition and recursive sorting theorem
remain open.

Lean progress (2026-10-15): correction_tail_extension_monotone now
formalizes the extension argument. Given monotone finite parity profiles, the
same-rank order, and the interior two-place shift, it proves the idealized
corrected sequence monotone across the terminal pair and constant tail. The
focused lake env lean ..\\experiments\\packets\\OddEvenMerge64.lean check
passes. The remaining bridge is to identify each concrete correction-layer
wire with this extended sequence, then compose the result with
oddEvenFront_shift_from_two_runs in the recursive sorting induction; the
64-wire sorting theorem is still open.

Correction-layer bridge follow-up (2026-10-15): `correction_tail_extension_monotone`
is kernel checked and supplies monotonicity for the idealized output extended
through the final odd wire. I tried to state a pointwise equality between that
sequence and `(oddEvenCrossLayer k).exec`; the even/interior-odd/final-odd
case split is mathematically direct, but my dependent `Fin` index rewrites did
not close. The attempted theorem was removed, leaving the focused file clean.
The next formal step is to define the physical-rank-to-parity-rank maps as
separate checked equalities, then prove the profile equality from those
identities without unfolding dependent `Fin` proofs in the main theorem. Until
that equality and the recursive sorting induction are checked, neither the
six-layer odd-even merge claim nor the resulting 197.5 coefficient is a
formal UB-25 contribution. Even after the merge proof, the global matching,
exceptional-tail, and coupled rank/discrepancy recurrence remain major open
obligations.
Index-map progress (2026-10-15): `evenEmbed_of_evenIndex` and
`oddEmbed_of_oddIndex` now kernel-check the physical-wire to parity-rank
identities directly, with the divisibility and quotient arithmetic isolated
from dependent `Fin` proof terms. The focused Lean file passes after adding
these lemmas. They are the intended adapters for the concrete profile bridge;
that bridge itself, the sorting induction, and the global UB-25 recurrence
remain open.

Completion audit (2026-10-15): the later source state closes the correction
profile bridge and the recursive sorting induction described as open above.
`oddEvenCrossLayer_exec_first`, `oddEvenCrossLayer_exec_last`,
`oddEvenCrossLayer_exec_odd`, and `oddEvenCrossLayer_exec_even` identify the
actual correction output at every wire, including both unpaired endpoints.
`oddEvenFront_threshold_count_gap` derives the required count gap from the two
sorted input runs, parity splitting, and count preservation through the
recursive submerges. `oddEvenFront_shift_from_two_runs` converts it to the
shifted inequality used by the correction layer. The strong induction
`oddEvenMergeNet_sorts_two_runs` then proves that the actual comparator network
sorts any two ascending runs at every power-of-two width. Its depth theorem
`oddEvenMergeNet_depth_le` proves depth at most the exponent, hence the 64-wire
instance sorts two 32-wire runs in at most six layers. The correction and
induction obligations are kernel-checked; `PacketMergeAxioms.lean` guards the
headline result with only standard Lean axioms. This closes the local merge
gate, not UB-25's receiver reassembly, matching schedule, coupled recurrence,
or global limsup proof. The current coefficient near 200 remains conditional.

Incidence progress (2026-10-15): `PacketHalfProfile.lean` now defines the
actual bag-to-bag piece selector on `KBag 64 d`. For each fixed source bag,
distinct receivers select disjoint indices: child receivers take their unique
middle index `receiver.x % 64 + 1`, while the source's parent takes fringe
indices `0` and `65`; the root is explicitly excluded from the parent-fringe
case. The generic finite aggregation theorem and its exact sorted-sender L1
identity have been generalized from `Fin` indices to arbitrary finite types.
`wireFlowLayer_profile_error_sum_le` instantiates them on the complete finite
64-ary bag tree, proving that the sum of absolute routed piece-profile errors
over all receivers is at most one coarse count error per source bag. The focused
scratch chain through `PacketMergeAxioms` passes. This is the incidence and
no-amplification gate, but it does not yet identify the all-bag sum with the
active `execPlacement` registers at root/leaf boundaries, identify summed ideal
means with the next target profile, or prove contraction of the coupled rank
and discrepancy state. The coefficient near 200 remains conditional.

Neighbor-map adapter (2026-10-15): `wireFlowLayerSelection_receiverSource`
proves that for an active receiver with `1 ≤ b.l` and `b.l < d`, its global
bag selector on each `wireFlowReceiverSource b ... source` equals the existing
local `receiverOutgoingSelection`. This is kernel-checked and axiom-guarded.
It gives termwise agreement on the 65 actual neighbors. The finite sum still
ranges over all KBag sources, so a support/reindexing argument and explicit
boundary treatment are required before applying the register identity to the
aggregate theorem.

Reindexing progress (2026-10-15): `wireFlowReceiverNeighborBags_mem` names a
receiver's parent and 64 children. `wireFlowLayerSelection_eq_empty_of_not_neighbor`
proves that all other source bags contribute no selected pieces, and
`wireFlowLayerSelection_receiverSum_eq` reindexes the full finite KBag source
sum exactly to the local `Fin 65` source sum. Together with
`wireFlowLayerSelection_receiverSource` and
`wireFlowReceiver_selected_count_eq_register`, the actual interior receiver
count identity is now modularly connected to the global incidence sum. The
attempt to package this as one summed actual-register theorem was too expensive
to elaborate in its initial form and was discarded; the checked component
lemmas remain. The next formal step is a compact wrapper using named profile
error/mean functions, followed by identifying the selected means with the
coupled recurrence's target.

Actual-register incidence bridge (2026-10-15): `wireFlowLayerSenderPieceCount`,
`wireFlowLayerSenderPieceMean`, and `wireFlowLayerSenderPieceError` package the
actual Boolean counts and ideal means on each sender's routed rank piece.
`wireFlowLayer_receiver_signed_error_eq_register` proves that the all-bag
signed error at any interior receiver is exactly its actual `execPlacement`
register threshold count minus the selected ideal means. The aggregate theorem
`wireFlowLayer_register_error_sum_le_source_count_error` then sums the absolute
discrepancy over every active receiver of the layer and bounds it by the sum of
coarse sender count errors, charging each source once. The prior oversized
wrapper was replaced by this modular theorem; both results are axiom-guarded.
This closes actual-register incidence accounting at one layer. The remaining
recurrence gap is to make these per-threshold targets coherent as a receiver
profile and establish the coupled rank and discrepancy contraction.

Selected-target capacity (2026-10-15): `profileIntervalMean_bounds` proves
that every ideal sender-piece mean lies between zero and that rank interval's
capacity. `wireFlowReceiverSelectedIdealMean_bounds` uses the exact
parent/child selected-piece count identity to prove that the sum of selected
means lies between zero and the actual receiver register size. Thus the
selected mean is a valid real-valued threshold target for the next receiver;
this does not assume a common mean across heterogeneous source bags. The
remaining issue is to show that these targets, simultaneously over all value
thresholds, define the required monotone rank profile and that the induced
profile/variance update contracts.

Threshold-profile coherence interface (2026-10-15):
`profileIntervalMean_between` and `profileIntervalMean_mono_mean` show that
linear interpolation between adjacent integer source profiles is monotone in
the underlying real target `q + frac`; the floor-change boundary is exact.
`wireFlowReceiverSelectedIdealMean_mono` sums this property over the actual
selected parent/child intervals. Therefore, if every source's target profile
is monotone over value thresholds, the receiver's selected target profile is
also monotone. This supplies the state-coherence part of the induction
interface. It does not prove that the actual scheduler preserves source
sortedness or that the resulting profile has a contracting rank energy.

Finite-threshold aggregate (2026-10-15):
`wireFlowLayer_register_error_sum_le_source_count_error_multi` lifts the
one-threshold incidence estimate to any finite family of Boolean thresholds.
The total actual receiver discrepancy, summed over every interior bag at
every active bag level and over the chosen thresholds, is bounded by the
source coarse-count discrepancy summed over those same thresholds, with no
extra factor for the number of active levels or port fragments. This is the
exact fresh-error budget to insert into a rank-profile recurrence. Its
right-hand side still needs a contraction/telescoping argument across stages;
adding it naively over all stages is not enough.

Target re-encoding (2026-10-15): `realTarget_has_integer_fraction` proves
that every real target in `[0,m]` for positive capacity `m` has a representation
`q + frac` with `q < m` and `0 ≤ frac ≤ 1`. At the endpoint `m`, it chooses
`(m-1)+1`, satisfying the strict integer-count hypothesis used by the sender
profile theorem. `profileInterval_partition_L1_exact_allow_endpoint` now
extends the exact error identity to both `q=m, frac=0` and `m=q=0`. This
endpoint case is threaded through the sender partition, selected-port bound,
bag-tree incidence estimate, actual-register aggregate, and finite-threshold
aggregate. Those theorems now require only `q≤|S|` and `q=|S| → frac=0`, so the
zero-capacity state `q=frac=0` handles empty startup/frontier bags. The
aggregate interface is therefore applicable from the first stage, subject to
the required sorted-source and state-profile hypotheses. The scheduler
invariant and quantitative contraction are still open.

Sender-repair invariant audit (Codex / GPT-6, 2026-10-15): a tempting shortcut
is to claim that the six-layer repair preserves `PacketSortedOn` on the same
64-rank grid. It does not follow from the local theorem. `senderBoundaryCell i`
is `prefix_i ∪ suffix_i`, while `senderRepair_support_cycle` says repair pair
`i` sorts `suffix_i ∪ prefix_(i+1)`. Thus the two halves of one rank-grid packet
are produced by different repair pairs. What is proved is that each crossed
repair support is rank-sorted and the union of all touched supports is exactly
the union of boundary cells; neither statement orders the two halves of an
individual output packet against each other. The next sortedness proof must
track placement through destination reassembly/merge and show how its outputs
reunite the crossed halves. This is the concrete scheduler invariant gap;
sender repair alone does not close it.

Interior-selector conservation (Codex / GPT-6, 2026-10-15):
`wireFlowLayerSelection_active_cover` proves every one of a source bag's 66
pieces reaches an active receiver when `2 ≤ source.l` and
`source.l + 2 ≤ d`. Pieces 1–64 go to the child indexed by the piece, and
fringes 0 and 65 go to the parent. Pairwise disjointness upgrades this to the
exact union identity and `wireFlowLayerSelection_active_sum_eq_range` for any
additive piece quantity. Its actual-target specialization,
`wireFlowLayerSenderPieceMean_active_sum_eq_target`, says the ideal target mass
is conserved exactly as `q(source) + frac(source)`, including empty and full
endpoints. Root and upper-frontier levels
are intentionally excluded; their unselected pieces need separate boundary
accounting before this can be used as a whole-stage conservation law. The new
lemmas are axiom-guarded and the focused check through `PacketMergeAxioms`
passes.

Boundary selector partition (Codex / GPT-6, 2026-10-15): for every tree with
`d ≥ 3`, `wireFlowLayerSelection_active_union_complete` now covers every
source level. Levels 0–1 route exactly pieces 1–64; levels 2 through d−2 route
all 66 pieces; levels d−1 and d route exactly fringes 0 and 65. The low/high
union lemmas and `wireFlowLayerSelection_active_sum_eq_union` turn these into
exact additive identities, so the frontier losses are now localized to
explicit rank-piece subsets rather than an unspecified inequality. The two
unrouted subsets (low fringes and upper middle pieces) still need a separate
startup/termination cost bound to close the global recurrence. Focused Lean
and axiom-guard checks pass.

Frontier error budget (Codex / GPT-6, 2026-10-15): each actual sender piece's
Boolean threshold count and ideal mean lie in its rank capacity. Theorems
`wireFlowLayer_low_frontier_error_sum_le_up` and
`wireFlowLayer_high_frontier_error_sum_le_down` aggregate the absolute errors
of all omitted pieces over the actual source bags: low fringes cost at most
`∑ up`, and high middle pieces at most `∑ 64 * down`. The root fringe error is
exactly zero by `hup_root`; the leaf middle error is exactly zero by
`hdown_leaf`. Thus only level 1's up-flow and level d−1's aggregate down-flow
remain as nonzero boundary terms. Their time-summed cost and how it feeds the
rank/variance contraction remain open. Focused check and axiom guards pass.

Temporal frontier charge (Codex / GPT-6, 2026-10-15): the actual §7 schedule
has `flowDown7 (d−1) t = 0` at every ordinary stage `t < tf7 d`, since
`omega7 d t < d−1`; the leaf down-flow is already zero. Hence
`wireFlowLayer_high_frontier_error_sum_eq_zero` proves the whole high-frontier
omitted-middle error is exactly zero, not merely summably small. For level 1,
`flowUp7_level_one_le_capacity_scale` bounds each ordinary-stage up-flow by
`capacity d 1 t / 4096²`, and `flowUp7_level_one_time_sum_le` telescopes the
ratio-`1/64` capacity schedule to at most `(64/63) * capacity d 1 1 / 4096²`
per source bag over `t=1..tf7 d−1`. Since `capacity d 1 1 = 64^(d−1)`, this is
`(64/63) * 64^(d−5)` per level-1 bag. `wireFlowLayer_level_one_bags_card_le_64`
and `flowUp7_level_one_aggregate_time_sum_le` formalize the multiplier 64 and
the total bound `(64/63) * 64^(d−4)`, a fraction `(64/63)/64^4` of `64^d`
(about `6.05e−8`). This closes the scheduler-time budget for the only possible
frontier residual, but not its incorporation into the rank/variance recurrence,
nor the sortedness invariant needed by the layer theorem. Focused chain and
axiom guards through `PacketMergeAxioms` pass.
