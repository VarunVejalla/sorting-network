# Rounded matching-cycle bulk and tail interface

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
