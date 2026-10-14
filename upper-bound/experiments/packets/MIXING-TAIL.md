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
`up/2 = 4095·32·64^g`, which is divisible by 4096 for `g ≥ 1`; at `g=0` it
has residue 4064 modulo 4096. Similarly, `botDesc` has
`down = 64^g-64^(h+2)`, divisible by 4096, and
`up/2 = 4095·32·64^h`, aligned for `h ≥ 1` with residue 4064 at `h=0`.
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
