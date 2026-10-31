# Sparse-bottom D2 candidate below 300 (paper screen)

2026-10-21. Exploratory structural candidate; no separator theorem or sorting
proof is claimed. This reuses the D2 cut-layout idea and modifies its flow
only at sparse-bottom nodes where the nominal upward quota exceeds the
current bag allocation.

## Proposed routing rule and cost

Use `(x,y,z)=(3,2,2)`, so `k=8`, `tf(d)=5d/2+O(1)`, and
`log2 N=3d+O(1)`. In the D2 cut-layout table, let `a` be a node's current
allocation and `pi` its scheduled upward quota. Replace `pi` by
`pi' = min(pi,a)`. When `pi>=a`, send the whole bag upward and give zero wires
to all children. In the cut representation, if the current low/high deficits
are `gL,gH` and the children's total current mass is `S`, then `a=S-gL-gH`;
with `pi'=a`, the cut fronts satisfy

```text
gL + pi'/2 = S - gH - pi'/2.
```

Thus they meet exactly instead of crossing, and every child interval is
cleared without a negative block. For `pi<a`, retain the ordinary D2 cut
layout. The `FlowDAG` experiment exposes this as `sparse_bottom=True`.

At fixed row height `m=2^14`, three bitonic column sorts cost
`3*(14*15/2)=315` layers per active stage. The stage/log rate is `5/6`, so
the conditional coefficient is `315*(5/6)=262.5`. Sending a whole bag up
uses no separator sort. The coefficient leaves 37.5 for any additional
per-stage work, but not for an unpriced asymptotic overhead.

## Finite exact-flow evidence

`d2_sparse_bottom_screen.py` checks nonnegative exact child blocks, conservation,
even upward quotas, and divisibility of every nonempty sender arity by `2^14`.
It reports:

| depth | stages | shared flow states | min fringe rows | send-all state classes | max terminal native bits |
|---:|---:|---:|---:|---:|---:|
| 50 | 118 | 126,287 | 17.52 | 390 | 20 |
| 100 | 241 | 1,019,814 | 9.81 | 1,420 | 23 |
| 150 | 368 | 3,563,554 | 6.73 | 2,846 | 20 |

These are exact finite screens, not an all-depth proof. The decreasing
minimum fringe is especially important: a fixed row height does not preserve
the `f>=13` hypothesis of the reviewed tiny-fringe certificate in these
samples. A local provider must cover shrinking/partial-row fringes or derive
a stronger invariant that avoids this threshold.

### Lower row-height tradeoff

The same screen at `row_bits=13` lowers the three-sort stage cost from 315 to
273 layers and the conditional coefficient from 262.5 to 227.5. This leaves
72.5 layers per log unit for provider work. The exact finite flow checks give:

| depth | shared states | minimum fringe | maximum terminal native bits |
|---:|---:|---:|---:|
| 50 | 126,287 | `28672/3273` (~8.76) | 19 |
| 100 | 1,019,814 | `57344/11691` (~4.91) | 22 |
| 200 | 8,399,594 | `57344/22191` (~2.58) | 22 |

At depth 200 the minimizing sender is an ordinary `mid` node at stage 485,
level 193, not a sparse-bottom send-all. The observed decline makes a fixed
positive-fringe provider a poor fit for this flow. It does not prove the
fringe tends to zero, nor rule out a provider uniform in the actual fringe or
a different treatment of these boundary senders.

### Boundary sender trace and fixed-tail check

The small-fringe sender lies on a reproducible boundary family. At stage
`t=tf(d)-26`, level `i=omega(t)-2`, the role is `mid`; choose the reachable
state with `low=0` and `high=G` (the opposite-side state is its mirror). For
row height `m=8192`, the quota ratio is `pi/c=7/1024`, so its equivalent
fringe is exactly

```text
f = m*pi/(2*a) = 28/(a/c).
```

Exact compressed-flow values are:

| depth `d` | `tf(d)` | `t=tf(d)-26` | `a/c` | fringe rows `f` |
|---:|---:|---:|---:|---:|
| 50 | 118 | 92 | `5706/2048` | `57344/5706` (~10.05) |
| 100 | 241 | 215 | `10851/2048` | `57344/10851` (~5.28) |
| 150 | 368 | 342 | `16206/2048` | `57344/16206` (~3.54) |
| 200 | 491 | 465 | `21351/2048` | `57344/21351` (~2.69) |

On the tested depth classes, increasing `d` by100 increases `a/c` by exactly
`10500/2048`. The four data points fit the phase formulas
`a/c=(105d+456)/2048` for `d=50,150` and
`a/c=(105d+351)/2048` for `d=100,200`. This is a concrete all-depth lemma
candidate, not a proved recurrence. If either phase formula holds for all
depths in its residue class, this family's fringe tends to zero like a
constant over `d`; a fixed minimum-fringe provider cannot cover this unchanged
flow.

A terminal exact-sort experiment screens the last `L` stages for replacement
by exact sorting of each sender bag. For `L=20`, the finite screen reports
minimum pre-cleanup fringes `57344/11061` (~5.18) at depth100 and
`57344/21351` (~2.69) at depth200. At depth200, `L=24` also leaves the
stage-465 witness before cleanup; `L>=26` includes this particular gap-26
state in the cleanup window. These runs therefore reject only the tested
short tails. They do not rule out every fixed `L`: that would require a
family of shrinking-fringe witnesses at gaps greater than each proposed
`L`. The screen's largest bag size and padded bitonic depth are finite
diagnostics only; no routing or global-correctness claim follows from sorting
individual bags.

There is a direct schedule bound on cleanup bag size. For `t>=2`, put
`s=t-3d/2+5`. The exact rounding definitions give

```text
alpha(d,t) >= s,
omega(d,t) >= 2t/5 + 3/5.
```

When the `max(0,...)` branch in `alpha` is inactive, its parity rounding also
gives `alpha(d,t)<s+2=t-3d/2+7`. When that branch is active,
`alpha(d,t)<=1` and `omega(d,t)>=2`. Hence, for sufficiently large `d`,
every `2<=t<=floor(5d/2)-11` has `alpha(d,t)<omega(d,t)`: in the positive
branch, `s+2-omega(d,t) <= -1/5`. Therefore
`tf(d) >= floor(5d/2)-10`. For any fixed tail length `L` and sufficiently
large `d`, monotonicity of `alpha` then gives
`alpha(d,tf(d)-L) >= d-L-6`. Every sender in the last `L` stages has active
level `i>=alpha(d,tf-L)`, hence its allocation is at most its native size
`m*8^(d-i) <= m*8^(L+6)`. Thus exact sorting of each sender bag in a fixed
number of final stages has a depth bound independent of `d` (for `m=8192`,
the crude bound at `L=40` is 151 padded bits per bag). The finitely many small
depths can be absorbed separately. This closes the *size* part of the fixed-
tail cleanup argument; it does not show that the resulting static intervals
can be combined into a globally sorted output. That rank/address terminal
criterion remains open.

The provider fringe is still the harder cleanup tradeoff. At depth100, the
physical `row_bits=13` screen with `L=40` gives minimum pre-cleanup fringe
`57344/10221` (~5.62), at stage199, level79. At depth150, the same fixed tail
gives `57344/15471` (~3.71), at stage325, level129. Thus even after the exact
near-terminal shrinking-fringe witness has been removed, a fixed 40-stage tail
does not preserve a positive fringe floor in these deeper screens. This is
finite evidence, but it strongly favors a variable-small-fringe provider or a
different local network over simply extending the fixed cleanup tail.

The two witnesses have a particularly simple normalized form. Their
`(a/c, fringe)` pairs are
`(10221/2048, 57344/10221)` at `d=100` and
`(15471/2048, 57344/15471)` at `d=150`. The allocation numerators differ by
`105*(150-100)` and both satisfy `2048*a/c=105*d-279`. For a mid sender in
this geometry, `fringe=28/(a/c)`, so extending this phase formula would give
fringe `57344/(105*d-279) -> 0`, while the witness stays outside the fixed
40-stage tail (42 or 43 stages before `tf`). This is not yet a recurrence
proof. The next sharp obstruction test is to derive the same affine phase
family for arbitrary fixed tail length `L`; if it holds, no fixed-tail
constant-fringe provider can close the sparse-bottom route.

Reproduce this screen with `python d2_sparse_bottom_screen.py --depth 100
--row-bits 13 --cleanup-tail 40`.

Reproduce the boundary trace with
`python d2_sparse_bottom_screen.py --depth D --row-bits 13 --cleanup-tail 26`.
The screen prints exact `omega-2` mid states in its final 30 stages. A proof
of the phase recurrence, or a local contract for aggregate partial-row fringe
mass, is the next mathematical gate.

Reproduce with `python d2_sparse_bottom_screen.py --depth 50 --row-bits 13`,
`python d2_sparse_bottom_screen.py --depth 100 --row-bits 13`, or
`python d2_sparse_bottom_screen.py --depth 200 --row-bits 13`.

### Minimum-fringe witness family

For `row_bits=14`, direct minimization identifies the smallest fringe at each
of depths 25, 50, 75, 100, 125, and 150 in an ordinary `mid` sender; it is
not a sparse-bottom send-all. The exact witness data are:

| depth | stage | level | `a/c` | minimum fringe rows |
|---:|---:|---:|---:|---:|
| 25 | 49 | 19 | 3921/2048 | 114688/3921 |
| 50 | 112 | 44 | 3273/1024 | 57344/3273 |
| 75 | 172 | 68 | 4533/1024 | 57344/4533 |
| 100 | 235 | 93 | 11691/2048 | 114688/11691 |
| 125 | 299 | 119 | 14421/2048 | 114688/14421 |
| 150 | 362 | 144 | 8523/1024 | 57344/8523 |

Here `c` is the scheduled capacity; a mid sender has `pi/c=7/1024`, so its
fringe is exactly `2^13*(7/1024)/(a/c)`. The observed `a/c` grows with depth
and the minimum fringe falls roughly like `1/depth`. This does not prove that
the infimum tends to zero, but it changes the provider target: a proof of a
uniform fixed-`f` fringe lower bound is unlikely to close the gate. The more
promising next lemma is a provider contract uniform in the *actual* (possibly
small) fringe, or a different way to handle these ordinary mid senders.

At depths 50 and 100 the minimizing state is specifically address zero, at
level `omega(t)-2`, with `low=G` and `high=0`; its `G/c` values are `151/1024`
and `645/2048`, respectively. Thus at these depths the shrinking fringe is
already present on the extreme left boundary, rather than arising only from
a complicated interior profile.

The exact `row_bits=12` edge trace has the one-sided structure at every active
`omega-2` mid state in the finite screens at depths 25, 50, and 100 (46, 110,
and 233 states per edge, respectively): the leftmost node has `low=G`,
`high=0`, while its mirror has `low=0`, `high=G`. The minimum fringe rows on
each edge are `28672/3921` (~7.31), `14336/3273` (~4.38), and `28672/11691`
(~2.45). This suggests a sharper proof target than a generic small-fringe
theorem: prove the extreme-edge one-sided invariant, then establish its local
sorting/error contract. The predecessor check identifies a concrete schedule
lemma: every such edge state is created by a preceding `topRise` or `mid`
parent cut whose two fronts straddle the designated end-child boundary. The
smallest observed normalized front margin is `43/256` of parent capacity
(at stage 4); this is ample finite slack, but still not an all-depth reserve
proof. Reproduce with
`python d2_edge_trace_screen.py --depths 25 50 100 --row-bits 12`.

These edge bags have a stronger global-color property. With total wire count
`N=scale*8^d` and target zero-prefix size `q=floor(N/3)`, an address-zero
native interval at level `i>=2` is `[0,N/8^i)` and hence lies wholly below
`q`; its mirror lies wholly above `q`. Every bag interval is contained in its
native interval. Thus the boundary sender's ideal contents are all zero on
the left and all one on the right. A specialized local contract need only
control movement of the opposite-color outsiders in the relevant direction;
it need not union both color orientations for these bags. This does not make
the bad keys disappear from arbitrary inputs: it changes the provider target
from a two-sided local guarantee to a one-sided output-port guarantee.

The same script now audits *every* level on both boundary paths at every
snapshot, not only the `omega-2` states. Across depths 25, 50, and 100 it
checks 434, 1,808, and 7,222 live edge states; all are one-sided. For every
ordinary edge sender it also checks the sufficient tail-reserve inequality
that keeps the opposite cut out of the endpoint child. The minimum reserve
divided by sender capacity is depth-independent in these screens: `211/256`
for `topRise`, `1673/2048` for `mid`, and `21/2048` for `botDesc`. This gives a
compact candidate induction: preserve one-sided edge debt, and prove those
three schedule-derived tail reserves. The bottom-descending reserve is the
tight case; finite agreement at three depths is not yet a proof.

The audit reduces the tail-reserve step to simple per-child lower bounds. In
boundary order, the seven non-edge child deficits divided by sender capacity
are bounded below by `(7/64)^6, 1/8` for `topRise`; `(7/64)^6, 21/128` for
`mid`; and `(1/512)^7` for `botDesc`. The scheduled quotas satisfy
`pi/c <= 1/128` for `topRise` and `pi/c <= 7/1024` for the other two roles
(sparse-bottom capping only decreases `pi`). These imply nonnegative opposite-
end slack; the weakest lower bound is `21/2048 c` in `botDesc`. The finite
screen checks these exact inequalities at both ends through depth 100. The
next proof-sized task is therefore the all-depth child-deficit floor lemma
for the edge paths; once established, one-sidedness follows by a direct stage
induction, with `botRise` preserving child roots and `topDesc` clearing them.

There is a separate schedule-only reduction for those floors. For every
active `topRise`, `mid`, or `botDesc` parent in depths 3--200, the parent is
inactive one stage earlier and the child capacity ratio is exactly
`c(i+1,t-1)=16c(i,t)`. A `topRise`/`mid` parent has child role `mid` or
`botDesc` at `t-1`, except for the startup child; their raw quota is therefore
`7c/64`, while the startup native floor is at least `c/8`. A `botDesc` parent
has child role inactive or `botRise` at `t-1`, and the latter's children are
inactive at that stage. The exact audit reports 14,504 `topRise`, 931,637
`mid`, and 33,712 `botDesc` active schedule points with no exceptions. This
is not yet a proof of the child deficits: it still needs a historical
inactivity/native-state lemma for `botDesc` and a treatment of its capped
quota branch. Reproduce with `python d2_sparse_edge_schedule_audit.py
--max-depth 200`.

An exploratory reuse of `fringe_cert_v2.py` tests whether its F2 probability
envelope reaches smaller fixed fringes at the candidate ragged width `n=8307`
and support cap 18 (`delta=18/(f*n)`). The parameter point
`(g1,g2,c,b,J)=(2,4,2/5,1,1)` at `f=9` passes the exact interval screen, though
the unbracketed Lean-friendly closed envelope misses the R1 budget. A rational
R1b tangent bracket `[1527/10000,1528/10000]` closes the bound at `f=9`, with
`ln(2P1)<=-7.50129` and `ln(2P2)<=-7.67752`; the generic `hf16` interface
guard still needs replacement by the actual-dimension condition. The sampled
`f=6,7,8` points fail the exact budget or a required precondition. This is only
a finite parameter search, not an impossibility result for smaller fringes;
the observed `2.45`-row sender remains uncovered. The next probability task
is to find a uniform variable-`f` certificate down through that boundary
range, or prove a different special contract for those extreme-left states.
In the current Lean interface `f`, `g1`, and `g2` are natural numbers, and the
postcondition bounds an integer escape count by `< f`; treating the geometric
`2.45` as a real-valued `f` is therefore a new partial-row contract, not a
direct instantiation of the existing theorem.

There is also a parameter obstruction at integer `f=3` for the current F2
R1a certificate, independent of the support cap. The natural constraints
force `g1=1`, `g2=2`, and `Delta=1`; `c*Delta >= J/(g1+1)` with `c<=1/2` and
`J>=1` then forces `J=1` and `c=1/2`. Writing `D=delta*f`, the screened
exponents reduce exactly to
`ts = 1 + ln(2) - (1/2)ln(D)` and
`beta = 3 + ln(D) - ln(2)`, hence
`lambda_a = -(ts+c*beta) = -(5/2 + (1/2)ln(2)) < 0` for every `D>0`.
So this particular positive-slope R1a argument cannot certify `f=3` by
shrinking `delta`; this is a limitation of the certificate, not a lower bound
on the true separator error. A viable edge treatment needs `f>=4` in this
integer template or a genuinely different one-sided/partial-row contract.
The support-one case itself is now kernel checked in
`F2SupportOne.lean`: total mass is conserved by row scrambling and
`onesAboveBottom` is bounded by that total, so at most one opposite-color key
implies `<2` escapes after any two scrambles, for every fringe width. This
removes the local probability estimate entirely if a global invariant can
certify support at most one for an edge sender. That global premise is not
currently proved and is the real condition needed to use this lemma.
Reproduce these selected parameter points with
`python ragged_provider_probability_screen.py` from this directory.

### Parity/divisibility subgate

For `m=2^14`, the exact screen now checks the following observed lattice

```text
active allocation a and deficit G: multiples of m;
stored low/high offsets: multiples of m/2;
uncapped ordinary-role quota pi: multiples of 2m; send-all roles use pi=a;
ordinary cut fronts low+pi/2 and S-high-pi/2: multiples of m.
```

It passes at depths 10, 20, 60, and 100. These congruences make all half-quota
cuts integral and align ordinary cut fronts to the native `m` grid. A stronger
first guess (all active quotas divisible by `4m`) is false: at depth10, stage10,
an active quota is `14m`. The role split above is the corrected target.

The uncapped ordinary-quota portion has a short schedule proof. Put
`q_i=3d+2i-2t`; then `m*cap=2^(q_i+11)`, and the alpha cutoff gives
`q_alpha>=10`. At a `mid` or `botDesc` node, `i>=alpha+2`, so its quota has
2-adic valuation `q_i+1>=15` (the coefficient is `7/1024`). A `topRise`
occurs only in the initial clipped phase, when `t` is odd, `alpha(t)=1`, and
`alpha(t+1)=0`. The latter inequality gives `3d-2t>=12`, so its quota has
valuation `q_i+4=3d-2t+6>=18`. Thus every uncapped ordinary nonzero quota is
divisible by `2m`.
An earlier proposed claim that every capped ordinary quota is a multiple of
`2m` is false. At depth14, stage26, level12 has role `botDesc`, allocation
`a=m`, and planned quota `14m`; saturation sends the odd-`m` allocation whole.
There is no later active stage at that level. The useful target is a coupled
phase statement: at every later ordinary sender, both cut fronts remain on
the `m` grid despite half-`m` offsets created by earlier send-alls. The finite
screen checks this directly through depth150. It also finds that every odd-
`m` send-all is `botDesc` or `botRise` and has no later ordinary cut at that
same level; this is useful schedule evidence, but does not by itself control
odd offsets created in child states. For example,
at depth10, stage4, level4 is `botRise` and reactivates at stages6, 8, 10, 12,
and14, but its actual allocation there is an even multiple of `m`.

Scale1 is too small to normalize this flow: `botRise` can have an odd quota,
so its half-quota would not be integral. The useful base is scale2. Under the
parity claim below, all scale-2 quotas are even and the scale-`m` flow is
exactly `8192` times the scale-2 flow. This reduces the allocation and deficit
lattice to parity at scale2; the remaining issue is whether a half-`m` offset
can persist into an ordinary cut. The screen checks the resulting regular
ordinary cut fronts on the `m` grid. A send-all has coincident fronts even
when its allocation is only an odd multiple of `m`.

A second role-wise screen narrows the saturation proof: through depth150,
every positive capped ordinary class is `botDesc`; no positive `topRise` or
`mid` class has `a<=pi`. At depths14, 30, and50 the `botDesc` counts are 18,
120, and390, with respectively 2,4, and10 odd-`m` cases. All other positive
`botDesc` caps are even multiples of `m`. Proving these inequalities and the
global front-alignment phase property from the recurrence remains open. At depth150 there
are 22 odd-`m` `botDesc` classes at `(t,i)=(365,147)` and `(366,148)`, and 10
odd-`m` `botRise` classes at `(367,149)`. The former exact location formula
`(5d/2-9,d-2)` misses the stage-365 class, so the exact location guess is
ruled out. The finite screen instead checks that every ordinary cut front is
on the scale-`m` grid through depth150; this remains an all-depth proof
obligation, not a theorem.

The scale-2 ratio scan gives a simple role-wise proof target. Through
depth100, every positive `topRise` has `a/c>=1` and every positive `mid` has
`a/c>=63/64`; their planned quotas are `pi/c=1/128` and `7/1024`,
respectively. These bounds would rule out their saturation with substantial slack. For
`botDesc`, `pi/c=7/1024`, but the observed minimum is `a/c=1/2048`, and the
minimum `a/pi` among capped states is `1/14`; this is the role where the
boundary-phase argument is essential. The exact ratio report is available
from `d2_sparse_bottom_screen.py --row-bits 1`.

The `63/64` midpoint lower bound has a repeated witness: at every tested
active time with `i=omega(t)-2`, the bag at address index1 has
`G=low=high=0` and `a/c>=63/64`. Through depth30 its eight child deficits,
divided by their capacity `4c`, have the fixed profile
`(21/512, 7/256, 7/256, 7/256, 7/256, 7/256, 7/256, 21/512)` and give equality.
That exact profile does not persist unchanged: at depth100, stage94, level38,
the index1 bag has `a/c=65/64` and its first child profile is `25/512`.
Across 233 tested stages through depth100, however, the index1 parent deficit
and offsets stay zero and the lower bound `a/c>=63/64` holds. The screen also
checks this bound for every positive mid sender through depth100. This gives a
boundary-state route to a proof: although the exact profile changes, all 16
observed types dominate the coordinatewise floor
`(21/512,7/256,7/256,7/256,7/256,7/256,7/256,21/512)`. Since the parent
deficit is zero and each child capacity is `4c`, this floor implies
`a/c>=63/64`. The screen checks this componentwise floor through depth100.
The depth30 fixed-profile pattern is not an all-depth invariant, and the
componentwise floor remains an unproved invariant.

The profile dynamics offer a smaller induction target. If `B_t` denotes the
index1 profile at level `omega(t)-2`, the exact screen checks 231 adjacent
transitions through depth100: when `omega(t+1)-omega(t)=1`, every coordinate
of `B` is nondecreasing; when the difference is `-1`, the next profile resets
to the floor vector above. Together with the initial floor state, these two
transition rules would prove the boundary profile floor. The rule holds at
depths50 and100 but still needs a derivation from the interval-cut recurrence.

### Exact two-step allocation audit

Added `d2_two_step_audit.py` to enumerate aligned state triples
`(v_{t-2},v_{t-1},v_t)` in the shared flow DAG and check the two-step identity
for every mid sender. If `C_t` is its capacity, and `C_0,C_1` are respectively
the same-address capacity at `t-2` and each child capacity at `t-1`, the
schedule gives `C_0=C_1=16 C_t`; exact flow conservation gives

```text
a_t / C_t
  = (G_{t-2} - G_t) / C_t
    + 16 * (pi_{t-2}/C_0 + sum_child pi_{t-1}/C_1).
```

At depths30, 50, and100 with scale2, the audit checks 4,733, 25,815, and
225,619 distinct aligned mid-sender triples respectively. Repeating at the
physical row scale `2^14` gives the same counts and bounds through depth100.
Every identity
holds, every checked pair satisfies `G_t <= G_{t-2}`, and every mid sender
has `a_t/C_t >= 63/64` (with equality attained). This provides an exact
finite verification of the decomposition and its target inequality.
Extending the scale-2 check to depth150 gives 802,659 aligned mid-sender
triples; all allocation identities, child-deficit updates, monotonicity checks,
and `63/64` bounds still pass. The physical-scale depth100 result remains the
largest checked at `m=2^14`.

The audit now also checks the child-level update in each aligned triple. If
`n1` is the intermediate parent state and `n2` the current one, then for every
child `j` it verifies exactly

```text
G_j(n2) = G_j(n1) + pi_j(n1),
```

where `pi_j(n1)` is the child's send in the intervening stage. This passes for
all 4,733 mid-sender triples at depth30 and all 225,619 triples at depth100,
at row scale `2^14`. Thus each half-profile sum splits into the prior cut-debt
contribution plus four fresh child quotas. This is the concrete recurrence
interface for the half-profile target: prove the two clipped-tail sums and
their corresponding fresh-quota sums together, while tracking the parent
low/high offsets across the same transition. The finite identity does not
establish those inequalities for arbitrary depth.

It also rules out the simpler proposed proof using only scheduled quotas.
At depth100, 106 of the checked `t-2` parents are positive capped `botDesc`
states, and 1,794 of 179,312 child `botDesc` visits are positive capped
(empty bags are tracked separately). The normalized sum of child quotas can
be zero, so monotonicity of `G` plus quota lower bounds alone gives no useful
uniform estimate. The two-step identity isolates that obligation but does not
close it; the more direct half-profile inequalities below are the current
proof target. Reproduce the physical-scale check with
`python d2_two_step_audit.py --depth 100 --row-bits 14` from this directory.

For `(3,2,2)`, the capacity relations are `C(i,t)=C(i-1,t-1)` and
`C(i+1,t-1)=16C(i,t)`. Substituting them into the exact two-step identity
gives the simpler scalar form

```text
a(i,t)/C(i,t)
  = (G(i,t-2) + pi(i,t-2) - G(i,t))/C(i,t)
    + sum_{j=0}^7 pi(child_j,t-1)/C(i,t).
```

The first term is the deficit reset caused by the intervening parent cut; the
second is the eight fresh child sends. For the hard `botDesc`-to-`botDesc`
phase, the depth30 audit sees reset range `[7/64,179/128]` and child-send-sum
range `[37/128,7/8]`, with their sum always at least `63/64`. The ranges are
not pointwise bounds that can simply be added; their correlation is exactly
the remaining scalar unsaturation sublemma. This is a possible weaker route
than the two separate half-profile bounds for establishing `a/C>=63/64`, but
it does not provide the spatial information needed for the global rank proof.

### Candidate half-profile cut lemma

The same audit finds a more direct state invariant. For a mid node at stage
`t`, let `C` be its capacity and let `p_j=G_j/(4C)` be the normalized deficit
of child `j` (each child capacity is `4C`). With the parent cut debts
`G=low+high`, the sufficient half-profile inequalities are

```text
sum(p_0, p_1, p_2, p_3) >= 63/512 + low/(4C)
sum(p_4, p_5, p_6, p_7) >= 63/512 + high/(4C).
```

They imply the target because
`a/C = 4*sum(p_0,...,p_7) - G/C >= 63/64`. The four-plus-four split matches
the two cut fronts, so these are plausible induction statements for the
actual interval recurrence. At depth30 the audit checks all 4,551 distinct
mid states and both inequalities hold, with minimum slack zero. At depth100
it checks 219,845 distinct mid states with the same result, at row scale
`2^14`. The stronger coordinatewise floor `p_j >= floor_j+G/(32C)` fails
(minimum margin `-163/16384` at depth100); the proof needs the paired
half-profile sums. At scale2 and depth150, the paired inequalities also pass
on all 787,649 distinct mid states, with zero minimum slack; the componentwise
floor still fails (minimum margin `-1009/65536`). These finite checks identify
a useful invariant interface, but do not prove it for all depths.

The tightness pattern narrows the induction target. The two-step audit now
reports which half-cut inequality is tight for each debt side. At depth50 and
scale2, all 25,815 aligned mid triples still satisfy `a/C >= 63/64`; among
24,871 distinct mid states, every single-sided-debt state except the listed
boundary cases has equality in the *opposite* half-cut inequality (high debt:
left; low debt: right). The exceptions to that tightness pattern occur only at
`level = omega(t)-2`, at stages 54, 64, 74, 84, 94, 97, 104, 107, and 114.
They retain nonnegative slack in both inequalities. At depth30 the same audit
finds 4,733 aligned triples and the first such boundary exceptions at stages
54 and 64. This points to a boundary-profile transition lemma as the next
small proof target; the exact tightness pattern is diagnostic evidence, not an
induction proof. Reproduce it with
`python d2_two_step_audit.py --depth 50 --row-bits 1`.

The same aligned-triple audit now checks the exact half-cut recurrence. For a
mid sender with parent capacity `C`, each four-child slack multiplied by four
is

```text
left:  (sum previous-cut G over children 0..3 - low)/C
       + (sum fresh child pi over children 0..3)/C - 63/128,
right: (sum previous-cut G over children 4..7 - high)/C
       + (sum fresh child pi over children 4..7)/C - 63/128.
```

This is an identity: each current child deficit equals its previous-cut
deficit plus that child's fresh quota. At depth50, scale2, all 25,815 aligned
triples satisfy the identity and have nonnegative slack. The separate minimum
carryover is only `7/128`, while the separate minimum fresh-quota sum is zero;
the two terms must be controlled jointly to reach `63/128`. This rules out a
proof using either a uniform carryover bound or a uniform quota bound alone.
It is a more precise target for the boundary-profile induction, still only a
finite audit. The script prints these six minima alongside the prior checks.

Grouping the exact decomposition by the schedule roles isolates the difficult
case further. At depth50/scale2, all states fall into three pairs
`(child role, parent role at t-2)`: `(mid,mid)` (21,241 triples),
`(botDesc,mid)` (1,497), and `(botDesc,botDesc)` (3,077). Each group has
minimum left and right `carry + fresh` exactly `63/128`. In the first two
groups, the four fresh mid-child quotas alone are at least `7/16`, and the
carry is at least `7/128`, giving the target by addition. Only the consecutive
bottom-descending case `(botDesc,botDesc)` needs a genuinely coupled state
argument: its fresh-quota minimum is zero, yet the sum remains at least
`63/128`. This is now the narrowest known form of the all-depth mid-sender
lemma; the finite classification does not prove the bottom-descending case
uniformly.

I made the aligned-triple traversal in `d2_two_step_audit.py` an explicit
visited-set DAG walk instead of relying on cached generator objects. Repeated
triples had already been traversed on first occurrence, so this was a clarity
and robustness change, not a correction to the measured results. The exact
depth30 and depth50 counts and bounds are unchanged. At depth100/scale2, the
walk checks 225,619
aligned mid triples, including 14,840 `botDesc`-to-`botDesc` cases; all pass
with minimum half-cut sum `63/128`. Those hard cases have 610 distinct
`(carry,fresh)` pairs and a 15-point Pareto frontier. The frontier size stays
15 from depth50 to depth100, but its endpoint values change, so it is not yet
a fixed finite certificate. Reproduce with
`python d2_two_step_audit.py --depth 100 --row-bits 1`.

The depth150 extension checks 802,659 mid triples and 36,543 hard
`botDesc`-to-`botDesc` cases; the minimum paired half-sum remains `63/128`.
The hard-case distinct `(carry,fresh)` point counts / Pareto frontier sizes
are 232/15, 610/15, and 1,022/16 at depths50, 100, and150. Both the frontier
and the endpoint-reserve window grow, so the finite screens still provide no
fixed all-depth certificate. Reproduce with
`python d2_two_step_audit.py --depth 150 --row-bits 1`.

There is a narrower endpoint-reserve form of the hard case. If `G_j` is a
child's deficit before its `botDesc` send, `a_j` its allocation, and
`q=7C/64` its nominal quota (where `C` is the current mid-parent capacity),
then

```text
G_j + min(q,a_j) = q + min(G_j, G_j+a_j-q).
```

Since `4q=7C/16`, it suffices to prove for the left half
`sum_{j=0}^3 min(G_j,G_j+a_j-q) >= low + 7C/128`, and symmetrically from the
right. The exact audit finds that the *first three endpoint children* already
suffice in every tested `botDesc`-to-`botDesc` transition: their minimum
reserve slack is zero through depth100. The first child alone can miss by
`119C/512`, and the first two by `47C/512`, at depth100; adding the third
closes the gap. This suggests a three-child endpoint reserve lemma as the
next all-depth target. It is not proved and the finite horizon does not show
that three children suffice at every depth.

Depth150 follow-up invalidates any inference that three endpoints suffice:
the minimum reserve slacks using one, two, three, and four endpoint children
are `-105/256`, `-69/256`, `-33/256`, and `0`, respectively. The first
nonnegative endpoint prefix grows from two children at depth50 to three at
depth100 and four at depth150. Keep the full four-child half-profile as the
target; a fixed smaller endpoint reserve is not supported.

The hard recurrence is genuinely two-directional. When a level-`i` sender is
mid at stage `t`, its level-`i-1` parent can be active at `t-1` and rewrite
the sender's stored `(G,low,high)` even though the sender itself is inactive
then. For example, at depth12 and `(i,t)=(2,4)`, the sender is `botDesc` at
`t-2`, inactive at `t-1`, and `mid` at `t`; its level-1 parent is `topRise`
at `t-1`. Thus the debt offsets entering the paired half-profile cannot be
advanced from the sender's own vertical recurrence alone. The all-depth proof
must couple the parent cut at `t-1` with the sender/child updates at `t-2` and
`t-1`. In the depth50 hard-case audit, all 3,077 such parent states are
active at `t-1`: 3 are `topRise` startup cases, and 3,074 are `mid`. This
suggests applying the parent mid invariant to control the offsets of its
bottom-descending children, with the startup cases handled separately. The
role conditions force `omega(t-2)=i`, `omega(t-1)=i+1`, and `omega(t)=i+2`:
the sender and its child both see consecutive `botDesc` steps. Its ancestor at
level `i-1` is therefore two levels below `omega(t-1)`, so it is `mid` unless
that level coincides with the active lower frontier `alpha(t-1)`.
The schedule-only edge audit now checks this implication over every depth
through200: it finds 18,964 hard schedule points, with 18,769 `mid`-ancestor
points and 195 `topRise` startup points, and no other ancestor role. This
does not prove the quota/carry inequality, but removes a potentially
depth-dependent role case from that proof. Reproduce with
`python d2_sparse_edge_schedule_audit.py --max-depth 200`.

### Conditional scale-2 parity induction

The scale-`m` flow is exactly `8192` times the scale-2 flow as long as the
scale-2 recurrence has integral half-quota cuts: quota and saturation are
homogeneous, and division by two commutes with multiplication by `8192`. At
scale2, every ordinary unsaturated quota is divisible by4 by the role-wise
valuation calculation, so its half-quota is even. A sufficient induction
interface is that every live deficit `G` stays even and every ordinary sender
has even cut fronts. Then its clipped child tails remain even. For a send-all,
`pi=a=sum(U_j)-G` is even; the two fronts coincide, so each child deficit
after the cut is its full `U_j` and stays even, although the two individual
child offsets may be odd.

The remaining phase lemma is therefore precise: odd offsets created at a
send-all must never reach a later ordinary sender as an odd front. The screen
checks every ordinary cut front directly through depth150 and finds them all
even at scale2; it also observes that odd send-alls are `botDesc`/`botRise`
and have no later ordinary cut at that same level. That schedule fact does not
control odd offsets in descendants, so the full front-alignment induction
remains open. The screen also finds that positive `topRise` and `mid` nodes
never saturate, but this stronger fact is not needed for the stated parity
interface and is unproved for all depths.

I also generalized `wire_partition_check.py` to accept the candidate
parameters and saturation mode. It checks exact equality of the routed static
wire intervals with each next-stage bag, for every bag and stage. The candidate
passes this check at `m=2^14` for depths 2 through 6 (2,396,744 bag checks at
depth 6). This removes a small-depth routing-geometry uncertainty, but does
not prove the invariant for all depths or sorting correctness.

The baseline compressed D2 table for `(3,2,2)` fails at depth9 because the
planned `pi` exceeds `a` and its cut fronts overlap. The saturation repair
passes the flow conservation/geometry checks through depth150. The key-level
perfect-separator check is only available at smaller depths; no proof that
the repaired table preserves rank addresses at every depth is claimed here.

### Sparse-support three-round gate (fixed seed)

`d2_sparse_support_core_gate.py` encodes all monotone 64-column height
profiles with total support at most18 as a MILP, applies the exact three
row-scramble rounds from `local_core_multiround_adversary.py`, and maximizes
the terminal column height. At seed0, HiGHS found a feasible profile using17
ones whose terminal maximum is3, so this fixed scramble does **not** provide
the desired uniform `<=2` edge gate. The nonzero initial heights (1-based
columns) are `1:1, 7:1, 14:3, 18:1, 21:2, 25:2, 40:1, 42:2, 52:4`.
The solve hit its 120-second limit, so this is a verified counterexample for
seed0, not an optimality certificate or a statement about other seeds. The
profile is directly re-evaluated through the core before it is reported.

Reproduce with `python d2_sparse_support_core_gate.py --seeds 0
--time-limit 120`. The bottleneck was the MILP solve, not Python simulation;
rewriting the model driver in C++ would not address the present obstacle.

## Proof gates

1. Prove by induction that the saturation rule yields a valid D2 interval
   partition, nonnegative child allocations, and exact address preservation
   through every stage; prove a constant terminal native-size bound.
2. Establish a two-sided bulk/local-fringe provider for the resulting
   `m=2^14` rectangles and partial-row cuts. The current Lean B2 theorem only
   applies at `m>=2^42`; the current tiny-fringe screen does not cover the
   observed shrinking fringe values.
3. Close the shared-witness probability budget, root profile initialization,
   all-cut rank/prefix recurrence, and terminal purity for this altered D2
   flow. Existing UB-42 LP obstructions concern weaker relaxations and do not
   settle this stronger fixed-core invariant.
4. Formalize the local networks, the saturated flow, arbitrary-`n` padding,
   and the limsup estimate. Do not start Lean before the first three gates
   have a reviewed paper proof.

This is a more credible sub-300 shape than uniform U because D2 removes the
observed ideal-routing address defect, while saturation repairs the first
finite sparse-bottom overlap. Whether both properties hold together at all
depths is open.
