# Actual first-sort profiles and shifted tails

2026-10-20. Codex (GPT-6). Paper research, not a sorting theorem.
Fresh read-only review of the first-sort/cut semantics: `first_column_review`
(GPT-6-luna). Independent mathematical review of the shifted-tail lemma and
counting: `shifted_profile_audit` (GPT-6-luna); its correction on reflected
cut coordinates is incorporated below. Neither review proves global sorting.

## Why the stronger local interface matters

`PhysicalPack2.lean` starts with an ordinary column sort, followed by two
row-conjugated column sorts. All physical comparators are ascending. Thus
every output prefix contains at least as many zero keys as the **actual
first-sort output**, not just as many as the original input. This costs no
extra layers. The rectangular source proves the ordering of the relabeled
comparators; a centered-ragged extension still needs its physical embedding.

`first_column.py` computes that first-sort word exactly on the proposed
centered-ragged layout using run lengths and column intervals. It passed
8,490 comparisons with independent literal column sorting (all binary words
of lengths1..12 at height ceiling4, plus300 larger random cases).
No arrays proportional to the ambient wire count are needed.

This restriction is materially stronger than bulk/fringe postconditions.
At d20, root bulk precision10^-7, threshold1/3, the postcondition-only ordered
oracle with epsB=.0095, epsF=1/16, delta=1/8 and the moderate tail admits:

| Initial wrong-key locations | First capacity gap |
|---|---|
| both outer ends | step10, subtree(1,0):3435 wrong vs2184 future exit slots |
| left end and just above threshold | same3435 vs2184 |
| just below threshold and right end | step12, subtree(1,3):429 vs136 |

These are failures of a weakened relational contract, NOT of the actual
fixed core. Requiring prefix dominance over the first-sort output excludes
all three sampled failures. The same full-schedule tests, plus a central
inverted band and column-aligned stripes, reach pure terminal blocks in the
sampled identity-then-Hamming adversary. All begin with109950 wrong keys.
The stripe test uses up to4096 small intervals at two different root-column
residues; it is more demanding than a contiguous inverted band.
The stripe sample also passes with delta=0 (no rare-fringe constraint), still
using the moderate tail and mandatory first sort. This removes that local
assumption only for this one sampled execution, not for the construction.

These are samples, not a uniform result. The oracle still assumes an
unpriced rare-fringe promise and an uncertified all-cut bulk scalar; it
chooses input-dependent outputs, and its root profiles satisfy only the
stated bulk budget. A passing run does not construct one fixed provider.

## A profile interface for the existing three-sort core

Work first with exact m-by-n rectangles, m>=1,n>=2, as allowed by
INFLATED-SCHEDULE. A one-column matrix is sorted exactly.
One means a zero key. After the first sort let c_j be column heights and

    T_c(b) = sum_j max(c_j-b,0),    0<=b<=m.

Fix a baseline b. The column profile c is dominated cellwise by b+d, where
d_j=max(c_j-b,0). The first b rows of this larger matrix are full. Row
permutations preserve that baseline, and every subsequent column sort keeps
it full. Removing it leaves exactly the sparse-profile process on the bottom
m-b rows. Monotonicity therefore gives

    output zero mass beyond row b+f <= sparse escape(d,f).

This holds even when c has missing marks within the baseline: filling them
only increases the comparison input. Reflection gives the corresponding
bound for holes before a row cut. This is a deterministic reduction, not
itself a probability or global sorting bound.

Apply the reviewed MODERATE-TAIL envelope to d with
i=ceil(T_c(b)/n), clipped to m-b. Use zero escape at zero mass. To choose one
row scramble working for every baseline b, mass class i, subset size p*n
and both orientations, at most2*m^2*(n-1) classes suffice. Replace that
note's entropy overhead by

    log(2*m^2*(n-1)/eta)/n.

The suffix restriction of independent uniform row permutations has the
correct distribution. Baseline restrictions need not be independent: the
union bound does not require independence. Profile/subset unions are still
covered by g(i) and binary entropy h(p). Endpoints p=0,1 are deterministic;
use non-strict escape inequalities and clip by actual mass.

Let Phi(E,f) denote this uniform escape envelope for all profiles of mass
at most ceil(E/n)*n. One round yields the whole-tail inequality

    T_next(k) <= min_{0<=b<=k} Phi(T_c(b),k-b).

Each later row permutation preserves a full-row tail and each column sort
only reduces it, so even the one-round inequality remains valid after the
second round. Alternatively apply the operator twice, selecting a common
witness for both scrambles with total failure budget eta (overhead then
log(4*m^2*(n-1)/eta)/n). Feeding an upper bound for T_next into the second
round is legitimate because its promise covers every profile below the
chosen mass cap; numerical witness selection need not be monotone.

For any output full-row cut k, these tails give concrete prefix lower bounds

    Y(k*n) >= H - T_out(k),
    Y(k*n) >= k*n - hole_mass_before_row_k.

The physical/semantic correspondence preserves these counts. For a cut
inside a row, use the preceding full-row prefix, or account for the partial
row explicitly; do not assume arbitrary-cut precision for free.
For the holes inequality at native cut k, reflect vertically and apply the
tail operator at cut m-k, not k: choose b_h+f_h=m-k in that reflected frame.
The endpoint k=m is exact. If a KL budget exceeds its maximal value, clipping
the threshold to i remains valid by the deterministic mass cap X<=in.

## Global prefix-flux invariant and terminal test

For a stage state, let `Z_t(r)` be the number of zeros on static wires
`[0,r)`, and let `q` be the conserved total number of zeros. Define the
prefix defect

    F_t(r) = min(q,r) - Z_t(r).

It is always nonnegative. If every active bag is listed in increasing static
wire order and its local output dominates its local input at every prefix,
then `Z_{t+1}(r) >= Z_t(r)` for every global cut `r`: intersect `[0,r)` with
each active bag; each intersection is exactly a local prefix, sum the local
inequalities, and add unchanged inactive wires. Therefore `F_t(r)` is
pointwise nonincreasing through the D2 stages. The exact interval-routing
identity checked by `wire_partition_check.py` supplies the required static
wire partition for this flow; the local prefix inequality follows from
ascending comparators.

This gives a more precise one-stage transfer. For the current bag partition
`B_t`, let `c_B(r)` be the number of wires of bag `B` below global cut `r`,
let `H_B` be its zero count, and let `d_B(c)=min(H_B,c)-Z_B(c)` be its local
prefix defect. Define the nonnegative alignment term

    A_t(r) = min(q,r) - sum_{B in B_t} min(H_B,c_B(r)).

Then exactly `F_t(r)=A_t(r)+sum_B d_B(c_B(r))`. If an active bag's local
provider guarantees local defect at most `T_B(H_B,c)` after the stage, local
prefix dominance gives the sharper bound

    F_{t+1}(r) <= A_t(r)
      + sum_{B active} min(d_B(c_B(r)), T_B(H_B,c_B(r)))
      + sum_{B inactive} d_B(c_B(r)).

The alignment term is what a local sorter cannot remove within this stage; it
changes when the next D2 stage changes the bag partition. This separates
local contraction from cross-bag alignment and supplies a concrete transfer
target for the tail envelope. The exact decomposition and monotonicity
consequence are checked on the finite flow by `global_prefix_flux.py`.

## Port transfer for bag-mass imbalance

There is also an exact endpoint identity that isolates how local prefix tails
create imbalance between the next stage's bags. Fix the global threshold `q`.
For each current bag `B`, list its wires in increasing static-label order,
write `P_B` for the number of these wires below `q`, and `H_B` for its actual
zero count. Let `Y_B(s)` be the output zero count in its first `s` local ranks,
and set

```text
delta_B = H_B - P_B,
d_B(s) = min(H_B,s) - Y_B(s),
g_B(s) = min(H_B,s) - min(P_B,s).
```

For a routed port occupying local rank interval `[u,v)`, its zero-mass
imbalance against the ideal threshold labels on those same static wires is
exactly

```text
eta_port = (Y_B(v)-Y_B(u)) - (min(P_B,v)-min(P_B,u))
         = g_B(v)-g_B(u) + d_B(u)-d_B(v).
```

The function `g_B` is monotone, with total variation `|delta_B|`; also
`d_B(0)=d_B(a_B)=0` and `d_B(s)>=0`. Summing absolute port imbalances over
the contiguous rank-port partition of an active bag therefore gives

```text
sum_ports |eta_port| <= |delta_B|
                    + 2 * sum_{internal port cuts s} d_B(s).
```

Inactive bags keep their wires and contribute `|delta_B|` unchanged; a
bottom-rise whole-bag port has no internal cut and satisfies the same bound.
Since each next bag is a union of routed ports, triangle inequality yields

```text
||delta_next||_1 <= ||delta_current||_1
                  + 2 * sum_{active B} sum_{internal port cuts s} d_B(s).
```

At the threshold cut, the alignment term above is exactly
`A_t(q)=||delta_current||_1/2`, since `sum_B delta_B=0`. Thus this is a
finite rank-profile interface: a uniform local tail bound on `d_B(s)` at the
actual D2 port cuts directly controls the next stage's bag-mass alignment.
The ordinary comparator property also gives `d_out(s)<=d_in(s)` pointwise.
In particular the threshold-cut defect itself has the exact decomposition

```text
F_t(q) = ||delta_current||_1/2 + sum_B d_B^in(P_B).
```

This does not yet contract the right-hand side: the bound retains the old
imbalance and sums local defects over all active bags. A closed recurrence
must exploit the exact phase geometry and the correlations between adjacent
port defects, rather than simply summing this inequality over stages.

## Distance-graded local defect gate

The round-one margin certificate can constrain the local prefix defect at a
cut when the sender's zero mass is known to lie strictly on one side of that
cut. For a sender of size `a=m*n`, let `H` be its zero count and let `Y(s)` be
the output zero count in its first `s` local ranks. Then

```text
d(s) = min(H,s)-Y(s).
```

If `H <= s`, this is the number of ones that crossed upward over rank cut
`s`; if `H >= s`, it is the number of zeros that crossed downward over that
cut. Every such key has rank displacement at least `|s-H|`. Thus a valid
far-crossing estimate at margin `r` rows gives `d(s) <= T(r)*a` whenever
`|s-H| >= r*n`. In the current 8192-row candidate, a margin of 512 rows
has the following certified outward rational caps. Each row is checked with
`sub500-screen/cert_walk_n.py tail 8192 8192 W numerator denominator`, using
one mass cell; these are interval-certified bounds, not sampled estimates.

| Margin `W` (rows) | Certified cap for `T(W)` |
|---:|---:|
| 64 | `103/10000` |
| 128 | `78/10000` |
| 256 | `47/10000` |
| 512 | `25/10000` |
| 1024 | `12/10000` |
| 2048 | `61/100000` |

This yields a cheap necessary LP constraint whenever the scalar history
interval `[Hlo,Hhi]` is wholly below or above the selected cut: use the
minimum possible distance from that interval to the cut and the strongest
certified margin not exceeding that distance. No selector variables are
needed. When the interval straddles the cut, this simple gate gives no
information; closing those near-boundary cases requires the full shifted-tail
operator or a coupled profile state. The LP gate must be added at cuts for
which the deterministic merge theorem actually supplies the corresponding
far-crossing statement; it must not be generalized to arbitrary cuts solely
from the numerical certificate. Even if this profile gate passes, it tests
only the finite abstract flow relaxation, not a single fixed provider or an
all-depth sorting proof.

The identity follows by writing `I_H(s)=min(H,s)` and
`I_P(s)=min(P_B,s)`. The local prefix defect is `d(s)=I_H(s)-Y(s)`, and the
mass-offset function is `g(s)=I_H(s)-I_P(s)`. For one port `[u,v)`, subtract
its ideal threshold mass from its actual mass:

```text
Y(v)-Y(u) - (I_P(v)-I_P(u))
  = g(v)-g(u) + d(u)-d(v).
```

As `s` increases, `g(s)` is monotone from0 to `delta_B`; its total variation
over any partition is therefore `|delta_B|`. The defect term has zero values
at the two endpoints, and the triangle inequality bounds its variation on
the port partition by twice the sum of its internal endpoint values. Routed
port subsets partition each next bag's static wire set, so summing their
signed discrepancies gives its `delta`; applying triangle inequality across
next bags proves the displayed `L1` transfer. This argument uses the exact
static-wire port correspondence from `wire_partition_check.py` and is
independent of the D2 phase formulas.

The same transfer holds at every global cut `r`, by replacing `P_B` with
`P_B(r)=c_B(r)`. In that version `delta_B(r)=H_B-P_B(r)` has total
`sum_B delta_B(r)=q-r`, and the alignment term has the exact expression

```text
A_t(r) = (||delta_t(r)||_1 - |q-r|)/2.
```

Indeed, for `r<=q`, `A_t(r)` is the total negative part of `delta_t(r)`;
for `r>=q`, it is the total positive part. The port-transfer inequality
therefore gives, simultaneously for every cut,

```text
A_{t+1}(r) <= A_t(r)
              + sum_{active B} sum_{internal port cuts s} d_B(s).
```

Here `d_B(s)` is determined by the local output and port ranks, so the tail
event at a port endpoint can bound this entire additive term for all `r` at
once. Summing the bound over cuts would introduce a factor `N`; avoiding that
loss requires retaining the cut-dependent signed discrepancies or a weighted
area potential. This all-cut version is the relevant interface for inversion
contraction, whereas the `r=q` case alone controls only central mass balance.

## Exact weighted-area decomposition

The inversion potential has a useful exact form that keeps the cut-gap
weights visible. For a current bag `B`, let its static wire labels in local
rank order be
`w_B(0)<...<w_B(a_B-1)`. Let `H_B` be its number of zero keys, `Y_B(s)` its
output prefix count, and `d_B(s)=min(H_B,s)-Y_B(s)`. Define `hat w` by sorting
each bag separately, placing its `H_B` zero keys on the first `H_B` local
wires. Then

```text
Inv(w) = Inv(hat w)
       + sum_B sum_{s=1}^{a_B-1}
           (w_B(s)-w_B(s-1)) * d_B(s).
```

Indeed, `F(r)=min(q,r)-Z(r)` decomposes as the global prefix defect of `hat w`
plus `sum_B d_B(c_B(r))`. Summing over global cuts gives `Inv(hat w)` in the
first term. For a fixed bag, `c_B(r)=s` at exactly
`w_B(s)-w_B(s-1)` integer cuts; the endpoint terms vanish because `d_B(0)`
and `d_B(a_B)` are zero. Thus the second term is a genuine weighted area of
the local rank defects, with weights equal to gaps between that bag's wires.

The same local defects control the perturbation of the next bag masses. For
an active source bag with consecutive local port intervals `[u_j,v_j)`, a
perfectly sorted reference output sends
`m_j^0=min(H_B,v_j)-min(H_B,u_j)` zeros to port `j`. The actual port mass is

```text
m_j = Y_B(v_j)-Y_B(u_j)
    = m_j^0 + d_B(u_j)-d_B(v_j).
```

Let `H_C^0` be each destination bag's mass under these reference port masses
(inactive bags pass through unchanged), and `H_C` its actual mass. Then

```text
Delta_C = H_C-H_C^0
        = sum_{ports j routed to C} (d_B(u_j)-d_B(v_j)),
sum_C Delta_C = 0.
```

If the destination bag `C` has ordered static labels `w_C(s)`, its bag-sorted
inversion term changes by the exact signed sum

```text
Inv(hat w(H)) - Inv(hat w(H^0))
  = sum_C oriented_sum_{s between H_C^0 and H_C} (w_C(s)-q).
```

The `-q` is allowed because the total mass perturbation is zero. This shows
why taking absolute values too early loses the area information: port defects
carry signs, and each unit shifts a bag boundary at a specific distance from
the global threshold. When all source bags are balanced (`H_B=c_B(q)`), the
perfectly sorted reference routes exactly the threshold labels, so
`H_C^0=c_C(q)` and `Inv(hat w(H^0))=0`.

For an explicit bound, let `R_C` be the largest value of `|w_C(s)-q|` among
the ranks crossed between `H_C^0` and `H_C`. Then

```text
|Inv(hat w(H)) - Inv(hat w(H^0))| <= sum_C |Delta_C| * R_C.
```

In the balanced case this bounds the entire next bag-sorted inversion by the
right-hand side. If `I_C` is the destination's native interval, its radius
satisfies
`R_C <= dist(q,I_C)+length(I_C)`. Getting a useful asymptotic recurrence
therefore requires either showing that nonzero signed defects only reach
near-threshold bags, or proving they decay fast enough to pay for the distance
of far bags.

These identities specify the weighted recurrence target: bound the signed
port perturbations with the local tail values, and bound the new weighted
local-defect area using the actual wire-gap weights. The remaining work is to
prove useful all-profile bounds for those terms over the full D2 schedule.
The formulas alone do not imply contraction; the input may have nonzero bag
imbalance, and the row-tail theorem has not yet been transferred to these
state-dependent weighted cuts.

At the terminal time, `F(r)=0` at every native interval boundary wholly below
or above the unique threshold-straddling interval is an exact sorting test:
below the threshold it says every wire in the prefix is zero; above it says
all `q` zeros have already appeared. The straddling native interval can be
sorted by the final exact cleanup. This identifies a compact global state
and terminal criterion, but monotonicity alone does not force defects to
vanish. The missing proof is a rank-tail contraction bound for `F` over the
actual active bags, strong enough to make every required terminal defect
zero within the priced schedule.

## Finite-cut ordered LP gate

`profile_cut_closure.py` propagates port and terminal cuts backward through
the static-wire geometry. With root row boundaries included, depth6 at scale
4096 needs 4,098 global cuts at the first two times, then 394 or fewer; the
largest local profile has 4,098 cuts. Without root row cuts, depth8 at scale
4096 closes with 1,866 global cuts at the first five times and at most 2,625
local output cuts in a stage. The closure is finite and small enough to put
into a sparse LP; it does not encode every local prefix.

`coupled_rank_lp.py --ordered-prefix` now couples those global profiles to
each local output profile, ties bag masses to exact static-wire intervals, and
requires local output prefix dominance at every selected closed cut. The
root-tail mode also constrains the initial profile by the computed rank-tail
envelope and by the exact worst-case first-column count at full row
boundaries. For a cut `p=k*n+s`, the first-column prefix count for column
heights `c_j` is `sum_j min(c_j,k+1_{j<s})`. Its exact minimum subject to
`sum c_j=q` is found by selecting the columns with `c_j` at least their prefix
height (these cost that height and can then hold up to `m` zeros); for each
selected-column count, choose the smallest prefix heights and minimize the
remaining unit-cost zeros. The implementation is independently checked
against every column-count profile on rectangles up to 4-by-4.

For depth6, scale4096, threshold `floor(N/3)`, root-tail mode produces a
fractional selected-cut LP optimum with 456,448 wrong keys in terminal
noncrossing blocks (141,903 in one block). Its first root-row prefix defect is
2,730, exactly the worst-case first-column lower bound at that cut. This is
not an actual-network counterexample: local prefix dominance is imposed only
at the finite selected cuts, and the rank-tail bounds are still coarse. It
shows that this finite interface does not close the 292.5 gate. The next
specific gap is stronger all-cut reachability/tiny-rank control for the same
fixed 3-sort, together with a root profile guarantee sharp enough to remove
the surviving remote defects.

## Actual-candidate adversarial gate (2026-10-23)

`coupled_rank_lp.py` and `profile_cut_closure.py` now accept the flow parameters
and row count, so this test targets the current `(3,3,2)` / 8192-row candidate
rather than the earlier `(2,3,2)` / 4096-row model. With exact sorted-root
initialization, the selected-cut LP optimizes to zero terminal wrong mass at
depths4--7. This is only a model sanity check: the root is already sorted, so
ascending comparators leave it sorted. The assumption is an unpriced exact
sort of the entire root and gives no evidence about arbitrary inputs or a
contracting recurrence. At depth4 the LP and its integral version both solve
to zero; depths5--6 use11,219 variables,8,221 equalities, and23,941
inequalities; depth7 uses141,992 variables,110,371 equalities, and301,004
inequalities. The depth7 run takes about12 minutes and peaks near3.3 GB.

The sparse model enumerates only positive-mass bag addresses, traversing the
interned flow tree and pruning empty subtrees. On depths4--6, this support
matches a dense address-by-address scan exactly. The transition equations are
also indexed only at global cuts strictly inside a source bag's wire span;
endpoint equations are already implied by exact bag-mass conservation. These
reductions preserve the depth4--6 outputs while avoiding the full `8^d`
address expansion.

With the 13-bit root-tail envelope instead of the exact root, the depth4 LP
optimizes to752,457 terminal wrong keys (161,217 in one block); depth5 gives
6,013,277 (1,290,930 in one block). These are respectively2.2425% and2.2401%
of the input, so this relaxation shows no contraction over those horizons.
At depth4 the objective is unchanged when row-boundary sampling is tightened
from every256th row to every64th and every16th row (all three LPs solve
optimally). Thus the observed obstruction is not caused by those coarse row
grids.
This is not a counterexample to the fixed network: the root envelope and later
selected-cut local profiles are relaxations, not the exact provider. It does
show that the current LP contract does not close the coupled recurrence. In
particular, `prefix_interval` conditions each local output cut only on the
bag's total mass. The stronger whole-tail interface already derived above is

```text
T_out(k) <= min_{0 <= b <= k} Phi(T_in(b), k-b),
```

where `T_in(b)` is the actual input tail of that same sender. The LP does not
encode this baseline-conditioned correlation, so its positive optimum may be
caused by this missing interface rather than by the per-node outsider budget
itself. The next decisive experiment is to add sound linear relaxations of
these constraints using the global input profile `Z_t`; only if that stronger
gate still fails should the aggregate moment budget be treated as necessary.
The first root-conditioned screen is now implemented in `coupled_rank_lp.py`.
It uses the exact worst-case first-column prefix count for each sampled
baseline, then applies `Phi` over a row gap. At depth4, scale8192, threshold
1/3, root-error allowance `q=11,184,810`, and row stride2048, this added two
available baseline constraints. The optimum remained40,080 terminal wrong
keys, exactly the same as the otherwise identical LP without those constraints
(also213 variables and an optimal solve). Thus this finite gate adds no
aggregate contraction; the baseline/output cuts it can express are too sparse
or the tail envelope is still too weak. This is not evidence against the exact
whole-tail theorem, only against this two-constraint encoding. This motivated
testing whether an aggregate weighted outsider budget removes the residual
instead of summing independent per-cut maxima.

The aggregate/seam experiment is now implemented in `coupled_rank_lp.py`.
At depth4 and 8-bit rows, a1% local full-row area allowance plus0.85%
pointwise seam caps still leaves a positive terminal objective. Replacing the
constant area cap by the mass-sensitive random-core *mean* bound also leaves a
positive objective. These runs use a fractional global-profile relaxation and
are not counterexamples to the network; they show that these scalar local
budgets alone do not close this finite coupled gate. Exact outputs and caveats
are recorded in [`STATUS.md`](STATUS.md). The next step should retain the
cut-dependent alignment/profile state in a contracting recurrence, rather
than merely tightening the aggregate mean.

The depth6 solve returned a HiGHS numerical/unknown status with no incumbent,
so it gives no additional evidence.
Depth8 closure with every-4096th-row cuts did not finish within10 minutes; no
LP was built. Model construction, rather than HiGHS optimization, is now the
experimental scaling issue. Full every-row closure already has65,538 global
cuts at depth4.

The next gate is a sound, sharper root-output contract for the actual
three-sort, followed by its coupled transfer through D2. Exact-root zeroes are
only regression controls; a more tolerant Chvatal-style per-node outsider
budget remains a fallback if the strengthened global profile recurrence still
fails.

## Remaining decisive gate

Derive a closed transfer of these tails through the **actual ordered D2
ports**, including returning child bands and partial-row cuts, and compare
it with future escape capacity. First-sort prefix dominance alone is a
useful restriction, but cannot replace that all-input argument. Establish
the common local witness, root initialization, all-depth flow geometry and
terminal criterion before any Lean work on this candidate.

The stage-cost target remains234*5/4=292.5, conditional on all those gaps.
The additional profile promises must be obtained from the same three sorts.

## Exact port frame and mass-only recurrence diagnostic

The local rank-tail cut frame is resolved for the inflated schedule, assuming
it is implemented by the provider under study. `R1Wire.blockOf` and
`downSetB` select intervals by rank in the static wire order. `R1Exec.stageNet`
feeds each node's local net through `orderEmbOfFin`, and `rankIn_orderEmb`
identifies local position c with rank c. With scale divisible by4096, every
nonempty arity is exactly a 4096-by-n rectangle. `PhysicalPack2Net_exec`
relates the physical and semantic core by a row-preserving permutation:
whole-row counts agree, and a cut inside a row incurs at most its remainder
r. Thus the local rectangle prefix contract applies to actual D2 port cuts,
with the partial-row surcharge already represented in the bound.

`rank_recurrence.py` tests the weakest count transfer that follows from this
interface. For each bag it turns the prefix lower bounds at a port's two
endpoints into an interval for that port's zero count, then adds parent
downports, child return ports and retained inactive mass. It makes no claim
that output ports are internally sorted. Root mass starts as the exact native
prefix. At the terminal stage it checks purity of every native block wholly
below or above the threshold.

The implemented envelope includes the common-witness union factor
`log(2*m^2*(n-1)/eta)/n`: `m` mass classes, `n-1` nontrivial output subsets,
both orientations, and `m` baselines. The latter factor was initially omitted;
the corrected run below supersedes earlier numbers. (The one-round tail event
persists through the later row permutation and column sort, so no second
scramble union is charged.)

At depth7, scale65536, threshold1/3, the corrected relaxation has five D2
rows and leaves63 terminal blocks uncertified as pure. One displayed lower
bound is 30990 below block capacity, while the reported worst unresolved
allowance reaches an entire block. This is loss of information from
independent count intervals and omitted cross-port correlations, not a bad
output witnessed for any fixed network. It shows the corrected mass-only
recurrence does not close the terminal gate. The next useful model must retain
a coupled rank-tail/profile state across ports and stages, or prove a
separate cheap repair. Root/fixed-core selection, tiny-rank and all-depth
terminal/depth gates remain open; no Lean theorem or coefficient improvement
follows from this diagnostic.

The physical-frame source chain is `R1Wire.blockOf`/`downSetB`,
`R1Exec.stageNet`/`rankIn_orderEmb`, and `Chvatal.PhysicalPack2`'s
`physicalPack2Net_rowRegion_card`. It settles whole-row count preservation
for exact rectangles and bounds an interior-row cut discrepancy by its
remainder. This remains conditional on implementing the inflated schedule's
exact rectangular arities with this provider; no ragged embedding is claimed.

## Coupled-flow stress test and reachability gap

`coupled_rank_lp.py` retains one cumulative output profile per active bag,
links all port counts to those common profiles, and carries the exact routed
counts through the whole D2 horizon. It uses the corrected baseline-uniform
rank-tail lower bounds, exact root output (the root input is already sorted),
and exact linear-flow equalities. Its rounded extremizer is checked against
every LP constraint with integer counts. At d6, scale65536 and threshold1/3,
the relaxation still allows 7,884,863 wrong keys across wholly one-colored
terminal blocks, with up to1,904,413 in one block. This is not a counterexample
to the fixed comparator core: local profiles remain adversarial choices and
the LP omits the requirement that each output prefix dominate the actual
input prefix. It does show that coupled port conservation plus the shifted
rank-tail promise still does not imply terminal purity.

The ordered `sparse_probe.py --rank-core` oracle includes that local
input-prefix dominance for a chosen trace. With corrected uniform tails,
d12, scale65536, threshold1/3 and root-error fraction10^-6, the outer-end,
left-end, and right-end band profiles all finish with zero error outside the
threshold-straddling terminal block; its remaining error is1782. These are
input-dependent oracle traces from assumed initial bands, not a fixed core or
an initialization theorem for arbitrary input. They identify the most
promising next paper gate: express actual first-sort/input-profile dominance
inside a shared global rank-profile recurrence, including the root state.
If that cannot be made finite and closed, this local rank-tail route is not
yet supportable at the nominal292.5 stage cost.

## Two finite checks of the profile coupling

The LP now optionally adds sampled local full-row dominance cuts and a shared
concave first-column row-count profile. At depth6, scale4096, threshold1/3,
root-tail initialization and every-256th row cut, the LP has39,072 variables
and still allows456,448 wrong terminal keys (fractional optimum). This matches
the earlier selected-cut objective to the displayed precision; the sampled
profile strengthening has not reduced the obstruction. It remains an LP
relaxation, not a comparator-network counterexample. Increasing cut density
quickly makes the closure large: the corresponding every-row closure has
393,498 global cuts. Commands are exposed by `profile_cut_closure.py` and
`coupled_rank_lp.py`.

`profile_conditioned_tail.py` independently enumerates small column-height
profiles and sums their exact hypergeometric event probabilities, giving an
exact finite union bound over profiles and output subsets. It does not compute
the exact probability of the union. For rows6 and10, columns8, mass cap16,
and eta=1/1000, the required escape allowances for fringe widths1 through
3 are respectively12,9,6 and13,10,8; the matched fixed-cap analytic envelope
is14.65,13.31,12.09. The gains are small and finite-size only. This screen
offers no uniform asymptotic improvement and does not change the global gap.
Fresh-context review by GPT-6-Luna confirmed the hypergeometric normalization,
profile multiplicities, and matched analytic comparison.

## Terminal-use limitation of the aggregate 448 transfer

The bound sum_t error_t <= parentError + 448*tiles cannot by itself certify a bounded-width set of dirty terminal tiles: it permits a nonzero error in every tile (including roughly 448 units per tile when parentError is small). Thus it does not imply a single N^theta dirty interval, nor a fixed number of seam windows. A terminal proof using this transfer needs a stronger max-per-tile or multiscale tail invariant, or a separately priced cleanup whose depth handles a linear number of distributed tile errors. This is why the 448 step alone is not the missing coefficient-300 theorem.

## Receiver-tile incidence diagnostic

A new exact finite-state screen (eceiver_fiber_types.py) enumerates every reachable shared parent-state context and its eight child receivers. At (3,3,2), scale 8192, the maximum number of distinct source physical tiles feeding one receiver tile is at most four through depth 9; a direct global-cell audit agrees through depth 7. The backward-cone screen (eceiver_ancestor_screen.py) reports maximum source-tile ancestry 9, 4, 5 at depths 5, 6, 7. These screens use exact static 4096-cell routing and are useful for targeting a finite-state proof, but they do not establish an all-depth bound. Even a fan-in bound of four gives no contracting pointwise error recurrence by itself. A closed spatial potential must account for how local 448-unit error is distributed among ports and how ancestry evolves over every stage.
