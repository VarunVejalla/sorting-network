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

For depth6, scale4096, threshold `floor(N/3)`, root-tail mode produces an
integral selected-cut LP witness with 456,448 wrong keys in terminal
noncrossing blocks (141,903 in one block). Its first root-row prefix defect is
2,730, exactly the worst-case first-column lower bound at that cut. This is
not an actual-network counterexample: local prefix dominance is imposed only
at the finite selected cuts, and the rank-tail bounds are still coarse. It
shows that this finite interface does not close the 292.5 gate. The next
specific gap is stronger all-cut reachability/tiny-rank control for the same
fixed 3-sort, together with a root profile guarantee sharp enough to remove
the surviving remote defects.

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
