# Independent search for a proved coefficient at most300

> Current handoff: [prefix-flux/HANDOFF.md](../upper-bound/experiments/prefix-flux/HANDOFF.md). This file is a historical search ledger; its older candidate prices and next steps are not current status.

Date: 2026-10-25. Owner: Codex (GPT-6). Goal remains active and unachieved.
Worktree `.claude/worktrees/sub300`, branch `sub300-structural`, based on
main `5f03290`. The root checkout and UB-34/UB-37 work are untouched.

## Verified baseline and acceptance conditions

Promoted endpoint:789.75. `Sub800/R1Nets.lean` charges
2709 +1053*(3d-15)+136 on16^d inputs, giving3*1053/4=789.75.
Ordinary stage depth must be at most400 at the unchanged3/4 stage/log rate
to reach300. The current R1Point API itself cannot do this: its exact-sort
threshold requires stage>=S(38), and its3*S(q) quantization forces stage>=759.
A genuinely new provider, threshold treatment, or global schedule is needed.

Formalization starts only after a candidate has:

1. A fixed input-independent network, including every frontier and tail.
2. A uniform all-input correctness invariant and exact terminal sorting test.
3. Complete global comparator-depth accounting, including local exact cases.
4. Independent fresh-context paper review, with blocking findings resolved.

R1Final already supplies a valuable terminal interface: prove geometrically
decaying outsiders, then final bags contain exact native rank intervals and
parallel exact sorting completes. Any new error potential must either imply
that condition or supply an independently proved exact cleanup.

## Initial audit and bounded probe

- Existing UB-37 optimistic tolerance/periodic models do not supply an
  invariant or priced provider. Their minimum numbers are not constructions.
- The newer residual pricing invalidates the old r*=0 model package. The
  root agent's fringe work should proceed independently; do not duplicate it.
- UB-41 tested persistent columns and incoming redistribution. Its
  small-C all-profile square-root recurrence is false, and a deterministic
  sparse-fringe witness violates the weak local contract at the apparent
  sub300 point. Fresh review and exact count checks are in
  `upper-bound/experiments/persistent-columns/{REVIEW,STATUS}.md`.
  Do not rerun that parameter model as a new proof candidate. Fixed-radius
  closure and stronger reachable-state hypotheses are distinct unproved
  questions, not consequences of the rejected recurrence.
- A read-only audit of the legacy Seiferas implementation found a genuine
  generic provider API, but no competitive ready primitive. Its coefficient
  bound is c*Dsep+9, c=ceilLog_(1/nu)(2A). Current conversion from a halver
  of error epsilon/(L+2) costs Dsep=(2L+3)*h,
  L=ceil(log2(ceil(1/(2gamma)))). At the original A10,gamma.01,epsilon.01,
  nu.65 point this is105h+9. Genericity does not by itself make a sub300
  route. Exact scalar guards are in legacy `Bags/Params.lean`, proof in
  `Bags/{Depth,Sorts}.lean`, provider in `Separator/Provider.lean`.

## Next research decision

UB-42 now tests signed prefix flux plus an affordable exact small frontier
on the existing D2 flow. See
[`prefix-flux/STATUS.md`](../upper-bound/experiments/prefix-flux/STATUS.md).
Fresh review caught a missing comparator-prefix constraint; the strengthened
oracle includes it. The larger C65536 frontier passes small samples but fails
at d12 with epsB.01, even with an exact root. These are negative relational
contract diagnostics, not counterexamples to all fixed comparator providers.
No repeated routing identities or speculative Lean were added.
The negative trace now has a scalable escape-capacity explanation in
[`CUT-OBSTRUCTION.md`](../upper-bound/experiments/prefix-flux/CUT-OBSTRUCTION.md):
raising any fixed exact cutoff cannot repair the tested coarse interface.
The next provider/invariant must bound wrong-color mass against future
subtree escape capacity, not merely a fraction of present bag size.
The follow-up [moderate-rank tail](../upper-bound/experiments/prefix-flux/MODERATE-TAIL.md)
has independent hand review and interval-checked local values excluding the
old obstruction's critical choices. A centered ragged core keeps local sort
height fixed, with reviewed bulk surcharge4r per direction for r extra cells.
The nominal292.5 budget remains conditional: a global capacity invariant,
tiny-rank termination and a common certified provider are still missing.
Before the next global test, implement the actual static-label interleaving
from R1Wire/R1Exec; see
[ORDERED-GATE](../upper-bound/experiments/prefix-flux/ORDERED-GATE.md).
Fresh source review found that the old concatenation oracle omits this
reachability restriction. An exact-root diagnostic must be error-free in
the faithful ordered model; a real proof needs a precise constant-depth root
and contraction from its nonzero initial error.
That ordered model is implemented and fresh-reviewed, including an ideal-rank
cut inside output ports. Its passing samples retain an unpriced fringe
assumption and are not proofs. A separate reviewed tiny-fringe probability
point and [inflated schedule](../upper-bound/experiments/prefix-flux/INFLATED-SCHEDULE.md)
remove some local-price/padding gates conditionally. The uniform global
profile recurrence is the central unresolved step; do not start Lean yet.

The exact compressed flow and sparse adversary now preserve error positions
without enumerating the full tree. A mandatory first-column-sort restriction
excludes sampled capacity failures left possible by the bulk/fringe-only
ordered contract. See [PROFILE-GATE](../upper-bound/experiments/prefix-flux/PROFILE-GATE.md)
for its independently reviewed shifted-profile tail lemma and the precise
remaining D2 transfer obligation. Neither passing adversarial samples nor
that local lemma proves the conditional292.5 sorting bound.

### Inversion-localization terminal alternative

The tracked global prefix defect has aggregate
`sum_r F(r) = inv(w)`, the binary inversion count. If a priced prefix schedule
could prove `inv(w) <= n^theta`, every error would lie within `n^theta` wires
of the threshold. A fixed recursive chunk/seam cleanup then gives coefficient
`(p+theta)/(1-theta)` from a prefix-stage coefficient `p`; at `p=292.5`, it
requires `theta < 15/602` for a strict result below300. The exact identities,
cleanup argument, and conditional gate are in
[`INVERSION-LOCALIZATION-GATE.md`](../upper-bound/experiments/prefix-flux/INVERSION-LOCALIZATION-GATE.md).
This replaces exact terminal native-block purity with a precise alternate
gate, but no current UB-42 recurrence proves the required inversion exponent.
The parameterized `(3,3,2)` core has conditional `p=273` and relaxes the gate
to `theta<27/301`; its row-height-13 provider is still missing. Finite ordered
oracle traces reach only the threshold-crossing terminal block through depth
24, but their measured inversion exponents are still well above the gate.

The latest gate check closes the local physical-frame objection: under the
inflated schedule, static D2 ports are rank intervals in each node's ordered
local input, and the semantic/physical permutation preserves row counts.
However, a conservative recurrence that propagates only independent
zero-count intervals through port endpoints, with the corrected common
baseline-witness union factor, fails terminal purity at depth7 (63 unresolved
blocks). This does not refute fixed cores; the relaxation forgets
correlations between ports and successive profiles. The next paper candidate
must retain a coupled tail/profile state or specify a priced terminal repair.
The physical-frame statement is conditional on exact rectangular arities and
the `PhysicalPack2` provider. Details and reproducible script are in
[`prefix-flux/PROFILE-GATE.md`](../upper-bound/experiments/prefix-flux/PROFILE-GATE.md)
and `rank_recurrence.py`.

A stronger global LP now retains common local output profiles and exact
cross-stage port conservation. Tail bounds alone still admit integral
terminal impurity even from an exact sorted root; the omitted first-sort
dominance is decisive. The ordered per-trace oracle passes outer/left/right
band samples after a small assumed root error, but does not construct a fixed
provider or handle arbitrary root profiles. The paper route's next gate is a
closed all-input recurrence that carries this comparator reachability.

### Independent UB-28 randomized-network candidate

The most promising current structural lead is UB-28 with an exact depth-15
sorter on every fixed 32-wire block, followed by randomized matching stages
only at widths `h >= 64`. The remaining bad event is a boundary predicate on
two block counts, `left > 0` and `right < 32`. A top-relative `(223,27)`
round schedule has modeled coefficient 250. At `n=2^24`, its grid-16
max-path screen over 97 boundary/interior representatives has minimum
`0.7233649`, above `ln 2`; keeping all width-32 counts through the first
width-64 stage barely changes the sampled center rate. This replaces the
complicated small exact-tail event with a simpler block-count event.

The rate direction needs care: maximizing log-probability over a restricted count lattice gives a lower maximum log-probability and therefore an upper bound on the minimum negative-log cost over all trajectories. More seriously, the grid misses a feasible modal path: from balanced top halves, the (223,27) schedule reaches terminal counts (29,28), which trigger the bad boundary event. Each modal transition costs at most log(h+1), so this path has only an exp(-O(log^2 n)) probability for a balanced input type. The script reproduces the bad terminal profile for all exponents 7 through 100 and sampled exponents through 1024; proving the recurrence for all scales is the next check. If it holds asymptotically, the random-network first-moment route is dead. Do not invest in a continuous Bellman certificate for this schedule before resolving that path. Details are in [UB28-WIDTH32-TAIL.md](../upper-bound/experiments/UB28-WIDTH32-TAIL.md).

No credible <=300 construction has yet passed the paper gates. Prioritize a
new local/global contract rather than another scalar retune. Two precise
possible directions remain to screen:

- A fixed-radius/temporal column-tail invariant, with the actual receiving
  network specified, that excludes both UB-41 adversaries through provable
  reachability. It must price rare-rank control without another full sort.
- A rank-sensitive multiway potential and explicit cheap primitive that
  permits moderate bulk error yet implies terminal native purity. Existing
  aggregate leakage alone allows nonlocal bin swaps; it needs a stronger
  location/tail statement or a fully priced repair.

Do not choose between them merely by an optimistic depth division. Derive a
closed count/target transfer and test its adversarial extremizers first. Use
new tickets for materially different constructions, and record a bounded
negative probe rather than expanding unproved Lean plumbing.

### Independent packet-mixing gate

The current signed-flux route is not rescued by its tiny-fringe parameter:
that parameter controls ranks near `10^-100` of the width, whereas the ordered
oracle's stranded 133 errors occur at a macroscopic cut. Its current local
contract therefore remains a negative result, not a credible 292.5 proof.

I screened a more structural UB-25 variant in
[`PACKET-MIXING-GATE.md`](../upper-bound/experiments/PACKET-MIXING-GATE.md).
After inspecting the current UB-25 worktree, I replaced my initial coarse
L1 screen with its sharper one-cycle energy estimate. A rank/Frobenius lower
bound on contraction leaves a narrow numerical possibility: `(q,s)=(16,23)`
uses391 layers (coefficient293.25) and would meet the optimistic
`36/105000 ~= 0.0003429` bulk proxy if the matching product has spectral norm
at most `0.0010205`. Fresh review verified the sharpened variance estimate.
However, a reproducible matrix-free random-matching screen gives roughly
`0.0027` at 23 rounds for packet counts up to262144, so random cycles miss the
gate. The proxy comes from a different schedule with the fringe idealized
away. No explicit structured family or global packet-routing proof exists;
rare cohorts and reassembly remain open. See the local gate for derivation
and commands.

### UB-28 whole-network candidate screen

I implemented the ticket's descending dyadic schedule literally in
[`ub28-small-screen.py`](../upper-bound/experiments/ub28-small-screen.py): at
each scale it runs `d` independent random cross-matchings on even neighboring
block pairs, then `d` on the one-block-shifted pairs. Every comparator sends
the minimum to the lower block. For `d=99`, the depth is exactly
`198 log2(n)` on powers of two. Five independently sampled networks at each
of `n=2,4,8,16` sort all Boolean inputs (the script checks all `2^n` inputs
exactly via bit-parallel execution). At `n=8,d=1` all four sampled networks
fail; at `n=8,d=2` three of four fail; at `n=16,d=4` three of four fail.
The script also extracts paired forcing certificates for each sampled failure;
at `n=8,d=1`, the displayed examples have disjoint initial 1/0 leaf sets of
sizes four and three.
Thus the witness screen exercises real failures and confirms the proposed
high-budget candidate is not trivially malformed, but it provides no
all-size probability bound. It also has no separate terminal cleanup charge:
the candidate must sort exactly through its dyadic passes. See the UB-28
ticket for the required paired-certificate counting argument. Reproduce the
small screen with `python upper-bound/experiments/ub28-small-screen.py
--n 16 --d 99 --seeds 5`; use `--witness` on a failing parameter to print a
certificate pair.

The clean paper target is now explicit. For a random schedule `N`, let `W(N)`
count the distinct triples `(i,S1,S0)` where `i,i+1` are adjacent outputs and
some forcing certificates require output `i=1`, output `i+1=0`, with disjoint
initial leaf sets `S1,S0`. A failure implies `W(N) >= 1`; hence the uniform
estimate `E[W(N)] < 1` would prove that some schedule sorts every Boolean
input. Counting distinct support pairs avoids needless overcounting of
different proof trees with the same leaves, while still requiring a sound
treatment of shared dependencies. The fresh-context review confirmed the
schedule/depth and finite witness code, and identified this expected-count
bound as the central missing theorem. The screen covers powers of two only,
but all-`n` extension is available once that gate closes: the legacy
`AKS.Sort.Shrink.restrictWires_sorts` and `restrictWires_depth_le` lemmas
restrict a power-of-two sorter to any smaller wire count without increasing
depth. This remains a model-level research candidate, not a proved sorting
bound.

A separate fresh-context review of the counting gate found no viable
independent-branch recurrence: a depth-`L` certificate may branch to `2^L`
leaves, and reconvergent paths make independent collision probabilities
invalid. Keeping exact leaf sets risks an input-sized state space. This blocks
the naive witness count, not the network itself. Any next recurrence should
track both certificates' live frontiers and shared-variable constraints, then
be checked against exact small-network certificates before an asymptotic bound
is attempted.

### UB-28 alternative: first moment over uniform inputs

There is a first-moment route that avoids paired certificate leaves: sample a
Boolean input uniformly together with a random matching schedule and try to
bound `E[F(N)] = 2^n P[N(X) is unsorted]`. A single cross-matching count
transition is exact: for input block counts `a,b`, the left output count is
`X ~ Hypergeom(h,b,a)` and the right count is `a+b-X`. The count-vector
recurrence is also exact for this annealed expectation. The uniform input law
is invariant under independent permutations of wire slots within each block.
A randomized cross-matching layer preserves that invariance: relabeling the
slots in its two blocks simply conjugates its uniform matching permutation.
Splitting a block into halves restricts the symmetry to independent
permutations within each child block. Inductively, conditional on the complete
block-count vector, all block patterns are independent uniform subsets.
Hence the hypergeometric matching and split kernels in
[`ub28-count-process.py`](../upper-bound/experiments/ub28-count-process.py)
are exact for `P_{N,X}[N(X) is unsorted]` when `X` is uniform and the schedule
matchings are independently uniform. The width-2 singleton example only
refutes this claim for a fixed input; it does not refute the annealed
first-moment recurrence. The local edge transfer is exact for the same
ensemble, provided its terminal bad-edge predicate is the exact count-based
tail predicate.

If `F(N)` is the number of Boolean inputs not sorted by sampled network `N`,
then `E[F(N)] = 2^n P[N(X) is unsorted]`. An all-size bound `E[F(N)] < 1`
would give a sorting network by the first-moment method, then the usual
zero-one principle and wire restriction give the claimed all-`n` result. At
The previously proposed 70-round schedule would have depth
`140 max(log2(n)-8,0)+510`; this is a candidate bound conditional on proving
the all-size first-moment estimate below.

The zero-one principle does not reduce this probabilistic gate to the `n+1`
monotone bit strings. Those are thresholdings of a fixed ordered input;
sorting-network correctness requires every binary assignment, since an
arbitrary inversion can threshold to an arbitrary subset of wires. Thus the
first-moment gate really must count all `2^n` inputs (or use a different
certificate count that still covers every assignment).

[`ub28-count-process.py`](../upper-bound/experiments/ub28-count-process.py)
implements the exact annealed rational model at small sizes. For `n=8`, one
random matching per pass gives `E[F]=58/3`, matching exhaustive enumeration of
all 192 schedules and all 256 inputs. At `n=16`, eight rounds gives
`E[F]=259465172802051769457880750622855061 /
1379746024126718839235385753600000000 < 1`. With sixteen rounds at widths 8
and 16 and exact deterministic splitters below width 8, it gives
`E[F]=0.0008828413466643175` at `n=32`. At `n=16`, seventy rounds at width 8
and exact splits below it give `E[F]=0`. These are actual annealed expectations
for the specified schedule; values below one certify existence only at those
finite sizes. A direct vector-state computation at `n=32` without low-width exact
splitters exceeded 500 MB and was stopped. The new challenge is to prove a
uniform-in-`n` bound on this first moment without enumerating all count
profiles; no such bound is established yet. A direct exact-rational run at
`n=64`, 70 rounds, and exact splitters below width 8 was also stopped after
about 100 seconds at roughly 8.6 GB resident memory, before producing a result.
So the count recurrence is a small-size exact verifier, not a scalable
uniform-in-`n` proof; a next computational step needs profile compression or
a rigorous local large-deviation bound. Separately, a SAT check of the deterministic cyclic `h=4,2,1`
tail on 32 wires found an unsorted output for input
`11000000111110111100100111111111` (wire 0 is the least-significant bit; the
tail leaves an inversion at wires 0 and 1). Thus the exact small-width tail is
not a stand-alone sorter for arbitrary residual arrangements. A valid profile
bound has to retain enough information about the state entering that tail;
assuming the tail cleans every residual state would be unsound.

There is a sharper finite terminal gate. For the deterministic cyclic `h=4,2,1`
tail, [`ub28-terminal-profile-screen.py`](../upper-bound/experiments/ub28-terminal-profile-screen.py)
checks every nondecreasing profile of width-4 input-block counts by SMT.
At `n=32`, all 495 profiles with partial blocks (counts 1, 2, or 3) spanning
at most three consecutive blocks sort for **every** arrangement within the
blocks. At `n=64`, the same criterion holds across all 4,845 profiles; the
first counterexamples appear at span 4. This supports a finite-state terminal
lemma, but does not prove its extension to all lengths or cover nonmonotone
profiles.

The gate is too strong for a direct first-moment proof. The exact count
recurrence in [`ub28-terminal-gate-mass.py`](../upper-bound/experiments/ub28-terminal-gate-mass.py)
gives `P[outside gate]=0.33676676654` with 16 matching rounds at widths 16 and
8, and `0.329109175927` with 70 rounds. Multiplying by `2^32` gives over a
billion inputs outside the gate. This does not estimate actual tail failures;
it rejects only the plan of charging every input outside the universally safe
set as a failure.

The exact `h=4,2,1` tail has a stronger simplification: its final output is
determined by the incoming width-4 block-count profile alone, for arbitrary
arrangements inside those blocks. For the cyclic `K_{h,h}` gadget, every
cross pair is compared, so a left 1 and right 0 cannot both remain; left
zeros and right ones are absorbing, forcing output counts
`(max(a+b-h,0), min(a+b,h))`. After the width-4 passes determine the width-4
counts, the width-2 even pass compares the two sibling width-2 blocks inside
each width-4 block and erases their unknown split. The width-2 odd pass then
acts on known counts. The width-1 even pass sorts each width-2 block, so the
final odd pass is determined as well. A fresh independent audit checked this
induction for arbitrary lengths divisible by four, including the unmatched
boundary blocks. [`ub28-terminal-count-gate.py`](../upper-bound/experiments/ub28-terminal-count-gate.py)
implements the resulting profile-to-output map.

There is an even smaller terminal condition. Let `e_j` be the width-2 counts
after the width-2 odd pass, with `m` the number of such blocks, and set
`L_j = [e_j=2]`, `R_j = [e_j>=1]`. After the width-1 even pass, each block is
`(0,0)`, `(0,1)`, or `(1,1)` according to `e_j`; the final odd pass compares
`R_j` with `L_(j+1)`. Its output is sorted iff none of these local conditions
holds:

```text
j = 0:          e_0 = 2 and e_1 < 2
0 < j < m-1:    (R_(j-1) or L_j) and not (R_j and L_(j+1))
j = m-1:        e_(m-2) > 0 and e_(m-1) = 0
```

Thus terminal failure is a union of bounded-window events in the incoming
width-4 counts. [`ub28-terminal-window-language.py`](../upper-bound/experiments/ub28-terminal-window-language.py)
propagates exact input supports and enumerates the local truth tables; one
adjacent output pair depends on at most six width-4 counts. The randomized
prefix count recurrence agrees exactly with the full `ub28-count-process.py`
failure probability at `n=32`, for both 16 and 70 matching rounds at widths
16 and 8. The expected failing-input counts are `0.000882841346664` and
`1.58277276181e-46`, respectively, with the exact tail below width 8. The
terminal accounting is closed for every length divisible by four. The open
proof gate is to bound the probability of these local bad windows under the
randomized prefix uniformly in `n`; the sum over all windows must be below
`2^-n` for the first-moment argument.

There is a useful backward-locality reduction for that gate. For one fixed
final adjacent inversion, the dependency support of its exact-tail predicate
has at most six consecutive incoming width-4 counts. Reversing a count pass
only closes this interval under that pass's disjoint adjacent pairs; reversing
a uniform block split maps child indices `j` to parent indices `floor(j/2)`.
After the split, the support has at most three indices, and the two reverse
offset passes at the next scale expand it to at most six again. Thus the
backward transfer for a single output edge has at most six count coordinates
at every scale, rather than the full profile vector. The exact terminal support
and this recurrence are checked for every edge through `n=4096` by
[`ub28-backward-window-support.py`](../upper-bound/experiments/ub28-backward-window-support.py).
[`ub28-local-edge-transfer.py`](../upper-bound/experiments/ub28-local-edge-transfer.py)
then evaluates the exact backward transfer for one edge, applying the
hypergeometric split kernels and randomized matching count kernels on only
these supported coordinates. Summing the edge probabilities gives a valid
union bound. With `--n 32 --check-full`, it matches the full-profile recurrence
up to the expected union-bound slack: for 16 rounds, the upper bound on
`E[F]` is `0.000882841346720` and the exact value is
`0.000882841346664`; for 70 rounds, both print as `1.58277276181e-46`.
This verifies the local transfer as an exact finite-size calculation, not an
asymptotic estimate. Its table still has up to `(h+1)^6` entries at block
width `h`; the next target is to compress or bound these local functions
uniformly as `h` grows, then sum the resulting edge bounds. A separate audit
checked the six-coordinate recurrence semantically for all powers of two,
including boundary clipping. As a larger finite screen, at `n=64` and the
central even edge 30 the exact local transfer gives `P[bad]=1.2267e-14` for
16 rounds and `1.8522e-62` for 70 rounds. This points toward a large-deviation
rate proof, but one edge and two finite sizes do not establish the required
uniform bound.

For the full profile, a spatial cut through the multiscale factor graph
crosses `O(log n)` scales. Its naive transfer state count is about
`prod_k (2^k+1) = 2^(Theta((log n)^2))`, quasipolynomial in `n`. The local
edge transfer avoids that full-profile state, but still has a six-coordinate
table with `h+1` values per coordinate at width `h`. The next useful
investigation is whether hypergeometric kernels preserve a low-rank, moment,
or exponential-tail certificate for those local functions as `h` grows. A
promising quantitative version is to derive a finite-dimensional entropy
variational bound for a bad terminal edge and prove its rate exceeds `ln 2`,
uniformly over edge phase and input density. No uniform asymptotic failure
bound is known yet.

### UB-28 local rank-sensitive spill estimate

The `1/9`-halver cap is too coarse to compose by itself: the scalar relaxation
in `ub28-scalar-halver-screen.py` has a counterexample at `n=1024` on a sparse
input. The random matching process has a stronger local estimate. Fix a pair
of `h`-wire blocks with total `c<=h` ones, and let `A_t` be the left-block one
count after `t` independent uniform matchings. Conditional on `A_t=a`, the
next count is hypergeometric with mean `a(c-a)/h`. Hence

```text
E[A_(t+1)] <= E[A_t] * (c-E[A_t])/h,
E[A_d] <= min(c*(c/h)^d, c/(1+d*c/h)).
```

The first estimate follows from `E[A_t^2]>=E[A_t]^2`; the second follows by
iterating `E[A_(t+1)]<=(c/h)E[A_t]` and by applying the reciprocal logistic
recurrence, respectively. By complement symmetry, if `c>=h`, the same bounds
hold for the right-block zero count with `c` replaced by `2h-c`. In particular,
balanced inputs leave at most `h/(d+1)` expected spill, while a sparse pair
has exponentially small probability of any spill. This is exact for each
fixed input arrangement under the random schedule; it does not require the
blockwise-uniform invariant.

This is a useful local potential, not yet a global proof. It indicates how
large balanced spill can become sparse after the next dyadic split, but the
shifted pass couples neighboring spill profiles. A valid closure must track
their positions or a weighted profile through both offsets; the scalar
`1/9`-only counterexample rules out replacing that work by independent caps.

There is also an exact local higher-moment tail bound. Write
`(x)_r=x(x-1)...(x-r+1)`. Given `A_t=a`, a random matching chooses a uniform
`a`-subset of right wires, so

```text
E[(A_(t+1))_r | A_t=a] = (a)_r (c-a)_r/(h)_r.
```

For `1<=r<=h`, this is at most `(a)_r q_r`, where
`q_r=(c-r)_r/(h)_r` (take the numerator as zero if `c<2r`). Iterating over
fresh matchings and applying Markov gives

```text
P[A_d >= r] <= binom(a_0,r) q_r^d.
```

This holds for every fixed initial arrangement; if `c>=h`, apply it to right
zeros with total `2h-c`. For `a_0/h -> alpha`, `c/h -> gamma`, and `r/h -> rho`,
the log of this bound divided by `h` tends to
`alpha*H(rho/alpha) + d*((gamma-rho)*H(rho/(gamma-rho))-H(rho))`, with
`H(x)=-x log(x)-(1-x)log(1-x)`, for `rho<=alpha` and `2rho<=gamma<=1`.
The identity is independently audited in the local-process review. It sharpens
the mean spill estimate for a fixed pair, but does not count compatible error
paths through the changing dyadic pairs.

I checked whether simply strengthening the scalar cap repairs the interface.
For the packed input `1^(n/4) 0^(3n/4)`, let `q_min` be the least integer `q`
for which the full scalar relaxation with a `1/q` halver cap sorts that input
(all widths below 200 are still exact). The screen gives:

| `log2(n)` | 10 | 11 | 12 | 13 | 14 | 15 | 16 |
|---:|---:|---:|---:|---:|---:|---:|---:|
| `q_min` | 23 | 32 | 45 | 64 | 91 | 128 | 181 |

For the half-full packed input the corresponding minima are `23, 33, 46, 65,
91, 129, 182`. The current script accepts `--epsilon-denominator` to reproduce
individual screens; for example, `--max-log 11 --epsilon-denominator 24`
checks every total through `n=2048` and first fails at 2048. This near-doubling
of the required denominator per two levels shows that a fixed scalar error
allowance does not close this relaxed model; it is finite evidence, not an
asymptotic impossibility proof for the actual matching schedule. A useful
global argument needs position-sensitive information (such as the local spill
estimate or tail bound above), rather than only a uniform error fraction. The
growth may reflect loss of the actual local comparator reachability in this
relaxation; it is not a lower bound on spill in the real random-matching
process.

The useful local gate is now closed at hand-proof level: 70 cross-matchings
can form a `1/9`-halver for every block width `h>=200`, and smaller widths use
exact complete bipartite gadgets. The random-graph expansion and rectangle
bounds were independently checked in fresh context; the elementary constants
have exact-rational checks in
[`UB28-LOCAL-HALVER.md`](../upper-bound/experiments/UB28-LOCAL-HALVER.md) and
[`ub28-halver-bounds.py`](../upper-bound/experiments/ub28-halver-bounds.py).
This makes a 140-per-log two-offset local-gadget budget credible, but does not
close the whole-network gate. The next proof obligation is a multiscale transfer for
paired one/zero forcing supports (or an equivalent rank-profile invariant):
the 1/9 local threshold alone gives no control over where residual errors
sit inside the next blocks. The legacy halver-to-separator bridge still
accumulates error linearly in the number of levels and therefore does not
yield a sub-300 coefficient from this primitive.

The generic legacy Seiferas-bag route is quantitatively incompatible with
this direct `1/9` halver as well. Its parameter constraints include
`1 <= gamma*A^2`, `(2*epsilon*A)^2 < 1`, and
`nu >= 4*gamma*A + 5/(2*A)` with `nu<1`. These imply
`epsilon < sqrt(gamma)/2` and, by minimizing the right side of the last
inequality over `A`, `gamma < 1/40`. Thus the separator level count must have
`gamma=2^-t < 1/40`, hence `t>=6`; but `halverToSeparator` charges
`epsilon=t/9 >= 2/3`, contradicting `epsilon < 1/(2*sqrt(40))`. This rules out
feeding the unamplified local halver through that existing bag parameter
interface. A sub-300 proof needs a direct schedule invariant or a genuinely
different global composition theorem.

I also simulated the correctly priced mixed schedule (70 matchings for
`h>=200`, exact cyclic `h`-matching gadgets below 200) in
[`ub28-actual-schedule-screen.py`](../upper-bound/experiments/ub28-actual-schedule-screen.py).
Four independently seeded schedules each sorted 22 selected inputs at
`n=256,512,1024,2048` (random words and several prefix weights). The measured
layer counts were 510, 650, 790, and 930, matching
`140 max(log2(n)-8,0)+510`. This is only a finite smoke test and does not
address the all-input witness-counting gate. A 60-second Z3 check of a
necessary-reachability relaxation at `n=256` returned `unknown`; it gave no
positive or negative evidence, so its exploratory solver scripts were removed.

I tested the scalar-only interface directly in
[`ub28-scalar-halver-screen.py`](../upper-bound/experiments/ub28-scalar-halver-screen.py).
It lets each paired-block transformation be any bit profile satisfying both
the 1/9 split-count bound and the necessary fact that no prefix gains ones;
for widths below 200 it imposes exact block separation. This relaxation has a
counterexample at `n=1024`, `H=45`: it permits a residual inversion at wires
766/767. This is not a counterexample to actual comparator matching gadgets;
it shows that their scalar halver and prefix-monotonicity contracts alone do
not prove the global schedule. The missing invariant must retain more of the
actual cross-matching reachability or the paired forcing supports.

### UB-28 top-heavy schedule candidate

A top-relative schedule screen in the exact annealed count model suggests a possible
structural improvement: use
`r=260` matching rounds per offset at every other scale counted down from the
top, and `r=20` on the intervening scales. Keep 150 rounds at widths 8 and 16
and the exact tail below 8. The two offsets then cost
`280 log2(n)+O(1)` layers. See
[`UB28-TOP-HEAVY-SCHEDULE.md`](../upper-bound/experiments/UB28-TOP-HEAVY-SCHEDULE.md)
for max-path screens and the exact proof gate. At `n=2^24`, a central-edge
coarse-lattice path screen gives rate about 0.8165, above `ln 2`; besides the
full-state and all-phase gaps, this screen is not a certified outer bound over
all count paths. The count model itself is exact for the annealed ensemble.
This is only a schedule diagnostic, not a candidate sorting theorem.

### UB-28 local state and rate gate

The annealed product-permutation invariant makes the block-count vector an
exact Markov state for the uniform-input/random-network first moment. For a
fixed terminal edge, its backward dependency cone contains at most six block
counts at every scale, by the exact-tail support and pairing-closure argument.
The local edge transfer therefore avoids the exponentially large full count
vector while remaining exact for the annealed law. Joint wire-pattern
histograms are an optional richer state, not a repair for a failed count
recurrence.

The exact check in
[`ub28-joint-histogram-check.py`](../upper-bound/experiments/ub28-joint-histogram-check.py)
enumerates every pattern for `(width, support)=(2,6),(4,3),(4,4)` and verifies
matching lumpability for both adjacent pair phases plus the split kernel when
the incoming columns are uniformly exchangeable conditional on their joint
histogram.
The matching transition also has a triple-type count: for predecessor,
current, and successor type table `T`, its exponential cost is `I(C;A,B)`.
Exact factorial formulas and small exhaustive checks are recorded in
[`UB28-JOINT-PATTERN-STATE.md`](../upper-bound/experiments/UB28-JOINT-PATTERN-STATE.md)
and [`ub28-matching-triple-types.py`](../upper-bound/experiments/ub28-matching-triple-types.py).
For the first-moment ensemble, the uniform input and independent matching
schedule give a product-permutation invariant: conditional on block counts,
block patterns are independent uniform subsets. Thus the split kernel is
valid; the fixed-input example of two zero rows and an untouched patterned row
does not apply to this annealed law. The joint histogram state is optional,
since the block-count process already closes. The remaining work is to certify
the rate over all phases and compare its exponent with `ln 2`. Forward
transitions may project away whole block rows only after the complete backward
cone is fixed. The exact width-4/2/1 tail is count-based by the cyclic
complete-splitter argument and explicit width-2-count predicate. See
[`UB28-JOINT-PATTERN-STATE.md`](../upper-bound/experiments/UB28-JOINT-PATTERN-STATE.md).

A finite-cutoff boundary warning is recorded in
[`ub28-exact-suffix-screen.py`](../upper-bound/experiments/ub28-exact-suffix-screen.py):
at `n=1024`, edge508, the exact suffix from width128 down fails on six
width-128 blocks that are constant with row values `(0,0,1,1,0,0)`. The
screen also finds a less extreme width-128 count profile
`[35,24,64,37,79,25]` whose pair totals are ordered `59 <= 101 <= 104`, yet
the suffix still leaves `10` at edge508. These ordered counts are compatible
with the necessary count inequalities after the width-256 offset passes: the
input has a zero prefix and a one suffix, so the fourth width-256 row really
is full of ones. A specified positive-probability sequence of width-256 and
width-512 matchings preserves the profile and leaves the exact suffix
inversion. Its probability is about `10^-9014.528` for 70 random rounds; this
is a valid finite local failure event but far too small by itself to refute a
whole-network first-moment bound.
zero-cost mean-field diagnostic in
[`ub28-mean-field-screen.py`](../upper-bound/experiments/ub28-mean-field-screen.py)
assigns positive mass to the corresponding column type at the cutoff. This is
not yet a no-go proof, because the probability of reaching that finite profile
under the actual upper prefix has not been bounded. The finite suffix must be
included in the coupled rate calculation and cannot be assumed to sort all
locally count-ordered inputs.

### D2 endpoint reserve status (2026-10-22)

In the standalone schedule model, the exceptional `botRise` predecessor now
has a kernel-checked child-reserve lemma: inactive children remain at native
deficit until their later cut, exactly supplying its `c/128` endpoint
reserve. The focused file check passes. This advances one branch of the
candidate's reserve induction, but does not connect the ordinary predecessor's
cut geometry or establish native-size bounds on its children. The eight-child
quota sum is now resolved from schedule roles, conditional on those native
bounds: regular child roles give total mass `15/16`, while the exceptional
`botRise` branch gives mass1 and forces the older sender's quota to `15/4096`.
The factor corollary compiles under the exact two-step identity and deficit
caps. A separate compiled lemma now forces current cuts to be noncrossing when
the two-stage predecessor is ordinary, given native allocation bounds and
the same exact identity/caps; the `botRise` predecessor has its trace-based
route, now including a compiled `a/c<=1/16` bound from trace conservation.
These are still conditional induction interfaces, not an all-depth flow
proof. The D2 coefficient candidates (273 for the row-13 `(3,3,2)` core, or
227.5 for the sparse-bottom variant) remain conditional; the shrinking-fringe
screens, exact-shape obstruction, local provider, global rank recurrence, and
terminal sorting contract still prevent calling either a realistic completed
path below300.

Later the same day, `D2ScheduleReserve.lean` gained a sentinel-aware
`D2FlowTree`, a kernel-checked full-tree initialization invariant, and a
recursive `d2FlowStage` matching the compressed Python step's
descendant-first/old-child-root order. Its callbacks now implement the rounded
D2 activity, role, and scale8192 integer quotas. Schedule/role matching,
active capacity exponent `>=20`, rational quota agreement, and leaf inactivity
through the horizon are kernel-checked. Bot-rise uses the live allocation;
the root index is `d`, and its initialized allocation is exactly `8192*8^d`.
The tree invariant now also includes `G<=sum(child G)` at every non-leaf; the
initial tree proves this, and the condition gives the exact allocation
subtraction needed by the executable recurrence. Scale8192 FlowDAG scans found
no reachable child-cover violation through depth100 (373,240 non-leaf states
checked at depth100); this is finite diagnostic evidence.
Lean proves root-deficit monotonicity for every recursive stage; child-cover
therefore persists at inactive and bot-rise nodes. The ordinary roles preserve
it as equality under the cut hypotheses, and top-desc does so under `G=0`.
The bot-rise parent native cap also follows from its children's native bounds
and child-cover. Ordinary-role native caps and reachable proofs of the branch
hypotheses remain open. A conditional full `d2FlowTreeInv` preservation theorem
for active ordinary nodes now composes recursive child invariants and explicit
parent/child native caps with the aggregate cut result. Its companion derives
front fit and those caps from the existing reserve lemma. A candidate-specific
bridge turns the normalized schedule-port inequality into the integer
quota-within-allocation premise. Proving this port bound and the sender/endpoint
reserves on reachable states remains open.
Prefix positions are proved contiguous; ordinary child cuts, top-desc clears,
and bot-rise child preservation reduce to the existing local update formulas.
The eight left/right cut lengths telescope exactly. Under balanced parent
endpoints, even quota, in-range fronts, and noncrossing fronts,
`d2FlowOrdinaryCut_conserves` proves the ordinary child deficits sum to
`G+pi`; `d2FlowStage_regular_child_mass` composes this with the recursive
stage for active top-rise, mid, and bottom-descending nodes. These are
conditional local results, not a reachable-state invariant proof.
Fresh review caught and fixed the
false unconditional `low+high=G` invariant at saturated nodes. The finite
depth100/scale8192 audit finds 100 saturated states where endpoint balance is
false, while all 482,411 non-saturated stored states and all active rows obey
it. The total Lean transition still needs conservation, quota parity, and valid
cuts proved on reachable states; there is no one-stage invariant-preservation
proof yet. This narrows the flow bridge but does not close its all-depth
induction. Details are in
[`D2-FLOW-STATE-SPEC.md`](../upper-bound/experiments/prefix-flux/D2-FLOW-STATE-SPEC.md).

## UB-28 thin-tail gate and cutoff repair (2026-10-24)

The 260/20 top-heavy rate screen's 150-random-round width-8 anchor has a
candidate subexponential failure path: mode transitions reach central
width-8 counts `(2,1,7,6)` for tested `log_n=16..96`, and the exact conditional
width-8-plus-tail failure probability is a fixed positive rational. A
per-transition mode-mass bound gives an `exp(-O(log^2 n))` prefix cost if the
profile stabilization is proved. This is not yet an all-depth no-go, but it
shows why the coarse grid-16 rate `0.8165` is unsafe as an upper-bound screen:
it omits thin count profiles. Details and reproduction are in
[`UB28-TOP-HEAVY-SCHEDULE.md`](../upper-bound/experiments/UB28-TOP-HEAVY-SCHEDULE.md)
and `ub28-thin-tail-path.py`.

A plausible repair is to use exact cyclic stages through a growing cutoff
`H=largest power of two <= (log_2 n)/2`, then use the 260/20 random schedule
above `H`. The exact tail costs `4H-2 <= 2 log_2 n`, giving modeled total
coefficient at most 282. This only prices the variant; the global exact-tail
transfer and an all-profile exponential-rate bound remain open. The D2
`V+E/2` route also remains blocked at the current relaxation: the depth-7
three-stage gate returned a feasible positive-drift witness, documented in
`prefix-flux/STATUS.md`.

## Route viability checkpoint (2026-10-24)

There is not yet a realistic end-to-end proof path below 300. The two priced
candidates are still conditional: UB-28 at about 282 (randomized top-heavy
prefix plus a growing exact tail), and D2 at 273 (fixed-height row sorts plus
a global rank/flow invariant). A direct zero-one exhaustive check confirms
that an exact tail stopped at `H < n/2` does not sort arbitrary inputs (for
example, a single one at wire 7 survives for `n=16,H=4`); it can only help
through a property of the prefix's delivered profile. UB-28 therefore still
needs a certified all-profile path-rate/terminal-transfer argument. D2 has
the stronger compositional routing idea, but its relaxed rank-transfer gates
admit alignment circulation or positive drift, and its viable ragged local
provider is not yet proved. UB-40's cost schedule is not an independent route:
its required refresh must contract a coupled global state, while the tested
one-snapshot alignment cap and fixed scalar potentials fail that gate.

A new exact integer D2 gate sharpens this: at depth 4, the full global-cut
MILP with an ideal local refresh has an integral `M_2` equality path and 2,691
terminal wrong keys. This is still a selected-cut relaxation, not a trace of
the fixed network, but it rules out strict contraction of this distance moment
from the present transition constraints alone. Reproduction and the solver
certificate are recorded in `prefix-flux/STATUS.md`. The same gate also has
an exact M3 equality path, so merely increasing the fixed moment order does
not resolve the selected-cut circulation.

The alternate aggregate-error interface has a larger exact local screen:
for one fixed four-column, 32-row two-scramble core, exhaustive enumeration of
all 1,185,921 height profiles found maximum summed defect 13, versus pointwise
caps summing to 598. This supports testing aggregate-plus-seam provider
budgets, but is far from the 8192-row, all-sender, weighted-tail theorem.

The strongest new cost point is a four-sort 4096-row core for the `(3,2,2)`
D2 flow: it prices at260, with40 coefficient left for cleanup. Three scramble-
sort rounds lowered the searched aggregate defect by roughly 11--14x versus
two rounds at 64 columns; the same trend persisted at 256 columns. The actual
depth-100 flow at this height has only about2.45 fringe rows, however, so the
current F2 provider does not apply. Details and reproduction are in
`prefix-flux/D2-FOUR-SORT-4096-CANDIDATE.md`.

The next decisive gate is a universal seam-weighted provider for this exact
four-sort core on the reachable 4096-row ragged sender profiles, including
fringe widths near2--3. If that gate passes, test its bounds in a phase-period
rank adversary with actual sender/receiver ports and within-bag defect; if the
provider needs more than the remaining40 coefficient, reject this cost point.
Until both gates pass, the sub-300 objective remains exploratory rather than a
realistic completed proof plan.

The cyclic 64-column core now has a deterministic local variance result: a
one-sided slope-profile DP for the last two cyclic rounds computes a final column
range bound `<=15`, hence `A_w/64<=28.125<48`, for every input profile. This
is a candidate width-64 `Gamma=48` provider without a random-core union bound,
but the finite DP is not Lean-checked. It is not
uniform in sender width: the same relaxation at 128 columns reaches range20,
though a direct full-core search finds only6 and is not a proof. The remaining
local question is an all-width provider or a priced finite-tile/seam scheme;
global alignment and terminal exact-count transfer remain independent gates.
The derivation and exact DP are in `prefix-flux/D2-FOUR-SORT-4096-CANDIDATE.md`
and `prefix-flux/d2_slope_profile_bound.py`.



## UB-40 scalar restoration versus fringe support (2026-10-24)

The Lemma 4.3' order-zero recurrence makes the periodic screen more precise. At the screened `(4,6,3)` point, with `T=1000` cheap stages, ten cheap steps raise the scalar outsider coefficient from `7.56e-6` to `6.43e-3`; four `q=24` precise steps return it to `5.31e-6`. Their modeled mean cost is `294.64`, before startup/terminal and provider costs. Reproduce with `upper-bound/experiments/sub500-screen/ub40_scalar_recurrence_gate.py`.

That scalar cycle is **incompatible with the current R1 Lemma 4.4 support condition**: the protected fringe can hold at most `delta_F*pi/(2c)=7.57e-6` outsider mass at this schedule (`delta_F=1/8`), about 850 times below the cheap-phase peak. Even taking `delta_F=1` leaves a 106-fold gap. More strongly, preserving the current support cap at each transition forces `epsilon_B<=4.58e-5`, hence bulk row exponent `q>=23` and about690 coefficient for the three-sort stage. Thus scalar periodic tolerance cannot meet300 while retaining the current support gate. UB-40 needs an invariant that separates short-range separator defect from the long-range outsider mass subject to fringe support, plus a bound on leakage between those components. The gate and derivation are in `upper-bound/experiments/sub500-screen/UB40-SCALAR-RESTORATION-GATE.md`.


The available n-uniform round-one margin-tail certificate was also tried at
the cheap q=9 height: even with margin W=m=512 it certifies only an upper
bound 4.04e-3 versus the 7.57e-6 support target. This fails to certify the
needed tail; it is not a lower bound on the true tail. The run is in
`upper-bound/experiments/sub500-screen/cert_tail_q9.out`; source was read-only
from branch `ub-34-fringe-duality`. A sharper full-stage tail bound is needed.


The D2 distance-tail period gate (`upper-bound/experiments/prefix-flux/D2-DISTANCE-TAIL-PERIOD-GATE.md`) imports UB-34's interval margin-tail method, with the five large-distance caps rerun for the actual 64-column domain. The corrected eight-point profile still permits exactly 6,390 terminal wrong keys in the depth-2 integer selected-cut relaxation (optimal, zero gap). The older depth-5 LP used stronger, `N_CERT=8192` tail caps and already admits positive drift, so that witness also survives the corrected weaker caps. UB-34's tail method is a useful local sharpening/diagnostic, but it does not close global rank transfer; the remaining gate is richer spatial port correlation or a stronger invariant.

The two-transition return-phase gate is also positive: the depth5 stage2->4 relaxation gives max drift +46,080 for `V+E/2` and +107,520 for `V+E`, even though the active level returns to level2. Thus tested fixed scalar weights fail to contract the full short period; a phase-dependent or richer spatial state is needed in this model.

To test phase-dependent level weights, the LP now allows distinct weights at the source and destination phases. One chosen pair makes phase2->3 contract by87.5, but swapping it back for phase3->4 gives +3.52 million drift. This pair fails as a cycle; longer phase-dependent states remain untested. The option and results are in `D2-DISTANCE-TAIL-PERIOD-GATE.md`.

The follow-up cutting-plane search jointly optimized normalized nonnegative
level weights for phases2,3,4. Six optimal depth5 selected-cut witnesses give
a strictly positive minimax lower bound `+1278.18` at `rho=0.99`, even when
weights may be zero. Thus this entire level-only linear potential family fails
for the tested 2->3->4 relaxation, not just the hand-picked weight pairs.
Witness residuals are at most `1.63e-5`; the saved cuts are in the ignored
`LLM-helpers/sub300-phase-weight-rho099-floor000001.json`. Further effort
should test a richer spatial state (e.g. explicit port correlations), rather
than continue tuning level-only weights. Details and the reproducible master
search are in `D2-DISTANCE-TAIL-PERIOD-GATE.md` and
`upper-bound/experiments/prefix-flux/optimize_phase_weights.py`.

Separating spine-bag and off-spine alignment with independent phase/level
weights also fails this relaxation: 24 witness cuts give a positive master
lower bound `+1248.62` at `rho=0.99`, even allowing zero weights; maximum
feasibility residual is `8.64e-5`. The optimized candidate reaches about
`+1274.44`. A rank-profile/port-flow state or stronger transition correlations
are now needed; more tuning of bag-total alignment weights is ruled out by
these finite gates. Saved cuts are in the ignored
`LLM-helpers/sub300-spine-phase-rho099-floor001.json`.

The longer-span LP construction itself is now a bottleneck: depth13/24-step and depth10/15-step models reached multi-GB memory, and depth8/9-step remained in construction after eight minutes. All were stopped without optimizer output and are inconclusive. A compressed phase/role state model is needed to test the 24-stage return map efficiently.

### Exact local D2 invariant gate (2026-10-24)

I checked the proposed sender-side premises directly in the interned exact
`(3,3,2)` D2 flow through depth100, including every distinct reachable active
state (not just the strong/weak `botDesc` slices). For ordinary positive-up
roles (`topRise`, `mid`, `botDesc`), all states satisfy
`G/c <= 1/512`, `pi/c <= 1/256`, and both endpoint-child deficits are at
least `c/128`. The exact maxima were `15/8192` for `G/c` and `15/4096` for
`pi/c`; the endpoint floor is tight at `botDesc`, `1/128`. There were zero
threshold failures. Reproduce with
`python upper-bound/experiments/prefix-flux/d2_local_invariant_audit.py --depth 100`.

This is stronger finite evidence for the local geometric bridge than the two
phase identity audit alone, and it removes an obvious startup/role counterexample
to those numerical premises. It is not an all-depth proof and does not address
the global rank recurrence, common-provider condition, or sorting. The next
paragraphs isolate the fixed-point transfer and its endpoint-reserve dependency.

The endpoint recurrence has an even sharper exact fixed point. Every ordinary
quota is `pi/c=15/4096`; if `G/c<=15/8192`, then for either end child
`G' = low + pi/2` and `c'=2c`, so
`G'/c' <= (15/8192)/2 + (15/4096)/4 = 15/8192`.
The scratch module now contains this as
`d2_ordinary_end_child_deficit_15over8192`. Its arithmetic was kernel-checked
in isolation with the same hypotheses; a direct check of the full 780 KB
scratch module was stopped after several minutes of unrelated elaboration, so
the module as a whole is not claimed checked in this pass. This tight fixed
point explains the finite depth-100 maximum exactly and is a better target for
the schedule induction than the slack `1/512` bound. It still only propagates
through ordinary endpoint cuts; it still needs a schedule-level proof that
the required two-stage endpoint reserves hold from startup through parent
overwrites.

The schedule handles that apparent `botRise` exception more cleanly than a
carried state: every active ordinary sender has an active parent one stage
earlier, and that parent is never `botRise`. A `topRise` sender's preceding
parent is `topDesc`, so its deficit is reset to zero. The existing Lean
schedule lemmas `active_parent_of_not_topDesc` and
`botRise_child_inactive_through_next` prove this exclusion, while
`active_regular_prev_two_role_cases` identifies the same-level predecessor
as ordinary or `botRise`. The abstract reserve transfer
`d2_scheduled_endpoint_reserve_persists` already handles the intervening
stage once the previous half-port is contained in the endpoint child. A finite
audit at depth1000 checked 373,250 ordinary senders and
confirmed that their preceding parent roles were only `topDesc`, `topRise`,
`mid`, or `botDesc`; reproduce with
`python upper-bound/experiments/prefix-flux/d2_schedule_parent_gate.py --depth 1000`.

This reduces the normalized deficit induction to propagating the parent cut:
topDesc gives zero; topRise starts with zero parent deficit and its `1/256`
quota yields at most `1/1024` of child capacity; mid/botDesc use the fixed
point `B/2+(15/4096)/4=B`, `B=15/8192`. The remaining coupling is geometric:
one must first prove the parent's fronts stay in the end children, using the
two-stage endpoint reserves. Thus the sender-deficit cap is no longer the
main standalone obstacle, but its all-depth proof still depends on closing
the endpoint-reserve induction; neither result addresses the global rank
recurrence.

The exact port-rank profile was added to the phase-weight search as a richer
potential `V + beta*P`. At `beta=1/8`, the two-iteration witness-cut master
still has a negative lower bound (`-225,747`), so contraction is unresolved.
At `beta=1/2`, its lower bound is positive (`+382,121`) with maximum accepted
primal residual `9.16e-6`, ruling out all tested phase/level spine/off-spine
linear weights for that fixed coefficient in the finite selected-cut model.
These gates do not concern traces of the fixed network. Further scalar tuning
of this profile is not promising; the live gap is a richer reachable-state
transition bound. Full setup and caveats are in
`upper-bound/experiments/prefix-flux/D2-DISTANCE-TAIL-PERIOD-GATE.md`.

The second-distance moment is now tested with a monotone sparse-cut enclosure;
its gap bounds pass exhaustive small-word checks and match the exact objective
when all cuts are retained. At depth5, the target 8192-row model gives
negative `rho=0.9` drift in all four root-initialized transitions, and the
arbitrary-source depth5 gates are negative at `rho=0.99`. Those constants do
not persist: at depth7 the arbitrary-source one-step LP has optimal positive
`rho=0.99` drift in phases3 and4, and phase5 also has a positive optimum. The
depth7 four-stage return gate is numerically unresolved, with a feasible
near-neutral candidate. Thus no all-depth potential recurrence is established;
the full tests and limitations are in
[D2-DISTANCE-TAIL-PERIOD-GATE.md](../upper-bound/experiments/prefix-flux/D2-DISTANCE-TAIL-PERIOD-GATE.md).

### Exact phase/shell quotient of the D2 flow skeleton

`d2_phase_shell_compression.py` now propagates classes from each stage root
without enumerating every address. A class is determined by the interned full
flow node state and the address's threshold-spine split shell (first differing
base-8 digit, side, and digit offset). This is an exact quotient of the
**deterministic flow skeleton**: every child class is obtained from the
representative node's actual child ID, and multiplicities account for every
static address. At depth8 it reduces 210,913,571 address-stage occurrences to
4,033 state/shell classes (52,297x). Reproduce with
`python upper-bound/experiments/prefix-flux/d2_phase_shell_compression.py --depths 8 --suffix-digits 4`;
the reported `state_shell_classes` is the stronger quotient count.

The simpler rule �shell plus a fixed number of trailing address digits� is not
uniform: two digits first fail at depth7, level4; three fail at depth8, level5.
The exact state/shell quotient remains small, but it does not yet compress
separator output profiles. Before using one aggregate profile per class, prove
that the local provider constraints and the rank-potential objective descend
to this quotient; otherwise aggregation could lose reachable adversaries or
underestimate the drift. The next gate is a quotient LP with independent
per-sender outputs represented by summed identical local polytopes, and a
comparison against the uncompressed LP on a small case.

The rank-history prerequisite was tested with `--check-history` at depths5 and6,
row height8192. The raw state/shell partition has15 groups whose interval
history varies; adding each bag's exact nearest occupied-wire distance to the
threshold yields1,199 and1,414 groups, respectively, with a unique history
interval in every class. A logarithmic distance bin did not have this property
at depth5. This exact-margin partition still is not transition-closed: at
depth5 two groups at stage3/level2 have identical current labels but split
into different child-history vectors. The quotient LP therefore needs a
joint child-port/history state, or a conservative aggregate of those vectors;
current-state compression alone is insufficient.

The compressed local recurrence state was then expanded to a radius-one star:
for each bag, record its own `(flow state, shell, H-interval)`, its parent label
and child digit, and the eight child labels. At depths5/6, every repeated star
has exactly the same next flow-state/history label: zero transition mismatches
among4,084 and5,260 distinct stars, with at most1,488/1,512 stars at any
single stage/level. This is finite exact evidence that a local neighborhood
state captures the scalar interval update on these schedules. It still omits
separator output-profile variables and is not an all-depth closure proof. The
reusable check is `d2_phase_shell_compression.py --check-history`.

The phase/shell equitable port-flow quotient was compared directly with the
uncompressed LP at `depth=5, scale=8, row_count=8`, with no ordered-prefix or
distance-tail constraints. Both solve optimally to `19,883` terminal wrong
keys. The quotient uses 3,359 variables versus 3,807 raw (2,477 classes for
2,925 vertices), only an 11.8% variable reduction. At depth3 the partition is
the identity. This validates objective preservation on the toy case but shows
that the current exact-state quotient alone does not deliver the hoped-for
scaling; a more aggressive phase/shell/star aggregation would need a proof
that it preserves local feasible transitions and the terminal objective.
Reproduce with
`python upper-bound/experiments/prefix-flux/d2_port_quotient_lp.py --depth 5 --scale 8 --row-count 8 --time-limit 60 --params 3 3 2 --sorted-root --compare-raw`.

### Reuse audit: UB-34 fringe-duality branch (2026-10-27)

UB-34 is useful as a source of probabilistic proof techniques, but its current
result does not plug into the sub-300 D2 proof. Its route-(d) energy/collision
argument bounds fringe escapes for fixed source sets under the UB-34 two-round
separator. The D2 recurrence instead needs a uniform all-j rank-prefix
position-escape profile for the actual scheduled local provider, then a
transfer of that profile into a spatial rank/alignment potential. These are
different observables and different network contracts; the UB-34 numeric
fringe certificate cannot be substituted for the missing D2 provider or
global recurrence.

The potentially reusable pieces are the n-uniform collision estimate,
fixed-set MGF/negative-association lemmas, and the level-crossing composition
pattern. Reuse would require first proving a new bridge from those lemmas to
the D2 provider's rank-prefix escape counts, uniformly over every active
sender and every j; the current UB-34 notes explicitly leave some of their
own asymptotic/certification steps open as well. Therefore the high-value next
gate remains a structural arbitrary-depth D2 transition theorem (or a
counterexample to the candidate invariant), not porting the UB-34 fringe
constant. This audit is a research assessment, not a theorem or a proof
milestone.


### Correction: UB-34 band-repair lemma is a direct structural lead (2026-10-27)

The earlier reuse audit was incomplete: besides route-(d) probability tools,
the UB-34 branch has a deterministic band-repair lemma in
`upper-bound/best/AKS/Sub800/MergeBandPack.lean`, notably
`bandStage_rowCount_le` and `mergeBandPack2Net_low_crossings_le`. The D2
worktree's `D2Slope25MarginTail.lean` proves a fixed-core variance bound that
implies every output-column height is within52 rows of its mean. If this
profile is the one immediately before a row-preserving scramble, the band
lemma with radius28 gives zero crossings from rank-distance at least80 at an
aligned cut (with a small rounding charge for nonaligned cuts). This is a
deterministic way to replace the missing probabilistic far-tail provider.

The screened implementation would sort three 4096-row columns (234 layers),
then sort 56- or 64-row repair bands in parallel (21 layers), and optionally
retain a 21-layer sparse-edge repair. Its modeled coefficients are 212.5 or
230, respectively, using the current 5/6 stage/log rate. Both are below300,
but they are conditional cost calculations, not a sorter proof. The UB-34
lemma is written for its Sub800 matrix-network model and is absent from this
branch's current source base, so a model adapter or a separately proved D2
version is required. The variance bound must be shown to apply at the correct
point in the full stage; the cut bands must be realized by actual addresses
and be disjoint at every active sender; and the resulting bounded-distance
errors must be propagated through the full schedule to a terminal cleanup
whose depth is sublinear in log n.

This is currently the strongest concrete below-300 lead found in the UB-34
material: it reuses a deterministic structural lemma, not the branch's
unfinished fringe certificate. The next gate is to specify and prove one full
D2 macro-stage (including the physical band network) with its exact crossing
contract, then derive the all-depth rank-displacement/terminal-cleanup lemma.
Until that global lemma is established, the 212.5/230 coefficients remain
models only.

### Arbitrary-root port quotient correction (2026-10-28)

The D2 local-profile quotient gate previously fixed the root to a sorted
threshold profile. Its arbitrary-root mode now keeps only the exact root mass
and permits local root prefixes throughout the modeled margin-tail bounds;
transfer of those caps to the actual D2 core remains unproved. With the
width-64 distance-tail caps, the depth-5 quotient remains optimal and feasible
but leaves 4.377M summed terminal wrong mass (versus 5.859M without tails);
equality/inequality residuals are below `2.2e-9`. This rules out the current
independent local-tail constraints as a sufficient global alignment invariant
in this relaxation, not the fixed D2 network. The run and caveats are in
`prefix-flux/D2-DISTANCE-TAIL-PERIOD-GATE.md`. The next proof-relevant
strengthening must encode actual shared core output profiles or schedule
reachability correlations; retuning tail caps alone is not supported by this
gate.


### Proof-priority correction (2026-10-31)

The prefix-flux source already proves the schedule-wide statements
`d2FlowCandidateRun_alignment_all` and
`d2FlowCandidateRun_frontContract_all` in `D2CutAlignment.lean`; these give
all-stage tile alignment and the recursive endpoint-front congruences for the
actual candidate run. The separate finite depth/time-shift screens are not a
necessary route to those facts and should not be extended as a substitute for
the remaining proof. The missing run-level provider is stronger:
`d2FlowStageInvInputs` (or its tolerant version) requires a quantitative
per-sender deficit cap, quota/allocation feasibility, and both endpoint
reserves at every active sender. Existing `D2Stage19/20PreservesInv.lean`
prove only individual startup transitions; `D2AllStageInvariant.lean` shows
that a universal provider would immediately lift to every run stage. After
that invariant, the global spatial rank-profile recurrence and terminal
sorting criterion remain separate obligations.

The UB-34 checkout on branch `ub-34-fringe-duality` now contains checked
network-level band-crossing lemmas (`mergeBandPack2Net_low_crossings_le` and
`mergeBandPack2Net_escapes_le`), including the previously omitted band-stage
escape term. These strengthen the local separator analysis but do not close
the D2 run provider or global spatial recurrence, and the route's current
costing is not a sub-300 proof. Treat them as reusable local mathematics, not
as a replacement global construction.


### Affine sender-profile gate refresh (2026-10-31)

A fresh exact-integer FlowDAG diagnostic at `d=110`, scale `8192`, checked
273,700 active ordinary senders across 994,746 interned states. All passed the
affine profile `8192*G + 7 <= 15*cap` and `4096*quota <= 15*cap`; special
roles balanced, and every `topDesc` root was zero. Worst deficit/cap was
`4533471823554859405148153 / 2475880078570760549798248448` (about
`0.0018307`), below `15/8192`; minimum endpoint reserve ratio was exactly 1.
Reproduce with `python upper-bound/experiments/prefix-flux/d2_reachable_reserve_audit.py --depth 110 --scale 8192 --require-affine`. This is finite evidence only.

The matching formal interface already exists in `D2StrongFlowStage.lean`:
`d2FlowStageAffineInputs` is sufficient for one-stage reserve-invariant
preservation, and `d2FlowCandidateRun_preserves_inv_of_affine_all_inputs`
lifts it over any finite run horizon. The unresolved theorem is therefore a
schedule-parametric provider of those affine sender inputs for every actual
stage, including the exact reserve and allocation conditions. Do not spend more
time extending finite stage bridges unless they establish a reusable induction
step for that provider. Even after it, physical rank-profile transfer, global
inversion contraction, terminal sorting, and the coefficient accounting remain
open.


### Affine input contract reduction (2026-10-31)

Added `D2StrongFlowNoAlloc.lean` and checked it with Lean. Its recursive
`d2FlowStageAffineInputsNoAlloc` contract omits `quota <= totalChildDeficit - G`
from each active ordinary sender. `d2FlowStageAffineInputs_of_noAlloc` recovers
that condition from the existing deficit/quota caps and the left endpoint
reserve; the corresponding all-horizon theorem then reuses the checked
affine stage-preservation lift. The all-stage provider is now reduced to
balance/role cases, affine deficit control, even quota, and endpoint reserves
(recursive children follow by the definition). This is an interface reduction,
not a provider: the actual uniform deficit and reserve estimates remain open,
as do physical rank transfer, global inversion contraction, terminal sorting,
and the coefficient proof.


### Tree-core provider interface (2026-10-31)

`D2StrongFlowCoreInputs.lean` is now kernel-checked. It removes the schedule-
determined quota bounds and parity from the missing positive-stage provider.
For every positive stage, the actual tree's recursive balance, top-rise/top-
descending root conditions, affine mid/bot-descending deficit envelope, and
endpoint reserves suffice: `d2FlowCandidateStageAffineCoreInputs_to_noAlloc`
reconstructs quota and parity fields from the closed-form schedule. The stage-0
reset is proved separately. `d2FlowCandidateRun_preserves_inv_of_core_provider`
then lifts any positive-stage core provider to the reserve invariant at every
run horizon. Thus the unresolved provider is sharply focused on actual tree
balance/role states, affine deficit control, and endpoint reserves. This still
does not prove that provider or the later rank-profile, sorting, and
depth-accounting obligations.


### Actual-run two-visit endpoint transport (2026-10-31)

`D2RunTwoVisitReserve.lean` is kernel-checked. The theorem
`d2FlowCandidateRun_path_endpoint_reserve_of_prior_sender` now transports the
local two-stage ordinary endpoint-reserve estimate to an arbitrary path in the
actual full candidate run. It explicitly models ancestor root overwrites and
uses only the schedule fact that the sender is inactive at the intervening
stage. Thus, for a sender with ordinary inputs at its prior visit `t-2`, both
endpoint reserves persist at its current visit `t`. This closes the path-history
bridge previously missing from the proposed per-sender time induction. It does
not establish the prior sender inputs, the exceptional bot-rise predecessor
case, or the affine deficit recurrence from the parent level.

### Affine child-profile scale adapter (2026-10-31)

`upper-bound/experiments/prefix-flux/D2StrongAffineChild.lean` is kernel-checked. It packages the local ordinary update as `d2_regular_update_preserves_child_affine_profile`: the parent's sharp affine profile gives every child `8192*G_child + 7 <= 30*c`. `d2_parent_affine_profile_to_child_capacity` rewrites this using the candidate's next-level capacity `2*c`, giving the child's `15*capacity` profile. This closes only the local arithmetic/scale adapter. Still required: lift the parent update through arbitrary paths in the actual run, handle startup and bot-rise, and combine with reserves into the all-stage core provider; global rank transfer, terminal sorting, and depth accounting remain open.
### Arbitrary-path affine child transport (2026-10-31)

Extended `D2StrongAffineChild.lean` with a kernel-checked history-level
one-step theorem and `d2FlowCandidateRun_path_parent_affine_child`. The latter
transports a parent sender's affine profile through its actual update to every
child on an arbitrary path in the full D2 candidate run; the path-history
context includes all ancestor root overwrites. Using the candidate's capacity
identity for child stage `t+1`, the child receives exactly the required
`15*capacity` affine profile. This closes the path-projection gap for the
regular-parent profile recurrence. It does not provide the parent local inputs
for every stage, and top-descending/startup and bottom-rise parent cases still
need to be composed with this ordinary step; the all-stage invariant, rank
transfer, terminal sorting and depth accounting remain open.
### Actual candidate arbitrary-path affine step (2026-10-31)

The checked `d2FlowCandidateRun_path_parent_affine_child` theorem in
`D2StrongAffineChild.lean` now composes that local update with
`d2FlowCandidateRun_path_as_history` and the path-context API. For any path
selecting an active ordinary parent in the actual candidate run, if the node at
that snapshot meets the affine sender contract, every child in the next
snapshot has the affine profile at its next-stage capacity. The proof accounts
for arbitrary ancestor overwrites. The capacity-doubling equality is an
explicit premise of this interface. The substantive unsolved part is now to
supply the per-sender contract for all stages, including startup and exceptional
roles, and then close the global rank/profile and terminal-sort arguments.
### Core-contract path extraction (2026-10-31)

Added and kernel-checked `d2FlowStageAffineCoreInputs_atPath` and
`d2FlowCandidateRun_core_provider_noAlloc_atPath` in
`D2StrongFlowCoreInputs.lean`, plus the generic recursive extraction lemma
`d2FlowStageAffineInputsNoAlloc_atPath` in `D2StrongFlowNoAlloc.lean`. Thus a
positive-stage full-tree core provider can now be restricted directly to the
actual sender subtree at any path, preserving its schedule level and all local
fields after the core-to-no-allocation adapter. This packages the hypotheses
needed by the newly checked actual-path affine child theorem. It still assumes
the all-stage core provider; proving that provider uniformly is the dominant
open D2-flow obligation.
### Checked Lean artifacts for affine path interface (2026-10-31)

The updated `D2StrongFlowNoAlloc.lean` and `D2StrongFlowCoreInputs.lean`
compile to kernel-checked oleans. The latter now includes
`d2FlowCandidateRun_core_provider_noAlloc_atPath`: any positive-stage full-tree
core provider restricts to the exact no-allocation affine contract on any
selected sender subtree. `D2StrongAffineChild.lean` also compiles to an olean
with the local and actual-run affine child transport results. This improves
composition of the provider interface, but does not prove the provider itself.
### Full local sender contract at arbitrary paths (2026-10-31)

Added and kernel-checked `d2FlowCandidateRun_core_provider_affine_atPath` in
`D2StrongFlowCoreInputs.lean`. Given the proposed positive-stage core provider,
it returns the full affine sender contract on any actual subtree path, including
quota parity and the quota-versus-allocation inequality recovered from the
endpoint reserve. This is the precise local input expected by the stage
preservation and child-profile lemmas. The missing theorem remains the
schedule-wide core provider itself.
### Core-provider ordinary endpoint reserve transition (2026-10-31)

`D2CoreProviderReserveStep.lean` now kernel-checks
`d2FlowCandidateRun_core_provider_endpoint_reserve_step`. Assuming the affine
core provider at the ordinary sender's prior visit `t-2`, it extracts the full
local sender contract at that path, derives child cover from the affine deficit
cap plus the left reserve, applies the schedule quota floor and two-stage
capacity ratio, then invokes the actual-path two-visit theorem. The result is
both endpoint reserves at the sender's current visit in the full run. This
closes the ordinary-predecessor branch of the reserve recurrence under the
core provider. The separate `botRise` predecessor/startup cases and the
schedule-wide core provider itself remain open.
The checked ordinary-reserve module also compiles to an olean. Its hypotheses
are intentionally split at the predecessor role: the theorem proves only the
ordinary `topRise`/`mid`/`botDesc` branch. The remaining schedule branch is a
`botRise` two-stage native-child argument, with startup handled separately; it
must be composed before claiming the recursive core contract is inductive.
### Complete two-visit endpoint reserve split (2026-10-31)

Extended `D2CoreProviderReserveStep.lean` with a checked `botRise` predecessor
case and a combined `d2FlowCandidateRun_core_provider_endpoint_reserve_step_all_roles`
interface. The ordinary branch uses the assumed affine core provider at `t-2`;
the exceptional branch uses the existing callback-window theorem to preserve
both native endpoint child roots up to the current visit. The current capacity
is exactly 128 times that native size, so both endpoint reserves follow. The
module compiled directly with Lean to `D2CoreProviderReserveStep.olean`.
This closes the role split for the *conditional reserve transition*, not the
schedule-wide core-provider induction. Startup, construction of that provider,
global rank/inversion contraction, terminal sorting, and coefficient
accounting remain outstanding; no improved limsup bound is proved.The combined theorem derives the predecessor-role split from the current active
regular role via `active_regular_prev_two_role_cases`; callers do not need to
supply a separate prior-role classification. Its remaining non-schedule premise
is the proposed core-provider contract at the prior snapshot.
### Tree-wide local transitions from a proposed core provider (2026-10-31)

`D2CoreProviderReserveStep.lean` now has two additional checked adapters.
`d2FlowCandidateRun_core_provider_endpoint_reserves_at_active_path` derives
the prior-role split from the schedule and lifts the conditional reserve step
to any active regular sender path, assuming the full-tree core provider at
`t-2`. `d2FlowCandidateRun_core_provider_affine_child_at_active_parent`
projects the full-tree core provider at `t` to an actual active ordinary
parent, extracts its sharp profile/allocation/reserve fields, and applies the
arbitrary-path update plus the schedule capacity-doubling identity to obtain
the next child profile. `d2FlowStageAffineInputs_ordinary_fields` now also
returns the sharp profile-cap disjunction, needed for this composition.
Both files compiled directly with Lean to oleans.

These do not yet close an all-stage induction. They cover the case where a
node's profile at the next time is written by an active ordinary parent. The
remaining source cases—parent inactive, top-descending reset, and bottom-rise
preservation—must be unified with the temporal state of that child; top-rise
zero deficit also needs its own schedule/history argument. Thus the core
provider is still unproved, and the global rank-profile contraction, terminal
sorting, and total-depth coefficient are still open.
### Top-rise parent schedule identity (2026-10-31)

Added and kernel-checked `d2ScheduleRole_parent_of_active_topRise` in
`D2CoreProviderReserveStep.lean`: an active top-rise sender at `(i,t)` has a
parent at `(i-1,t-1)`, and the exact parity-rounded frontier inequalities force
that parent to be `topDesc`. This identifies the source of the required zero
root: the previous-stage parent update resets the child root. The remaining
work for this case is an arbitrary-path actual-run lemma transporting that
reset to the queried sender snapshot. The schedule identity and the ordinary
child-profile and two-visit reserve transitions are checked; the all-role,
all-stage core provider is still not established.
### Arbitrary-path top-rise zero-root closure (2026-10-31)

The remaining top-rise reset bridge is now proved. In
`D2CoreProviderReserveStep.lean`,
`d2FlowTreeRunWithParentOverwrites_topDesc_child_zero` shows a top-descending
parent history sets the selected child root to zero on the next step;
`d2FlowCandidateRun_topDesc_parent_child_zero_at_path` transports this through
any path in the actual candidate run, including all ancestor overwrites.
`d2ScheduleRole_parent_of_active_topRise` then identifies the previous-stage
parent of an active top-rise sender as top-descending, and
`d2FlowCandidateRun_active_topRise_root_zero_at_any_parent_path` composes the
schedule fact with the actual-run reset. It kernel-compiles to the module olean.
This closes the top-rise zero-root subcase of the core contract after startup.
It does not close topDesc-active nodes, ordinary affine profiles beyond the
active-parent transition, the recursive all-time core provider, or the later
sorting and coefficient proof.
### Profile sourcing for every active non-top-descending child (2026-10-31)

Added the checked theorem
`d2FlowCandidateRun_core_provider_affine_profile_at_active_nonTopDesc_child`.
From a full-tree core provider at parent stage `t`, every active child at `t+1`
whose role is not top-descending gets its affine deficit profile: the schedule
ensures its parent was active at `t` and not bot-rise; an ordinary parent uses
the arbitrary-path affine child transition, while a top-descending parent uses
the just-proved reset. This includes the top-rise schedule region's zero-root
source (also separately stated as `d2FlowCandidateRun_active_topRise_root_zero_at_any_parent_path`).
Thus the remaining role-specific profile gap is narrowed to active
 top-descending children themselves, plus the general startup/all-stage
provider induction. The module compiled directly with Lean.
### Current `topDesc` root-profile gap (2026-10-31)

The missing active-`topDesc` profile case appears to have a bounded two-stage source, rather than requiring a long backward search. An exhaustive schedule audit for dimensions `7..999` found that every active `topDesc` sender at stage `t >= 4` is active at the same level at `t-2`, with role `topDesc` or `topRise`; it is inactive at `t-1`. The `t-2` role has zero root deficit under the core contract, and its own update outputs zero. At the intervening stage, either the parent is inactive and the sender retains zero, or the parent is active `topDesc` and the already checked parent-reset theorem writes zero again. Startup/root-level cases need to be stated separately. This audit is evidence only, not a Lean proof.

The next formal interface should split on the parent action at `t-1`: (a) active `topDesc`, discharged by `d2FlowCandidateRun_topDesc_parent_child_zero_at_path`; (b) inactive, discharged by a two-stage path-history projection plus the `t-2` `topDesc`/`topRise` zero-root contract. The schedule lemmas needed are: current active `topDesc` implies same-level active at `t-2` with role in `{topDesc, topRise}`, and the parent at `t-1` is either inactive or `topDesc`. Do not infer these from the earlier failed claim that the immediate previous-stage parent is always active; it is false.
### Correction: exact active top-descending history (2026-10-31)

The previous paragraph's audit claim that every active top-descending sender was itself `topDesc` or `topRise` two stages earlier was false. Counterexample: `d=7, i=2, t=6`; the sender at `t-2=4` is `botDesc`. This is a reset case: the parent at `i-1` is active `topDesc` at `t-1`, so the existing `d2FlowCandidateRun_topDesc_parent_child_zero_at_path` applies. The authoritative schedule theorem `alpha_topDesc_two_step_patterns` gives the complete split: (1) same-level `topDesc` at `t-2`, with frontier at `i+1` at `t-1`; (2) same-level `topRise` at `t-2`, with frontier at `i-1` at `t-1`; or (3) frontier at `i-2` then `i-1`. In cases (2) and (3), the level `i-1` parent is top-descending at `t-1` and should reset the queried root. Case (1) is the only one requiring propagation from the prior same-level zero-root state through the intervening inactive stage.

Added `D2TopDescHistory.lean`; `active_topDesc_two_stage_frontier_cases` packages the existing frontier split for an active top-descending sender and kernel-compiles. This replaces the earlier audit-based proposed interface. Remaining formal work: derive the parent-active/topDesc schedule fact in cases (2)/(3), then prove case (1)'s two-stage path-history zero-root transport. The exhaustive Python audit was diagnostic only.
### Checked closure of the repeated-frontier `topDesc` source (2026-10-31)

`D2TopDescHistory.lean` now kernel-checks three reusable pieces. First, `d2FlowStage_path_eq_of_inactive_prefix` proves that a recursive stage projects to the same local stage whenever every ancestor on the selected path is inactive. Second, `active_topDesc_has_two_stage_reset_source` packages the exact frontier split: an active top-descending sender either has an active top-descending parent at stage `t-1`, or is itself active top-descending at `t-2`. The parent activity and role in the latter frontier cases are formal, using a new one-step bound on `omega`.

Third, `d2FlowCandidateRun_priorTopDesc_root_zero_after_inactive_stage` transports the latter source through the actual run at arbitrary path depth. It assumes the all-level affine core contract at snapshot `t-2`; under that contract the node's root deficit is zero, its top-descending update retains zero, and the inactive next stage retains zero. It uses the inactive-ancestor projection theorem, so this is now a checked actual-run result rather than a schedule-only simulation.

The remaining top-descending integration is the other source branch: connect the active parent-reset theorem to a path's final edge (the current path API is prefix-oriented). After that, this role's zero-root profile can be fed into the all-stage core-provider induction. Neither that induction nor the downstream sorting/depth/coefficient proof is closed.

### Top-descending child root interface (2026-10-31)

`D2TopDescHistory.lean` now proves `d2FlowCandidateRun_priorTopDesc_child_root_zero`: if a child is active `topDesc` at snapshot `t-1`, has zero root under the affine core contract there, and the two following parent updates are inactive, then that child root remains zero at snapshot `t+1`. The proof projects the full run through the inactive ancestor prefix and handles the child's local two-stage update.

The new theorem `d2FlowCandidateRun_active_topDesc_child_root_zero_of_prior_core` composes this with the exact schedule split. An active `topDesc` child at `t+1` has either an active `topDesc` parent at `t` (direct reset through the arbitrary-path overwrite theorem) or the repeated-frontier source at `t-1` (the new two-stage child lemma). In the latter case, the affine core at `t-1` supplies the source zero. The module compiles with Lean. This closes the active-`topDesc` child zero-root interface under a prior core hypothesis; it does **not** establish the all-stage core invariant. The next formal target is a recursive one-step provider theorem that constructs the complete affine core at snapshot `t+1` from the required prior core snapshots, including startup. The global rank/inversion contraction and final sorting-depth accounting remain separate, major proof obligations.
