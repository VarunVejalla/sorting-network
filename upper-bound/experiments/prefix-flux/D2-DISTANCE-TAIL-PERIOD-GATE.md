# D2 8192-row distance-tail period gate (2026-10-24)

**Status: finite selected-cut adversarial screen, not a sorting proof.** This
combines an interval-certified margin-tail profile with the coupled rank LP.
The profile is derived from `cert_walk_n.py` on the read-only
`ub-34-fringe-duality` checkout, using `N_CERT=8192`, exact `m=8192`,
`NCELL_M=1`, and `PCELL_RATIO=1.1`. The reproduced output fragments are in
`LLM-helpers/sub300-check/artifacts/sub300-structural/upper-bound/experiments/sub500-screen/cert_tail_m8192_W*.out`
in this machine's ignored artifact cache (original paths and hashes are in its
`MANIFEST.tsv`). Rounded-up caps used below are
conservative relative to the printed interval upper bounds:

| margin rows r | certified T(r) cap used | printed interval upper bound |
|---:|---:|---:|
| 64 | 103/10000 | existing `PROFILE-GATE.md` certificate |
| 128 | 78/10000 | existing `PROFILE-GATE.md` certificate |
| 256 | 47/10000 | existing `PROFILE-GATE.md` certificate |
| 512 | 151/100000 | 1.50552e-3 |
| 1024 | 319/500000 | 6.37735e-4 |
| 2048 | 31/100000 | 3.09994e-4 |
| 4096 | 7/40000 | 1.74187e-4 |
| 8192 | 117/1000000 | 1.16035e-4 |

The first three caps are the prior certified values; the latter five were
rerun at `N_CERT=8192`. The LP uses a monotone step profile: each cap applies
from its listed margin to the next larger listed margin.

## Candidate-scale shallow checks

At `depth=2`, `scale=8192`, `row_bits=13`, `(x,y,z)=(3,3,2)`, ordered global
prefixes, root-tail initialization, 64-row sampled cuts, and integral count
variables, the eight-point profile yields an optimal MILP solution with
6,390 terminal wrong keys (largest block: 2,082). The older six-point profile
also allowed 6,390, so the stronger large-margin values did not improve this
terminal objective. The model remains a selected-cut relaxation, not a fixed
network trace.

For the same depth-2 instance, maximizing one-step drift at stage 1 with
`V + E/8` gives an optimal maximum drift of `-75` (counts integral; zero MIP
gap). Here `V` is the level-weighted cross-bag alignment with level ratio
`1/4`, and `E` is within-bag threshold defect. This is a local positive
signal only. `V` alone still admits drift `+48.5` in that transition.

## Longer-period check

At `depth=5` (four transitions), the continuous selected-cut model with the
same eight-point profile and a one-step drift objective from phase 2 is
optimal, but both tested fixed weights fail badly:

- `V + E/8`: maximum drift `+190,438.425`.
- `V + E/2`: maximum drift `+190,385.464`.

The LP has 12,401 variables and an exact solver optimum; the represented count
profile is continuous and cuts are sampled every 64 rows. Positive drift is
therefore a counterexample to these particular potential inequalities in this
relaxation, not a concrete sorting-network counterexample. The matched
depth-4 integral solve hit its time limit without a primal point and is
inconclusive.

**Reading:** certified distance grading does not by itself close the D2
recurrence. It improves some shallow constraints and permits a `V+E/8`
contraction on one small transition, but a longer phase window routes
alignment into a different level and defeats both fixed weights. The next
structural gate is a phase-dependent alignment potential (or exact port
correlations strong enough to prevent this level-to-level circulation), tested
against this same certified profile before adding more Lean bridge lemmas.

Reproduce the terminal and drift gates with `coupled_rank_lp.py` using the
commands recorded in `docs/sub300-search.md` and the profile above.


The five target-check logs `cert_tail_m8192_W*_target.out` rerun
each interval computation against the rounded-up cap listed in the table and
all return `CERTIFIED`. For each W, the command was
`python -I cert_walk_n.py tail 8192 8192 W numerator denominator` with
`N_CERT=8192`, `NCELL_M=1`, `PCELL_RATIO=1.1`; the numerator/denominator is
the corresponding profile cap above. The exact source path was
`<root checkout>/upper-bound/experiments/sub500-screen/cert_walk_n.py` on
branch `ub-34-fringe-duality`.

## Width-64 domain correction and rerun (2026-10-26)

The preceding table's five large-margin bounds used `N_CERT=8192`; they do
not establish the same caps for D2's 64-column sender. I reran the interval
certifier from `ub-34-fringe-duality` at `N_CERT=64`, exact `m=8192`,
`NCELL_M=1`, `PCELL_RATIO=1.1`. The certified upper bounds are:

| margin rows r | width-64 tail upper bound | rounded-up cap used |
|---:|---:|---:|
| 512 | 1.83898e-3 | 185/100000 |
| 1024 | 8.62839e-4 | 863/1000000 |
| 2048 | 4.51592e-4 | 452/1000000 |
| 4096 | 2.63192e-4 | 264/1000000 |
| 8192 | 1.77016e-4 | 178/1000000 |

Each rounded-up cap independently reruns as `CERTIFIED` at `N_CERT=64`.
The existing 64, 128, and 256 caps are from the broader-domain certificates.
Using this corrected eight-point profile in the depth-2, scale-8192 integral
selected-cut gate still gives the optimal terminal wrong mass 6,390 (1,081
variables; 605 equalities; 2,709 inequalities; zero equality residual and
1.5e-8 maximum inequality residual). Thus the corrected far-distance tail
profile remains valid local input but does not improve this global terminal
relaxation. It does not rule out value in a richer spatial state or in a
tighter transition model.

**Matched no-profile baseline (2026-10-26).** Re-ran the same command and
MILP settings with `--distance-tail-profile` omitted. HiGHS again proved an
integral optimum, now with 8,980 terminal wrong keys (maximum single block:
2,898; 1,081 variables; 605 equalities; 2,529 inequalities). With the
corrected width-64 profile, the optimum is 6,390 (maximum single block:
1,960; 1,081 variables; 605 equalities; 2,709 inequalities; maximum
inequality residual `1.49e-8`; zero integrality error to displayed
precision). So the certified margin profile cuts this relaxation's optimum
by 2,590 keys, about 28.8%, but does not force terminal purity. This is a
useful quantitative gain from UB-34's tail machinery, while the remaining
6,390-key witness still shows that local distance tails alone do not control
global port alignment. Both optima are selected-cut model witnesses, not
traces of the fixed D2 comparator network.

Reproduce the baseline by running the preceding shallow command without its
`--distance-tail-profile` option. The profiled command is exactly the one
shown there; its printed reduced fractions are the caps used by the model.

**Column-profile shape test (2026-10-26).** Adding
`--all-row-dominance --column-profile-monotone` to the corrected-profile
gate gives an optimal continuous objective of 6,021.9232 terminal wrong
keys (63 impure blocks; 8,441 variables; 2,461 equalities; 27,743
inequalities; maximum inequality residual `4.66e-10`). The matched
continuous run with all-row dominance and the same tail profile, but without
column-profile monotonicity, gives 6,390.0192. Thus sampled occupancy
monotonicity contributes only about a 5.8% further reduction. The integer
version with the shape constraint timed out without a primal solution, so
there is no integral comparison. The tested shape condition is useful but
does not explain away the residual global alignment.

The earlier depth-5 positive-drift witness used the stronger `N_CERT=8192`
caps from the preceding table. Since every corrected width-64 cap above is
weaker at margins 512 and larger, that same witness remains feasible under
the corrected profile; the long-window noncontraction finding therefore
survives this domain correction.

For reproducibility, use this shared profile argument in the LP commands:

```text
--distance-tail-profile 64=103/10000,128=78/10000,256=47/10000,512=185/100000,1024=863/1000000,2048=452/1000000,4096=264/1000000,8192=178/1000000
```

The shallow terminal MILP adds `--depth 2 --scale 8192 --threshold 1/3
--ordered-prefix --root-tail --row-stride 64 --params 3 3 2 --row-bits 13
--integer --time-limit 120`. The shallow `V+E/8` drift gate adds
`--alignment-drift-stage 1 --alignment-drift-span 1 --alignment-weight 1/4
--alignment-drift-rho 1 --alignment-prev-floor 100
--alignment-error-weight 1/8`. The long-window gates replace those with
`--depth 5`, omit `--integer`, set
`--alignment-drift-stage 2 --alignment-drift-span 1`, and test
`--alignment-error-weight 1/8` or `1/2`.


## Two-transition return-phase drift

The 2-transition cycle gate at depth5, phase2->phase4, is also optimal but
allows drift `+46,080` for `V+E/2` (same geometric level ratio `1/4` and
same certified profile). Increasing the static local-error coefficient to
`E` worsens the maximum to `+107,520`; the optimizer changes its witness.
Both runs used continuous global count variables, sampled cuts every64 rows,
and zero solver gap. Thus the positive drift is not just level switching
between adjacent phases: the tested fixed potential also grows on a return to
the same active level. This makes a time-periodic or richer spatial state
necessary in the selected-cut model.

Reproduce by using the depth5 long-window command above with
`--alignment-drift-span 2`, first `--alignment-error-weight 1/2`, then `1`.


## Phase-dependent one-step weights

`coupled_rank_lp.py` now accepts separate source and destination level-weight
vectors via `--alignment-level-weights` and
`--alignment-next-level-weights`. On the depth5 phase2->3 gate, source weights
`(1/1000,1/1000,1,1/1000)`, destination weights
`(1/1000,1/1000,1/1000,1/1000)`, and `E/8` give maximum drift `-87.5125`.
But swapping those vectors on phase3->4 gives maximum drift `+3,516,122.413`.
Both are optimal selected-cut relaxations with the eight-point margin profile.
So downweighting the destination phase can make one transition contract, but
this particular two-phase return weighting fails catastrophically when the
state is restored to the source weights. This does not rule out a longer
phase-dependent potential; the tested vectors are only one candidate pair.

A tiny scale-8 invocation with distinct vectors passes, and the existing
source=destination commands retain their prior behavior. `python -m py_compile
upper-bound/experiments/prefix-flux/coupled_rank_lp.py` also passes.

## Optimized phase-weight gate (2026-10-24)

I replaced hand-chosen weights by a cutting-plane min-max search over one
nonnegative normalized level-weight vector for each of phases2,3,4. Each LP
optimum supplies a feasible adversarial trace and therefore an affine lower
cut on the worst `V+E/8` drift. To exclude the zero-alignment witness, the
gate imposes `sum_bag L1(b) >= 100` at the source phase; this constraint is
unweighted and independent of the potential weights. The two transitions
are optimized jointly, sharing phase3's vector as the destination of 2->3
and source of 3->4.

For `rho=0.99`, depth5, scale/row-height8192, row stride64, and the same
certified eight-point distance-tail profile, six optimal adversarial cuts
give a master lower bound `+1278.1778` even when every phase weight may be
zero. Thus no phase-dependent **level-only linear alignment potential** of
this form strictly contracts this finite selected-cut model over both
transitions 2->3 and 3->4. The best returned candidate has worst drift
`+1289.15`, leaving a master gap of about11. The largest witness feasibility
residual is `1.63e-5` on the 8192-row scale; every affine cut was checked
against its generating LP objective. The cuts and independently reproducible
master calculation are in the ignored local artifact
`LLM-helpers/sub300-phase-weight-rho099-floor000001.json`; the solver harness
is `optimize_phase_weights.py`.

This rules out that potential family for the stated finite relaxation, not
all spatial potentials or the fixed comparator network. It strengthens the
positive-drift gates: the remaining route needs a richer state (for example,
port-correlated cross-level flow) or tighter transition constraints that
remove the witness circulation. More Lean stage-bridge work will not address
this global obstruction.

## Centered-area constraint scaling gate (2026-10-29)

I added the checked two-shuffle bound `A_w/64 <= 169/8` to the coupled
rank-profile model using `--variance-prefix-area-gamma 169/8`. This also
activates its implied aggregate port-variation bound. With `(3,3,2)`,
`row_bits=8`, `scale=256`, root-tail initialization, all row cuts, and the
selected-cut global transition model, the optimal terminal wrong mass is:

| tree depth | wires `N=256*8^d` | baseline | area bound | area + monotone-column shape |
|---:|---:|---:|---:|---:|
| 2 | 16,384 | 2,105 | 205 | not run |
| 3 | 131,072 | 16,435 | 1,639 | not run |
| 4 | 1,048,576 | 131,044 | 13,105 | 7,973.52 |

The depth-2, depth-3, and depth-4 constrained optima were 205, 1,638.57, and
13,105 respectively; fractional values are allowed in this LP relaxation.
The area-constrained residual remains about 1.25% of `N` at every tested
depth. Adding the existing monotone-column profile condition lowers the depth-4
residual to 0.76% of `N`, still linear in this test. Thus the local variance
provider and this profile-shape condition substantially improve the
relaxation but do not force sublinear terminal error or a coefficient-300
cleanup. The model's transition horizon is only two stages in these runs, and it remains a
selected-cut relaxation rather than a trace of the fixed D2 network; this
does not refute that network. It does show that the area bound alone is not
the missing global invariant.

Reproduce the area-bound results with the same command at each depth `d`:

```text
python upper-bound/experiments/prefix-flux/coupled_rank_lp.py --depth d --scale 256 --threshold 1/3 --ordered-prefix --root-tail --all-row-dominance --row-stride 1 --params 3 3 2 --row-bits 8 --time-limit 60 --variance-prefix-area-gamma 169/8
```

The matched baseline omits `--variance-prefix-area-gamma 169/8`. The extra
depth-4 shape run adds `--column-profile-monotone`. All seven solves returned
optimal status. The next decisive constraint must connect
the same sender's error across the schedule's successive port maps, rather
than impose a local area cap independently at each represented transition.

### Four-transition candidate-scale stress test

At `depth=5`, `scale=row_count=512`, the same all-row selected-cut model has
four transitions and 82 active-sender area constraints. The baseline optimum
has 1,520,762 terminal wrong wires; imposing `A_w/columns <= 169/8` and its
implied port-variation cap lowers this to 248,548. The latter is still 1.48%
of `N=512*8^5=16,777,216`. Both solves are optimal; the constrained mixed
integer solve has zero MIP gap (447 auxiliary piecewise selectors), with
maximum displayed equality and inequality residuals `3.73e-9` and
`4.57e-8`. The count/profile variables themselves are continuous. This
confirms the small-scale pattern over four actual schedule transitions: local
area and port caps improve the relaxation by about sixfold, yet permit a
linear residual. It remains a selected-cut relaxation, not a fixed-network
trace or a refutation of the D2 construction.

Reproduce the constrained run with:

```text
python upper-bound/experiments/prefix-flux/coupled_rank_lp.py --depth 5 --scale 512 --threshold 1/3 --ordered-prefix --root-tail --all-row-dominance --row-stride 64 --params 3 3 2 --row-bits 9 --variance-prefix-area-gamma 169/8 --time-limit 90
```

The matched baseline omits the final variance flag. The remaining proof
obligation is a reachability/correlation invariant that excludes these
independently chosen per-sender profiles while retaining the actual fixed
network's transitions.

### Spine/off-spine refinement (2026-10-24)

The LP already partitions each stage's L1 mismatch into the unique bag whose
static interval contains the threshold (the spine) and all other bags. I
extended the potential search to assign separate phase- and level-dependent
weights to these two classes, sharing the phase3 vector across both
transitions. The 24-cut min-max master still has a positive lower bound:
`+1248.6243` for `rho=0.99`, even when all weights may be zero. Its best
candidate upper bound is `+1274.44`; the largest recorded witness residual is
`8.64e-5` on the 8192 scale. The zero-weight master was independently rebuilt
from the saved cuts in
`LLM-helpers/sub300-spine-phase-rho099-floor001.json`.

Thus splitting aggregate alignment into spine and off-spine mass does not
remove the selected-cut circulation. The next useful state must retain more
than the bag's total mismatch, such as the within-bag rank profile at child
ports, or the transition model must gain correlations that forbid these
witness traces. This remains a finite model obstruction, not a statement
about the fixed comparator network.


## 24-transition period attempt

An exact-height attempt at the screen's 24-transition refresh period (`depth=13`,
`scale=1`, `row_bits=13`, `row_stride=8192`, same profile, stage1 span24) did
not reach the optimizer. Model construction grew to about3.5GB resident /
4.5GB private memory, leaving under1GB free on the host, so it was interrupted
to avoid exhausting system memory. This is **inconclusive**, not a failed
period gate. A future run needs a reduced cut closure or a compressed phase
state before testing the full 24-transition return map.


## Long-span model size

Two longer-span attempts were stopped before optimizer results: depth13 /
24-transition construction reached about3.5GB resident and 4.5GB private memory;
depth10 / 15-transition reached about3.8GB private with roughly1.1GB free. A
depth8 / 9-transition construction stayed near1GB private but had not reached
optimization after eight minutes. All were interrupted; these are resource
limits, not mathematical failures. They show that simply increasing depth in
the current per-bag selected-cut LP is not a practical way to test the 24-step
refresh period. The next gate should compress bags by phase/role and retain
only the exact state aggregates needed by the alignment identities.

## Exact port rank-profile weight sweep

I added the exact port-cut profile potential `V + beta*P` to
`optimize_phase_weights.py`, where `P` sums `min(H_b,s)-Y_b(s)` at the D2
ports. At `beta=1/8`, two cutting-plane iterations leave a negative master
lower bound (`-225,747`) and a positive feasible candidate (`+160,098`), so
the result is unresolved. At `beta=1/2`, the same setup gives a positive
master lower bound (`+382,121`); the four accepted cuts have maximum primal
residual `9.16e-6`. This excludes every phase/level spine/off-spine linear
alignment weighting paired with that fixed `beta` from strict contraction in
this finite selected-cut model. It does not exclude other `beta`, richer
states, or traces of the fixed comparator network.

The ignored reproducibility artifacts are
`LLM-helpers/sub300-portprofile-beta0125.json` and
`LLM-helpers/sub300-portprofile-beta05.json`. Both runs use depth5,
scale/row-height8192, row stride64, `rho=.99`, exact port profiles, and
30-second adversarial solves. Some cuts come from feasible time-limit
incumbents; their equality, inequality, bound, and selector residuals were
checked before saving. The next useful test is a richer spatial state or a
strengthened transition contract, rather than a wider blind `beta` sweep.

## Phase/shell state compression

The new `d2_phase_shell_compression.py` traverses the exact interned flow DAG
by threshold shell. At depth8, it accounts for all 210,913,571 address-stage
occurrences with 4,033 distinct `(flow-node-state, shell)` classes. Two trailing
base-8 digits do not give a uniform quotient (first counterexample at depth7);
the exact state-shell key does. This is a deterministic flow-state compression
only. A compressed adversarial LP still must preserve independent local
separator profiles and the global rank objective. The next test is to sum the
identical per-sender local constraint polytopes over each state-shell class and
compare the resulting bound with the full model at a tractable scale.

A follow-up on the scalar interval recurrence identifies the missing state.
At depths5/6 with the 8192-row model, the exact state/shell partition alone has
15 history-inconsistent groups. Refining by exact nearest occupied-wire
distance to the threshold gives1,199/1,414 classes and a unique scalar
history interval in every class. However, two depth5 classes at stage3/level2
with identical current labels have different child-history vectors. Thus
margin restores current interval homogeneity but does not by itself give a
closed transition system. Preserve the joint child-port history or bound its
aggregate conservatively before treating the quotient as an LP state.

Finally, the script checks a radius-one star label (own flow/shell/history,
parent label and child digit, all child labels) against the next-stage exact
history. Depths5/6 have zero transition mismatches among4,084/5,260 star
classes. This identifies a compact finite state for the scalar interval
recurrence; it does not yet carry local separator profiles or prove an
all-depth transition theorem.

## Exact quotient and global-prefix LP checks (2026-10-24)

`d2_port_quotient_lp.py` now adds the eight certified distance-tail caps to
the equitable local-profile quotient. At depth5 and depth6 with
`scale=row_count=8192`, the quotient LP and the uncompressed
`coupled_rank_lp.solve(..., ordered_prefix=False)` have exactly the same
optimal objective (difference 0). At depth5 the quotient has 3,359 variables
versus 3,807 raw variables, and bounds the summed terminal wrong mass by
1,885,719.80; without the tail caps the corresponding value was 3,233,571.
At depth6 it is 15,041,040.37 with the caps, versus 25,841,216 without them.
These terminal quantities sum over nested occupied bags, so they are not
counts of distinct wrong wires. They show that the local tail caps tighten the
relaxation but do not establish a useful global contraction by themselves.
This quotient's scalar history is generated from `H=(q,q)` at the root, so
these comparisons are conditional on the sorted-root history; they are not an
arbitrary-input gate.

**Correction:** the zero-error ordered-prefix runs above were tautological
sorted-input fixed-point checks. They all used `root_error=0` and
`root_tail=False`; in `coupled_rank_lp.py`, that fixes the initial global
prefix profile to `min(q,cut)`. Their exact dual certificates only verify the
encoded LP at an already sorted input and provide no evidence about sorting
arbitrary inputs. The captured exact duals remain useful for testing the
export/check machinery, but should not be cited as sorting progress.

The relevant arbitrary-input model must use `--root-tail`, which leaves the
initial profile variable subject to the root rank-tail envelope. Existing
results in `STATUS.md` show positive terminal error for this model at depths4
and5; the immediate gate is now to add the distance-tail sender constraints
and see whether they remove that error. At depth2, scale/row-height8192,
`(3,3,2)`, root-tail and stride64, adding all eight caps solves to 6,390.0192
terminal wrong mass (largest block 2,078) in the continuous LP. Requiring all
1,081 model variables integral solves to 6,390 (largest block 2,082), with
zero equality residual and maximum inequality residual `7.5e-8`. This is a
feasible local-profile witness, not a legal network trace; it shows the
stronger caps still do not force global alignment even in this small gate.
In that integer solution's final decomposition, global prefix defect is
6,400 = 3,670 cross-bag alignment + 2,730 within-bag defect; the off-spine
level-two alignment is 6,390 across14 nonzero bags. The dominant remaining
gap is therefore spatial rank placement, not merely total local defect.

A shallow weighted-drift probe illustrates the depth sensitivity. With
`beta=1/8`, `rho=1/2`, and source-potential floor100, the stage1-to-2 maximum
drift is `-6.625` at depth2, but `+165.59375` at depth3 with the same row
height and tail profile. Thus the shallow contraction is not stable as the
tree gains another level; a useful potential must account for the full
level/phase circulation, not just one downward transition.
At depth5, the same arbitrary-root model with stride64 and all eight caps
returns HiGHS `Unknown / primal Basic`, so there is no candidate-scale result.
Full root-row closure was stopped during prolonged model construction. The
`--row-stride` argument alone does not add active-sender row cuts: that
requires `--all-row-dominance`.


## Exact sampled rank-profile potential gate (2026-10-25)

I tested whether adding the within-bag rank-defect area to level-weighted
alignment repairs the phase-2 to phase-3 drift. The LP uses the arbitrary-root
13-bit tail envelope, ordered global prefixes, stride-64 cuts, the all-row
dominance constraints, the `17/2000` seam cap, and exact selectors for the
retained rank-profile defects. At row grid `2^8`, both tested fixed weights
produce a constraint-feasible positive-drift incumbent before the 120-second
HiGHS limit:

| rank-profile weight | max drift incumbent | rank-profile drift | solver gap |
|---:|---:|---:|---:|
| `1/8192` | `+424,299.46` | `+2,099,576.47` | 1.75% |
| `1/4` | `+1,541,714.43` | `+6,453,591.21` | 553% |

Both incumbents have equality, inequality, bound, and selector residuals below
`2e-7`. The time-limit results are not optimality certificates; their positive
feasible values do suffice to refute contraction for these two fixed weights in
the encoded selected-cut relaxation. The global count profiles are continuous,
so these are not actual-network counterexamples. The second weight also drives
the model to a much larger terminal error, indicating that simply assigning
a large coefficient to sampled local rank defects lets the relaxation exploit
the loose relationships between adjacent sampled cuts.

Reproduce either run by replacing `W` below with `1/8192` or `1/4`:

```text
python upper-bound/experiments/prefix-flux/coupled_rank_lp.py --depth 5 --scale 8192 --threshold 1/3 --ordered-prefix --root-tail --all-row-dominance --row-stride 64 --seam-defect-fraction 17/2000 --params 3 3 2 --row-bits 8 --alignment-drift-stage 2 --alignment-drift-span 1 --alignment-weight 1/4 --alignment-drift-rho 1 --alignment-prev-floor 100 --alignment-prev-floor-unweighted --rank-profile-weight W --rank-profile-exact --time-limit 120
```

The next potential gate must retain correlations across the complete local rank
profile (or use the actual 8192-row certified profile); another scalar
coefficient sweep on sampled defects is not justified by these results.


## All-retained-cut potential and builder profile (2026-10-25)

I extended `coupled_rank_lp.py` with `--rank-profile-all-cuts`, so the
rank-defect component can use every local profile cut retained by cut closure,
rather than only sender port boundaries. At the actual 8192-row scale,
`row_stride=64` solves optimally with max drift `-18.75`; the optimizing witness
has zero sampled rank-defect potential at both endpoints. Thus this shallow
contraction is still the previously known `V+E/8` gate, not a gain from the
extra state.

At `row_stride=8`, the same conservative source-lower/destination-upper
rank-defect model has 74,120 variables and 220,804 inequalities. HiGHS hit its
120-second limit, but its minimization dual bound is `+12.56075` while its
feasible objective is `+18.75`. Since the minimized objective is the negative
of potential drift, the solver's numerical bound puts max drift at most
`-12.56075` in this finite sampled relaxation. The local rank-defect component
again vanishes at the incumbent; this does not test unsampled within-row
defects or establish a network theorem. The initial every-row (`row_stride=1`) build was stopped after more than
16 minutes before producing a model. After adding the analytic gradient, a
repeat still exceeded 3.5 GB and produced no result after about 11 minutes; it
was stopped to bound resource use. A complete every-row LP remains impractical
in this implementation.

Profiling the pre-change code isolated the dominant cost:
`rank_recurrence.prefix_interval` called `sparse_probe.profile_tail` 12,284
times, and each distinct tail invoked three L-BFGS-B optimizations with
numerical gradients in `moderate_tail.bound`. Those optimizations accounted
for 355 seconds of a 370-second 1024-row-grid model run. Supplying the analytic
two-variable gradient reduced the same profiled run to 120 seconds while
preserving the solver result
(`max_alignment_drift=-18.750000000001`); finite-difference checks on 32
parameter points had maximum relative gradient error `7.3e-7`. This Python
optimization is more effective than porting the cut builder to C++: the
standalone cut-closure pass took only `0.44` seconds, while repeated numerical
optimization dominated. The fine-grid build is still expensive and the
sampled potential does not resolve the global rank-transfer gap.


## Phase-2 to phase-3 exact rank-profile witness at row height 8192

With all retained local rank cuts included at `row_stride=256` and exact
selectors for `min(H,s)`, the arbitrary-root depth-5 model has a feasible
positive-drift incumbent for `V + E/8 + R/8192`, where `V` is geometric
bag alignment, `E` is the threshold defect, and `R` is the sum of exact local
prefix defects at retained cuts. The phase-2 to phase-3 drift is
`+137,865.05`; the exact rank-profile component itself increases by
`5,093,571.15`. HiGHS hit the 120-second limit, so this is a feasible witness,
not an optimum. Its equality, inequality, bound, and integrality residuals are
`1.39e-7`, `3.58e-7`, `4.47e-8`, and `0`, respectively.

This refutes contraction of this fixed weighted potential in the finite
selected-cut relaxation. The profile variables are continuous, cuts are sampled
every 256 rows, and the model does not represent one common comparator-network
trace; it is not a counterexample to the fixed network. It does show that exact
rank defects at the sampled cuts, added to the present sender tail and
prefix-dominance contracts, still permit cross-level alignment circulation.

Reproduce with:

```text
python upper-bound/experiments/prefix-flux/coupled_rank_lp.py --depth 5 --scale 8192 --threshold 1/3 --ordered-prefix --root-tail --all-row-dominance --row-stride 256 --distance-tail-profile 64=103/10000,128=78/10000,256=47/10000,512=151/100000,1024=319/500000,2048=31/100000,4096=7/40000,8192=117/1000000 --params 3 3 2 --row-bits 13 --alignment-drift-stage 2 --alignment-drift-span 1 --alignment-weight 1/4 --alignment-drift-rho 1 --alignment-prev-floor 100 --alignment-prev-floor-unweighted --alignment-error-weight 1/8 --rank-profile-weight 1/8192 --rank-profile-exact --rank-profile-all-cuts --time-limit 120
```

## Sparse-cut second-moment enclosure (2026-10-25)

`coupled_rank_lp.py --inversion-sparse-enclosure` bounds the global distance
moment from retained static-wire cuts without constructing every wire cut.
For `F(r)=min(q,r)-Z(r)`, binary profiles make `F` nondecreasing through `q`
and nonincreasing afterward. Between retained cuts, use the appropriate
endpoint as a lower or upper bound; the order-`s` cut weights telescope over
each gap. Thus maximizing `M_s(destination)_upper-rho*M_s(source)_lower`
gives a valid outer bound on moment drift for every actual binary profile
satisfying the represented transition contracts. The returned moment values
are scaled by `N^(s-1)` to keep LP coefficients well conditioned.

Validation: exhaustive enumeration checked the gap enclosure on all 2,044
binary words of lengths 2 through 10 for `s=2`, with sparse cuts including the
threshold. With all cuts retained, exact and enclosure LPs both optimize to
zero second-moment drift on the depth-6 `(2,2,1)` diagnostic. The LP is
degenerate, so they choose different optimizer profiles: the exact model
reports equal source/destination moments `6,603,876,199`; the enclosure model
reports equal `M2/N` bounds `1,655,674.29`.

At the target `(3,3,2)`, depth 5, scale/row height 8192, the all-row
dominance model with the eight-point certified distance-tail profile and
`row_stride=1024` solves the phase-2-to-3 gate optimally. At `rho=1`, its
upper bound on `M2(destination)-M2(source)`, in the script's `M2/N` scale, is
`-7,570,844,424,320` (source lower bound `22,509,024,705,192`, destination
upper bound `14,938,180,280,872`). SciPy's wrapper returned numerical
`Unknown` on most phases. Solving the same matrices through raw `highspy`,
with presolve disabled and Dantzig dual-simplex, gave optimal bounds at
`rho=0.9` for all four transitions:

| transition | source lower (`M2/N`) | destination upper (`M2/N`) | drift upper | ratio |
|---:|---:|---:|---:|---:|
| 0 -> 1 | 39,080,856,288,704 | 31,812,507,895,254 | -3,360,262,764,580 | 0.8141 |
| 1 -> 2 | 24,250,943,862,422 | 16,693,604,018,930 | -5,132,245,457,250 | 0.6884 |
| 2 -> 3 | 24,160,469,807,502 | 16,581,489,152,372 | -5,162,933,674,380 | 0.6863 |
| 3 -> 4 | 24,094,966,386,322 | 16,532,530,805,032 | -5,152,938,942,658 | 0.6861 |

Each model has 13,059 variables and 31,322 inequalities. Across the four
solutions, equality residuals are at most `4.92e-7` and inequality residuals
at most `1.91e-6`. These are floating-point LP optima, not rational dual
certificates. Strides 512/2048 and the full four-transition objective remain
unresolved.

These phase gates share one depth-5 root-tail initialization; they do not
establish the transition inequality for every admissible source profile, nor
the all-depth invariant or terminal sorting criterion. The results are
promising finite recurrence evidence, not an upper-bound proof.

Reproduce the `rho=0.9` gates by adding
`--inversion-drift-stage T --inversion-moment-order 2 --inversion-drift-rho
9/10 --inversion-sparse-enclosure --no-presolve --lp-method highs-ds
--simplex-edge-strategy dantzig --raw-highspy` to the target-scale command
above, setting `--row-stride 1024`, and using `T=0,1,2,3`. The next mathematical gate is to
establish a uniform transition bound from every admissible source state,
including the final phase, then prove its induction and sorting terminal
contract.

## Shifted arbitrary-source and deeper-period gates (2026-10-25)

`--transition-source-stage t` now shifts the exact D2 flow window to stage
`t`, frees the source global binary profile subject only to its exact total
zero count and the scalar-history interval for each bag, and applies the
sender tail/provider constraints to the selected transition. Set
`--transition-source-span L` with `--inversion-drift-span L` to test a return
map. This is a larger source set than states reached from the particular
depth-5 root-tail input, so it tests a reusable induction interface.

For depth 5, each of the four one-step gates contracts at `rho=0.99`; a
six-step bisection placed the worst threshold near `0.983` (phase 2), with
phase 1 near `0.953` and phase 3 near `0.974`. These values were specific to
the depth-5 geometry. At depth 7, the optimal arbitrary-source one-step gates
at `rho=0.99` have positive drift in phases 3 and 4 (`+4.30e16` and
`+4.60e16` in the `M2/N` scale); phase 5 also has a positive incumbent
`+3.21e16`. Thus depth-5 one-step contraction does not extrapolate to the
deeper schedule. These are LP-profile witnesses, not traces of the fixed
sorting network.

The depth-7 four-transition gate from source stage 3 to stage 7, at `rho=0.99`,
built 88,397 variables and 178,469 inequalities. Raw HiGHS returned
`Unknown` with a feasible primal candidate of drift `+2.48e16`; residuals
were `6.5e-4` equalities and `3.4e-3` inequalities. This does not establish
the period's optimum or sign, but the candidate does not support a strong
contraction. The shifted-source interface therefore finds the main issue:
the finite root-initialized gates hid adverse intermediate profiles, and the
generic D2 rank-moment recurrence remains too weak or insufficiently
correlated for a sub-300 proof. A new state/potential or structural algorithm
change is still needed.

## Strong aggregate-area stress gate (2026-10-25)

At depth 4, scale 512, row-bits 9, with root-tail initialization, all-row
local prefix dominance, and both aggregate-area and seam-defect caps set to
`1/1600`, the continuous selected-cut model solves optimally with terminal
wrong mass `66.0099`. Residuals are at most `2.65e-7`; the model has 27,598
variables, 8,614 equalities, and 82,143 inequalities.

Reproduce with:

```text
python upper-bound/experiments/prefix-flux/coupled_rank_lp.py --depth 4 --scale 512 --threshold 1/3 --ordered-prefix --root-tail --all-row-dominance --row-stride 1 --aggregate-defect-fraction 1/1600 --seam-defect-fraction 1/1600 --params 3 3 2 --row-bits 9 --time-limit 120
```

Important scope correction: `aggregate-defect-fraction` caps the **sum over
all row-prefix cuts** in a bag. The B2 provider contract is pointwise at each
output cut, so this aggregate cap does not follow from the provider; the seam
cap is also a separate abstraction. This is only an artificially strong
stress relaxation, not a test of the provider's actual scalar contract.
Requiring every profile variable to be integral at the looser `1/800`-per-
category caps timed out at 120 seconds without an incumbent.

## Pointwise B2 cut-budget gate (2026-10-25)

The explicit ragged-provider paper screen gives a pointwise full-row cut
budget `1/800` after transferring B2's `3/2500` error and the fixed-mask
boundary mismatch. I added `--local-cut-defect-fraction` to constrain each
local full-row prefix defect by that fraction of bag size, using exact
piecewise-linear min-count selectors. This matches the *form* of the B2
contract; the test is still a reduced D2 relaxation at row-height 512, not
the 8192-row fixed-mask provider or its 8307-column profile.

At depth 4, scale 512, row-bits 9, with root-tail initialization and all-row
local prefix dominance, the optimal continuous selected-cut model under the
pointwise `1/800` cap leaves terminal wrong mass `5,242.88`. It uses 36,823
variables, 17,839 equalities, and 86,688 inequalities, including 4,608
pointwise local-cut constraints; equality residual is below `1.2e-10` and
inequality residual below `6.8e-8`. This identifies the
global gap more faithfully: the pointwise local B2 budget together with the
retained profile-tail bounds does not close rank transfer in this relaxation. It does not refute the
fixed network; F2 constraints, the exact heterogeneous mask, and comparator
trace correlations are absent.

Scope correction: that run also retained the model's `prefix_interval`
profile-tail bounds. It was not a test of the B2 cut budget in isolation.
The new `--cardinality-prefix-relaxation` switch removes those extra local
profile-tail assumptions, retaining only cardinality bounds, exact
first-column lower bounds, sampled comparator-prefix dominance, and the
explicit B2 cut budget.

The matching row-height-8192 run was stopped after more than seven CPU
minutes without returning model or solver status. The process remained
CPU-bound at about 150 MB working set. Since the script reports only after
matrix assembly and optimization, this does not distinguish Python assembly
from solver time; treat the full-scale depth-4 gate as unrun. The candidate-
height depth-2 screens below are more informative for the scalar-contract
question.

### Candidate-height sampled B2-only gate

At depth 2 and actual row height 8192, I removed the profile-tail bounds and
sampled local/global prefix cuts every 64 rows. The history-only consequence
of B2 at each retained full-row cut is
`Y(cut) >= min(H_lower,cut) - a/800`; it is weaker than the exact contract
because `H_lower <= H`. The continuous LP solves optimally in about 12
seconds with 8,441 variables, 2,461 equalities, and 24,609 inequalities.
It leaves terminal wrong mass `1,310.72` (maximum one-block error 655), with
terminal threshold defect `825.36`, split into cross-bag alignment `655.36`
and within-bag defect `170`. Equality and inequality residuals are below
`3e-11` and `5e-10`. The solution is fractional; this is evidence that the
sampled scalar contract plus the retained geometry does not prove cleanup,
not a network counterexample.

The integer version at stride 128 also solves optimally: zero MIP gap after
4,773 nodes, with 4,345 variables, 1,437 equalities, and 12,321 inequalities.
It leaves exactly 1,310 terminal wrong keys (maximum one-block error 448).
The terminal threshold defect is 997, split into cross-bag alignment 655 and
within-bag defect 342. All count/profile variables are integral, and equality,
inequality, bound, and integrality residuals are at most `3e-9`. Thus the
positive terminal mass is not a fractional-profile artifact in this sampled
relaxation. It remains an abstract integral flow: no fixed comparator trace is
encoded, and B2 is imposed only at the retained cuts.

Reproduce the integral gate with:

```text
python upper-bound/experiments/prefix-flux/coupled_rank_lp.py --depth 2 --scale 8192 --threshold 1/3 --ordered-prefix --root-tail --all-row-dominance --row-stride 128 --local-cut-defect-fraction 1/800 --cardinality-prefix-relaxation --local-cut-history-relaxation --params 3 3 2 --row-bits 13 --time-limit 120 --integer
```

The unsampled exact B2 cut linearization at depth 2 and row height 8192
generated 409,846 variables and 1,228,824 inequalities, then hit its 120-second
HiGHS limit without a primal solution. The limitation there is MILP scale;
rewriting Python assembly in C++ would not remove the segment-selector
optimization. Use the sampled continuous gate for quick structural screens.
Reproduce it with:

```text
python upper-bound/experiments/prefix-flux/coupled_rank_lp.py --depth 2 --scale 8192 --threshold 1/3 --ordered-prefix --root-tail --all-row-dominance --row-stride 64 --local-cut-defect-fraction 1/800 --cardinality-prefix-relaxation --local-cut-history-relaxation --params 3 3 2 --row-bits 13 --time-limit 120
```

Reproduce with:

```text
python upper-bound/experiments/prefix-flux/coupled_rank_lp.py --depth 4 --scale 512 --threshold 1/3 --ordered-prefix --root-tail --all-row-dominance --row-stride 1 --local-cut-defect-fraction 1/800 --params 3 3 2 --row-bits 9 --time-limit 120
```

### Tail profile implied by the aggregate-area cap

There is a valid but redundant distance grading available without another
provider theorem. Write `d_j=min(H,jC)-Y(jC)` for the defect at row boundary
`j`, where each row has `C` wires, `H` is the total count of the tracked key
class, and `Y(s)` counts that class in the first `s` wires. If
`H<=jC-rC`, the `r` preceding boundaries `j-r,...,j-1` lie on the `H<=s`
side and each has defect at least `d_j`, since `Y` is nondecreasing. If
`H>=jC+rC`, use the `r` following boundaries `j+1,...,j+r` on the `s<=H`
side; their defects are at least `d_j` because `Y` increases by at most the
number of wires added. Hence the total prefix-defect area `A=sum_k d_k`
satisfies `r*d_j<=A`. An aggregate-area bound `A<=epsilon*a` consequently
implies the margin-tail cap `d_j<=epsilon*a/r`.

I added the resulting dyadic profile `T(r)=1/(1600*r)` to the depth-4
selected-cut gate with `epsilon=1/1600`. It adds 3,722 constraints, but the
optimal terminal wrong mass is unchanged at `66.0099` (residual below
`2.5e-7`). This confirms the profile contributes no strength beyond the
aggregate area in this model; a genuinely useful distance profile must come
from a sharper provider estimate. The separate eight-point profile above
comes from the UB-34 separator certificate and has not been connected to the
ragged 13-row provider, so it cannot be substituted as that provider's bound.
Reproduce the redundant-profile screen by adding
`--distance-tail-profile 1=1/1600,2=1/3200,4=1/6400,8=1/12800,16=1/25600,32=1/51200,64=1/102400,128=1/204800,256=1/409600`
to the command above.

## Arbitrary-source second-moment gate at a reduced row height (2026-10-26)

I shifted the D2 flow window to stage 3 and optimized the one-step order-2
distance-moment drift at `rho=0.9`, freeing the source global binary profile
subject to the model's scalar-history bounds. At depth 7, scale 512, row
height 512, the continuous LP found positive drift. I then reran the model as
an integer program. HiGHS reported an optimum with zero MIP gap (2,982
variables, 2,497 equalities, 4,172 inequalities). Rounding its returned point
to integers and checking every saved equality and inequality with exact
integer sparse arithmetic gave zero violations (11,995 equality and 10,248
inequality nonzeros). The model-reported source and destination moments are
`6.726227514800872e16` and `6.771088663706547e16`, with drift
`+7.174839003857624e15` in normalized `M2/N` scale. Thus there is an exactly
feasible integral witness with large positive drift in this finite
relaxation. The objective and optimality status still come from floating
point; the exact check certifies feasibility, not exact optimality or a
concrete network trace.

Reproduce with:

```text
python upper-bound/experiments/prefix-flux/coupled_rank_lp.py --depth 7 --scale 512 --threshold 1/3 --ordered-prefix --all-row-dominance --row-stride 64 --params 3 3 2 --row-bits 9 --transition-source-stage 3 --inversion-drift-stage 0 --inversion-moment-order 2 --inversion-drift-rho 9/10 --inversion-sparse-enclosure --no-presolve --lp-method highs-ds --simplex-edge-strategy dantzig --raw-highspy --time-limit 120
```

This is not a fixed-network counterexample. It shows that a uniform `M2`
contraction theorem cannot follow from these scalar-history and selected-cut
constraints alone; it does not refute a stronger invariant for states
actually reached by one fixed comparator network. Reproduce the exact primal
feasibility check with `python LLM-helpers/verify_d2_m2_relaxation_witness.py`.

As a stricter reachability screen, I removed `--transition-source-stage` and
kept the complete depth-7 root-tail history, moving the M2 objective to stage
3. At the same row height 512 and `rho=0.9`, HiGHS reached its time limit with
a feasible positive-drift candidate `+5.80259131751929e14`; source and
destination values were `5.793944500956096e15` and `5.794809182612416e15`.
The model has 155,111 variables, 119,923 equalities, and 339,097 inequalities;
the returned residuals were `2.21e-6` and `2.97e-5`. This is not an exact
certificate, but it suggests the arbitrary-source growth is not solely caused
by freeing the intermediate profile. Exact rational recovery and the target
8192-row provider constraints remain necessary before treating it as a
mathematical obstruction.

## D2 448-port allowance sensitivity gate (2026-10-26)

The kernel-checked fixed-core result in `D2Slope25RowMajorBridge.lean` gives
aggregate port l1 error at most448 for a complete4096-by-64 sender partition,
which is7 per column. I tested that numerical scale in the selected-cut model
by setting `--variance-port-l1-gamma 169/8`: its rational square-root
rounding gives a cap of `(sqrt(2*169/8)+1/2)*columns = 7*columns` on each
eligible sender. With the corrected width-64 distance-tail profile, depth2,
8192-row scale, all-row dominance, row stride64, and integral variables, the
MILP timed out at120s, but HiGHS' minimization dual bound was171528 against
the constant172032. Since reported wrong mass is `172032 - objective`, this
gives the numerical solver bound of at most504 residual wrong keys (gap
0.293%). The continuous relaxation solves optimally at504. The time-limited
integral run has no feasible primal witness, so it does not certify an
integral optimum or terminal sorting.

For comparison, relaxing the cap slightly to7.5 per column
(`--variance-port-l1-gamma 49/2`) solves the integral model optimally with540
wrong keys and63 noncrossing blocks. The cap-7 result is consistent with a
meaningful tightening, but neither model result is itself a Lean theorem.
More importantly, this numerical port cap is not yet a valid transfer of the
448 theorem to every LP sender: the Lean estimate is for a fixed4096-by-64
geometry, while the LP's active sender dimensions vary. The immediate proof
interface is therefore still to generalize the local aggregate bound to the
actual sender geometry and show its leakage is absorbed by the D2 flow
reserve. This experiment does not resolve the multi-stage alignment drift.

Reproduce the cap-7 run by adding
`--variance-port-l1-gamma 169/8 --integer --time-limit 120` to the depth-2
command in the preceding section; omit `--integer` for the optimal continuous
result. The corresponding cap-7.5 optimum uses `--variance-port-l1-gamma
49/2`.

## Tight aggregate port cap at the 512-row stress scale (2026-10-26)

I added `--variance-port-l1-gamma 169/8`, which constrains each eligible
sender's aggregate port l1 discrepancy to7 per represented column, alongside
the corrected width-64 tail profile and all-row dominance. At depth5,
`scale=512`, `row_bits=9`, and stride64, the continuous selected-cut LP
optimally maximizes the phase-2 one-step drift of `V+E/8` at `+30,435.19`.
It has15,517 variables, 9,915 equalities, 31,977 inequalities, 82 aggregate
port constraints, and891 distance-tail constraints; maximum equality and
inequality residuals are `6.1e-9` and `2.3e-8`. This is much smaller than the
previous `+190,438` depth-5 witness without the port cap, but it remains
positive. Therefore the local port cap does not establish this fixed
one-step potential inequality in the selected-cut relaxation.

The matched integral MILP timed out after120s without a primal point, so it
does not confirm the positive drift with integral counts. Both runs are
reduced-scale relaxations, not traces of the fixed comparator network; this
rejects only the tested scalar potential under these constraints. It points
back to a spatial rank state tied to actual flow reachability or a phase- and
address-dependent potential. Reproduce with `coupled_rank_lp.py --depth 5
--scale 512 --threshold 1/3 --ordered-prefix --root-tail
--all-row-dominance --row-stride 64 --params 3 3 2 --row-bits 9
--time-limit 120 --alignment-drift-stage 2 --alignment-drift-span 1
--alignment-weight 1/4 --alignment-drift-rho 1 --alignment-prev-floor 100
--alignment-error-weight 1/8 --distance-tail-profile
64=103/10000,128=78/10000,256=47/10000,512=185/100000
--variance-port-l1-gamma 169/8`; add `--integer` for the inconclusive MILP run.

## Arbitrary-root correction to the quotient gate (2026-10-28)

The earlier `d2_port_quotient_lp.py` results silently fixed the root's every
selected prefix to `min(q,cut)`, i.e. the already-sorted threshold profile.
That made its depth-5 terminal objective a sorted-root fixed-point test. The
script now defaults to the arbitrary-root model: the root has exactly `q`
threshold zeros, but each local root prefix ranges over the `prefix_interval`
bounds induced by the modeled margin-tail caps; `--sorted-root` preserves the
old diagnostic. Raw-model comparison is opt-in and restricted to the legacy
sorted-root case. The caps are certified numerically, but their transfer to
the actual D2 local core is still unproved, so this remains a model gate.

Using the corrected width-64 eight-point tail profile at
`depth=5, scale=row_count=8192`, the arbitrary-root quotient solves optimally
with 2,477 classes, 3,359 variables, 2,056 equalities, 2,064 inequalities and
464 tail constraints. Its summed terminal wrong-mass objective is
4,376,781.515, with maximum equality residual `1.40e-9` and inequality
violation `2.14e-9`. Without distance-tail caps, its optimum is 5,859,245
(zero displayed residual), so the caps reduce this relaxation objective by
about25.3% but leave substantial error. The objective is versus 1,882,883.515
for the sorted-root diagnostic with the same constraints. The arbitrary-root
depth-2 result is 6,390.0192, matching the previously reported continuous
root-tail gate. These objectives sum
errors over nested terminal bags, so they are relaxation objectives rather
than distinct wrong-key counts. The result confirms that the local tail
provider plus this port-flow relaxation leaves substantial global alignment
freedom; it is not a counterexample to the fixed network. Reproduce with
`d2_port_quotient_lp.py --depth 5 --scale 8192 --row-count 8192 --params 3 3
2 --time-limit 120 --distance-tail-profile
64=103/10000,128=78/10000,256=47/10000,512=185/100000,1024=863/1000000,2048=452/1000000,4096=264/1000000,8192=178/1000000`.

At depth6 the same arbitrary-root profile solves in10.2s with the same2,477
classes and3,359 variables, yielding35,028,192.118 summed terminal wrong
mass. At depth2 it yields6,390.0192, matching the earlier arbitrary-root
root-tail gate. The sorted-root compatibility check at depth2 matches the raw
LP exactly (300 variables; objective difference below3e-11).
