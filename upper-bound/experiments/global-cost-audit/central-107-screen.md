# Central 107-layer target: candidate-screening update

Research review, 2026-10-10. No construction or lower bound is established.
This checks whether the currently indexed multiway-halver lead directly fills
the central repair slot from [the disjoint bulk budget](disjoint-bulk-budget.md).

## Required contract

A central network on roughly `2^43` rows must be fixed in advance, confined to
the central rectangle, and handle all 63 interior threshold cuts in one common
network. For each cut, it must leave at most the actual bulk error allowance
minus the possible `2048*n` contamination from the protected windows. It must
also tolerate the central mass perturbation caused by those windows. The same
network is used for every rank and for both orientations. The available depth
is 107 binary-comparator layers; the target does not ask for a full sort.

## Screening the AKS 1992 lead

The indexed Ajtai–Komlós–Szemerédi result is a two-layer `k`-sorter
**halver for one cut**. It does not give the required 63-cut near-sorter. The
paper's final p-way near-sorter is a proposal, with its part-combination step
left to reconstruct; it does not supply the needed global error-repair
schedule.

A direct Batcher simulation of the two `k`-sorter layers costs
`r*(r+1)` binary layers at `k=2^r`: 156 layers for `k=4096`, 182 for
`k=8192`. These already exceed 107, before any multiway combination or
finishing work. At `k=8192`, the paper's stated halver error is still on the
order of several percent, whereas this central interface has an error fraction
on the order of `10^-8`. The distributional input promise might allow a looser
local primitive, but that would require a new analysis rather than invoking
the theorem as stated.

Thus the AKS lead is a useful design prompt, not a current 107-layer
candidate. Faster explicit small `k`-sorters alone do not address the missing
all-cuts guarantee or error contraction.

## Most promising next test

The smallest informative experiment is to derive the paper's proposed p-way
composition completely for one finite parameter tuple, then write a table of
(1) exact cut error, (2) binary depth including the `k`-sorter implementation,
(3) cuts/ranks covered, and (4) remaining correction depth. Reject it if it
cannot improve the central 631-layer baseline or if its error contract does not
compose under the actual row-scrambled distribution.

A custom expander is premature until this interface check succeeds: the
existing central obstacle is not lack of a graph certificate, but the absence
of a shallow *simultaneous all-cuts* primitive with a quantitative residual
error bound. If no p-way construction survives the parameter check, the 107
budget should be treated as an aspirational target; the honest fallback remains
631 layers and conditional coefficient 1261.5.

## Finite Batcher-priced tuple

For two serial `k`-sorter one-factors, simulating each `k`-sorter with a
Batcher bitonic network on `k=2^r` wires costs

```
2 * (r*(r+1)/2) = r*(r+1)
```

binary layers. The largest power-of-two arity fitting 107 layers is
`k=512` (`r=9`): cost 90, leaving 17 layers for the entire p-way combination.
At `k=1024`, the two sorter rounds alone cost 110. For the paper's stated
`epsilon=2*sqrt(log(k)/k)` at `k=512`, the estimate is about `0.221` with
natural logarithm and `0.265` with base-two logarithm. The central contract
needs errors around `10^-8` of the central height. This is a gap of over seven
orders of magnitude for an arbitrary-input guarantee.

The tuple `(k,p)=(512,16)` or `(512,32)` therefore cannot yet be called a
candidate: the paper gives no finite p-way combination depth or error formula
to price in the remaining 17 layers. The paper's suggestion is asymptotic and
points to a separate work “in preparation.” We cannot fill that missing
calculation from the published theorem alone. This does not rule out a
row-scramble-specific analysis with a much weaker local guarantee, nor a
better-than-Batcher implementation of the k-sorters.

## A row-scramble obstruction for the two-round k-sorter core

There is a sharper test than applying the arbitrary-input epsilon bound. It
uses a balanced two-height profile, which is in the currently retained L1
class (though not known to be reachable after every common first-scramble
witness).

Take `k=512`, a central interval of length `H=kN`, and its middle cut. Let
half the columns have height `H/2+delta` and half have height `H/2-delta`,
with `1<=delta<N`. Their total mass is exactly `H*n/2`, and their L1 deviation
from the cut is `delta*n`. At each of the `2*delta` physical rows around the
cut, exactly half the columns are high. Independent uniform row scrambles
therefore make the boundary bits for a fixed destination column independent
Bernoulli(1/2).

The first vertical k-sort sees the `delta` possible highs immediately above
the cut as one boundary-row defect set, and the `delta` possible holes just
below the cut as a second set. Conditional on the fixed row permutations of
the second one-factor, let their image supports be `S_H,S_L`, each of size
delta. At an offset in `S_H intersect S_L`, the second vertical k-sort leaves
one high in the upper half exactly when the upper defect is 1 and the lower
hole is 0, probability `1/4`. At an offset in `S_H \\ S_L`, that probability
is `1/2`. Thus the expected leakage after the two k-sorter rounds is

```
|S_H intersect S_L|/4 + (delta-|S_H intersect S_L|)/2 >= delta/4.
```

This holds for every fixed choice of row permutations. Best alignment of the
two supports still leaves the `delta/4` floor. For the central geometry,
`delta` can be `floor(m/2^18)` and `N=(m-2*T)/512`, so `delta<N`. The expected
residual is then about `m/2^20` per sorting column, while the full central
repair allowance is about `m/1.2e8` per column after the protected-window
reserve: a gap of roughly 110-fold. This rules out the two-round k-sorter core
as the complete repair even under this row-scramble law.

It does **not** rule out the proposed p-way combination: the remaining 17
layers could still mix and repair these boundary defects. But they must reduce
expected leakage by at least about 110-fold, simultaneously for all ranks and
all supported `delta`. The defects occupy a `delta`-sized boundary interval;
matchings chosen uniformly over the whole `N`-position row are too diffuse at
`delta/N ~= 1/512`. A viable finishing network needs a multiscale/localized
mixing argument, with its depth charged, or a stronger first-scramble promise
excluding this profile.

This is a conditional obstruction to the 107-layer route under the stated
L1-only profile interface, not a global impossibility result: reachability of
the two-height profile under the actual first scramble has not been proved.

## What the 17-layer residual repair must accomplish

Normalize to a support interval of `delta` positions where the two boundary
rows can contain defects. In the best-aligned case, immediately after the
k-sorter core, each position has independent state

```
high-only with probability 1/4,
hole-only with probability 1/4,
matched/clean with probability 1/2.
```

For this profile, the reserved bulk allowance is about `0.0022*delta`, versus core expectation `0.25*delta`. Thus `0.0022` is a conditional stress-test threshold: it applies if this two-height profile is reachable after the fixed scramble. The later common first-scramble localization promise excludes this profile on its good event: its mass beyond the band is about 8 million per column, while that promise allows only A=4,096--8,192. Thus this is not a necessary target for the revised reachable class, assuming that localization argument holds. The exact obligation is the input- and cut-dependent repair slack in [the repair contract](repair-contract.md), or a direct proof of the repaired count against the scheduler allowance.

Two simple completion models miss this target:

1. **Independent random cross-boundary matchings.** In the large-support
   approximation, if both defect densities are `q_t`, one fresh random
   matching leaves density `q_(t+1)=q_t*(1-q_t)`, starting at `q_0=1/4`.
   After 17 layers `q_17 ~= 0.0437`; expected high leakage is
   `q_17*delta ~= 0.0437*delta`, about 20 times the target. This
   model is diagnostic, not a lower bound for every fixed network.
2. **Independent exact Batcher blocks.** Sorting each block of 32 wires
   (16 from each boundary row) costs 15 layers. In one block, the signed
   defect count is a sum of 16 iid values `+1,-1,0` with probabilities
   `1/4,1/4,1/2`; the expected positive part is `1.119599...`. Across blocks
   this leaves about `0.06998*delta`, about 32 times the target. Two spare
   layers do not bridge that gap by this calculation.

Thus the 17-layer finisher would need a genuinely stronger structure: for
example, a multiway pooling step that gathers defects across much larger
regions, or a first-round profile promise that reduces `delta`. A generic
random matching family and small exact blocks do not suffice. The full
all-rank network still has to handle changing support intervals and all 63
cuts simultaneously.



## Matching-graph screen for localized repair

One way to make the remaining requirement precise is to model each of the 17
binary layers as a perfect matching between the two boundary rows. Their union
is a bipartite multigraph of degree 17. In the aligned iid profile, each upper
position is initially high-only with probability `1/4`, each lower position
is initially hole-only with probability `1/4`, and all other positions are
clean. A high defect can only be removed by meeting a hole; a high vertex with
no hole among its 17 neighbors is therefore a necessary residual defect for
this matching-only model. Its expected density is

```
(1/4) * (3/4)^17 = 0.0018792367...
```

This is not a general lower bound on arbitrary comparator networks: it assumes
the repair consists of cross-boundary matchings and uses the iid profile. It
does give a narrow design margin under this profile. Against the conditional
`0.0022*delta` stress threshold, the expected budget left for all
non-isolated failures is only about
`0.000321*delta`. Any successful 17-matching candidate must approach near
perfect defect-hole pairing on this random profile; merely spreading the
opportunities is not enough.

We screened a more locality-preserving family: 17 fixed cyclic shifts between
the boundary rows, with offsets sampled from `[-R,R]`, applied to iid
high-only/hole-only states on a long interval. Across 40 sampled schedules,
mean residual high-defect fractions were about `0.0481` for `R=32`, `0.0445`
for `R=256`, `0.0444` for `R=2048`, and `0.0449` for `R=8192`; best runs were
still about `0.042`--`0.046`. These are exploratory simulation results for
that schedule family, not proofs and not lower bounds. Local shifts preserve
the support interval up to endpoint effects, but do not come close to the
required pairing efficiency.

Within the restricted cross-boundary-matching model, the target remains a
fixed 17-layer schedule with expected high leakage at most `0.0022*delta` and
strong enough concentration for all columns and cuts. The following
within-row compaction screen tests the broader approach of moving defects
before pairing them.


## Fixed-edge-order diagnostic

In a cross-boundary-only repair, each comparator edge either removes one
high/hole pair or leaves both defects in place. Processing every edge in the
17-layer schedule therefore produces a maximal matching in the initial
bipartite graph induced by the high and hole sets: if an adjacent unmatched
pair remained, its comparator would have repaired it when processed. This
separates two issues: whether the degree-17 bipartite multigraph has a near-perfect matching
for typical defect sets, and whether its prescribed edge order finds one.

A small schedule-training diagnostic is now reproducible with
`matching_schedule_screen.py`. It uses 64 positions per boundary row and iid
Bernoulli-1/4 defect sets. For each layer after the first, it chooses a
permutation maximizing the number of repairs on a 12,000-sample training
corpus, then validates on 50,000 fresh samples. Seed `20261010` gave validation
residual `0.047394`; five independently sampled random schedules averaged
`0.051465`. The training residual was `0.041801`, indicating some overfit.
The trained schedule is only a small finite-size improvement and remains over
21 times the target. This is not evidence that all fixed schedules fail: it
only says this greedy distribution-training heuristic is inadequate. The
finite size also has noticeable random imbalance between the two defect counts.

## Random regular graph: capacity versus fixed order

The proposed discriminator was run with `matching_capacity_screen.py`: four
independent bipartite multigraphs, each formed from 17 random perfect matchings on 4,096
positions, and 500 samples per graph. Each sample chose exactly 1,024 high
positions and 1,024 hole positions independently on the two sides. This
balanced sampling removes finite-sample total-count imbalance. For each same
sample, the screen measured both the residual from the fixed 17-layer edge
order and the residual from a maximum matching in the induced graph.

Across the four multigraphs, mean isolated highs were `0.001840`--`0.001956` per
position. The fixed-order schedules left `0.043604`--`0.043679` high defects
per position. A maximum matching left `0.002501`--`0.002605` per position.
The conditional stress threshold `0.0022` is about 9 high defects at this
scale: graph capacity is close, though this random graph family misses the
threshold slightly; fixed-order
execution is about 20 times worse. This strongly identifies greedy edge order
as the bottleneck in this family, rather than a complete lack of graph
capacity.

The maximum matching is an offline, input-dependent benchmark; it is not a
17-layer fixed comparator network. The computation is a finite iid diagnostic,
not a lower bound on all 17-layer schedules. Within this matching-only family,
one would need a graph whose induced maximum matching is below target and a
fixed schedule that realizes nearly that matching without seeing the input.
The within-row compaction screen below tests a broader way around this
fixed-order obstruction. Locality across every supported interval and uniform
concentration over columns and cuts remain unchecked.


## Within-row butterfly compaction

The matching-only obstruction suggests moving defects before trying to pair
highs with holes. Consider a block of `N` positions, with independent states
high-only, hole-only, and clean, each position having probabilities
`1/4, 1/4, 1/2`. On each of the two boundary rows, use the same butterfly
schedule: for dimensions `t=0,...,r-1`, where `N=2^r`, compare every pair of
positions differing in bit `t`. Orient each row's comparators so its defect
indicator's OR goes to the lower-index wire and its AND to the higher-index
wire. This takes `r` layers in parallel on the two rows. A final cross-row
layer compares the aligned positions; it repairs exactly the locations where
both defect flags coincide.

The one-wire state distribution can be calculated exactly, without sampling.
At each butterfly dimension the paired wires depend on disjoint sets of
original positions, so their four-state distributions are independent. The
script [butterfly_compaction_screen.py](butterfly_compaction_screen.py)
propagates these distributions. Results are:

| Block size | Within-row layers | Including final cross layer | Expected high leakage per position |
| --- | ---: | ---: | ---: |
| `2^8` | 8 | 9 | `0.03751` |
| `2^12` | 12 | 13 | `0.01711` |
| `2^16` | 16 | 17 | `0.007920` |
| `2^17` | 17 | 18 | `0.006538` |

This beats the fixed cross-matching screen, but the 17-layer instance still
misses the conditional `0.0022` stress threshold by a factor of about 3.6. It is a genuine
within-row relocation mechanism, not a full solution.

There is enough mass-balance room in principle. For perfect compaction of both
rows, the only residual high defects would be `(X-Y)_+`, where at each position
`X-Y` has probabilities `+1,-1,0` equal to `1/4,1/4,1/2`. For a block of `N`
positions, `X-Y` has the law `Binomial(2N,1/2)-N`, so the exact ideal expected
residual per position is

```
(1/2) * binomial(2N,N) / 4^N
```

which is about `0.001102` at `N=65536`, below the conditional stress
threshold. Thus the observed `0.007920` is primarily a compaction-network
loss, not an unavoidable block imbalance. A 16-layer distribution-specific
compactor reaching `0.0022` would pass this stress test, but missing it does
not rule out the full construction unless the profile is shown reachable. In
either case, an iid block estimate must still be connected to actual
post-scramble states, concentration, support intervals, and all 63 cuts.

### Exhaustive placement of cross-row cancellation layers

I also tested whether the butterfly loss is mostly a bad placement of the
cross-row layer. For each `r=8,...,16`, retain all `r` butterfly dimensions
and distribute the remaining `17-r` cross-row cancellation layers among the
`r+1` gaps (before, between, or after butterfly dimensions). Repeating a
cancellation layer in one gap is redundant, so all distinct gap subsets were
exhausted. Exact four-state propagation gives the minimum leakage in this
restricted family:

| Block | Cross layers | Schedules checked | Best leakage | Best cross gaps |
| --- | ---: | ---: | ---: | --- |
| `2^8` | 9 | 1 | `0.029449` | `0,1,2,3,4,5,6,7,8` |
| `2^9` | 8 | 45 | `0.023036` | `0,1,2,3,4,5,6,7` |
| `2^10` | 7 | 330 | `0.018355` | `1,2,3,4,5,7,8` |
| `2^11` | 6 | 924 | `0.015239` | `1,2,4,5,8,9` |
| `2^12` | 5 | 1,287 | `0.012687` | `1,4,5,7,8` |
| `2^13` | 4 | 1,001 | `0.010668` | `1,4,7,10` |
| `2^14` | 3 | 455 | `0.009187` | `3,6,9` |
| `2^15` | 2 | 120 | `0.008041` | `3,8` |
| `2^16` | 1 | 17 | `0.007162` | `7` |

Gap `t` means after `t` butterfly dimensions. The best 17-layer member is
still over 3.2 times the target, and even the optimum gap placement improves
the original `2^16` schedule by only about 9.6%. This rules out layer placement
as the main repair: any substantial gain needs a different within-row
compaction network or a richer set of operations than whole-row butterfly
layers plus pointwise cancellation. Reproduce the exhaustive finite search by
running `python butterfly_compaction_screen.py --search-17`; it certifies only
the stated schedule family and iid block model.

### Unstructured random matching layers

As a first genuinely different topology, I sampled fixed networks whose each
layer is a uniformly random perfect matching. For each of three schedules on
256 wires, I sampled 5,000 iid initial ternary vectors, applied 16 comparator
layers, then measured high-only defects after the final cross-row cancellation.
With OR destinations chosen by each layer's random half split, leakage was
`0.048333`--`0.050530` per position (standard errors about `0.00033`). I also
oriented every comparator toward the lower endpoint in one fixed random total
order; leakage was `0.047259`--`0.048774`. Both are materially worse than the
exact best 17-layer butterfly/cancellation schedule at this block size,
`0.029449`.

This rejects unstructured random matchings as an off-the-shelf choice, not the
broader use of non-hierarchical layers: only three randomly generated networks
per orientation were sampled, with no topology optimization. The reproducible
screen is [random_compaction_screen.py](random_compaction_screen.py). A better
candidate should retain deliberate coarse-to-fine movement while changing how
mass is pooled within or across levels; purely random matchings erase too much
of the useful rank organization.

### Truncated bitonic network

I also screened a standard bitonic sorting network truncated after 16 layers,
followed by the cross-row cancellation. On 3,000 iid ternary samples per size,
the leakage was `0.04925` on 64 wires, `0.04922` on 256, and `0.04955` on
1,024 (standard errors `0.00092`, `0.00046`, `0.00024`). The 256-wire result
is well above the exact `0.029449` best in the 17-layer butterfly/cancellation
family. A generic merge-sort prefix therefore does not supply the missing
compaction either. Reproduce with
[bitonic_prefix_screen.py](bitonic_prefix_screen.py). Together with the random
matching result, this points toward a distribution-tailored construction that
deliberately coordinates coarse and fine ranks, rather than a generic partial
sorter.


## What finite sorter searches can contribute

Finite search is useful here if we optimize the *right* local contract.
[SorterHunter](https://github.com/bertdobbelaere/SorterHunter) evolves
full sorting networks and currently supports up to 64 wires; SAT-based
optimal-depth work gives certified finite sorters only at still smaller
scales (the cited method settles the remaining cases through 16 inputs).
These can supply candidate comparator templates or baselines, but their
objective is exact full sorting, not expected high-only leakage or the
cut-dependent repair slack. A specialized evaluator/search objective is needed.

There is also a hard scale mismatch if such networks are merely tiled. Even
perfectly sorting both defect rows independently in blocks of 64 positions
leaves an ideal count-imbalance floor of
`0.5 * binomial(128,64) / 4^64 = 0.03519` leakage per position, far above
the conditional `0.0022` stress threshold. To help asymptotically, a finite
gadget must be part of a multiscale construction that combines block output
profiles across larger scales; repeating independent finite blocks cannot do
it. A useful search objective should therefore record the full output profile
(or a certified transfer bound), not only the scalar leakage.


## Finite matching-layer search (iid proxy)

`finite_repair_search.py` searches fixed within-row perfect-matching layers for the three-state defect process, with one parallel cross-row cancellation layer. At 64 positions, 16 within-row layers plus one cross-row layer, a 300-step single-seed search produced training residual `0.021381` and independent validation residual `0.021379`. The repeated-butterfly baseline validated at `0.045250`; a random fixed schedule at `0.036368`. The schedule is saved in `results/finite-repair-64.json`. The small train/validation gap is evidence against obvious sample overfit for this one iid distribution, not a guarantee across profiles.

This is not yet the right acceptance objective for the 107-layer scheduler slot: the proxy samples independent exact-quarter-density defect sets, while the actual interface is a deterministic, cut-dependent count requirement over all admissible intermediate states, and probability enters only in proving which states the fixed scrambles can reach. The iid screen improves the finite topology baseline, but remains about 9.7 times the conditional `0.0022` stress threshold and does not certify any localized-band bound.

The next useful finite-search step is therefore to make the evaluator mirror the repair contract: encode small instances of the cut-indexed cumulative-tail constraints, search for worst-case inputs against each candidate schedule (or derive a compact adversarial witness), and separately generate reachable samples from the actual first-scramble model. Do not optimize a scalar iid leakage average and infer a scheduler guarantee. The numerical slack retuning in [central bulk feasibility](central-bulk-feasibility.md) is currently the more direct path to validate against the existing 631-layer candidate; the finite topology search has not yet found a sub-1000 construction.

## Exact small-profile contract evaluator

`cut_contract_screen.py` enumerates height profiles `c in {0,...,m}^n` with exact mass `sum(c)=i*n`, optional `sum |c_j-i| <= L_1`, and optional two-sided overflow bounds beyond a band. It applies one fixed row-wise permutation per row, then a fixed physical comparator network, and computes `Q_*`, `Q_R`, and the exact integer reserve `cap-Q_*` profile by profile. The same scramble and repair are tested across all requested cuts. The row-wise scramble image is exact for each listed profile; whether the upstream fixed network reaches every profile in the chosen L1/tail envelope remains a separate question.

A finite search on `m=8,n=4`, cuts `i=2,4,6`, `L1<=16`, band half-width `W=1`, tail bounds `U,D<=4`, and synthetic target cap `4` enumerated 781 cut-profile cases. Identity repair exceeded the cap by 1, 2, and 1 at the three cuts. A 4-layer arbitrary perfect-matching network found by worst-case search passed all 781 cases; exact re-evaluation gives minimum cut slacks 1, 0, and 1 and maximum repair defect 3. Its schedule is `results/toy-repair-search-8x4.json`. This is an exact finite result for the specified toy envelope and fixed scramble, not a scaled scheduler theorem.

The unrestricted search can use protected rows. When constrained to rows `2:6`, 500 four-layer proposals and 800 six-layer proposals both left a worst excess of 1; this is only a search outcome, not a lower bound. Full column sort, at depth 8 in this toy geometry, has zero defect and passes. The synthetic cap and tiny geometry make these data useful to validate the contract/search loop, not to estimate the asymptotic coefficient. Reproduce with `cut_contract_screen.py`; add `--confine-rows lo:hi` to enforce a repair region and `--search-depth` to search a common network against the entire finite profile set.
