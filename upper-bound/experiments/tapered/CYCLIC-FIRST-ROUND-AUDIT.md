# Cyclic first-round scramble: smaller-row B2 audit

Status: width-16 construction and padded witness are now formalized in the
scratch package. This repairs the local scale mismatch for live sizes from
`2^34` up to (but not including) `2^38`; it is not yet installed in the
all-stage scheduler or global outsider induction. It does not give a
uniform-in-`n` first-round F provider.

## Exact discrepancy calculation

Use the row permutation `σ_r(k) = k + r (mod n)` in zero-based row
coordinates. The source column that lands in destination column `j` on row
`r` is then `k = j-r (mod n)`. Write `h_k = (c k).val` and `t = m-r`, so
source column `k` is occupied exactly for `1 ≤ t ≤ h_k`. For fixed `j`, as
`k` ranges over the columns, the residues `m-j+k (mod n)` range over every
residue once. Thus the post-scramble height `H_j` is a sum of `n` terms, one
for each `k`, each counting integers `t ∈ [1,h_k]` in one residue class mod
`n`. Each term differs from `h_k/n` by strictly less than one. Consequently,
if `Σ_k h_k = n i`,

`|H_j - i| < n`, hence `|H_j-i| ≤ n-1`.

This is a direct consequence of the row/column indexing in
`MatrixBridge.rowScrambleWirePerm_apply`; check the chosen shift sign when
encoding it in Lean. It does not assume any ordering of the column heights.

Since column sorting preserves this multiset of heights, the intermediate
exact-mass state has

* `excessAbove(c₁,i) ≤ n(n-1)`;
* all heights in an interval of width at most `2(n-1)`;
* the Bernoulli variance proxy `Σ_r p_r(1-p_r) ≤ (n-1)/2`, because only
  rows between the smallest and largest heights can be partial, and each
  summand is at most `1/4`.

The final variance bound is much stronger than feeding the excess estimate
through `variance_le_of_excess`.

## B2 rate screen for `n = 16`

For `n=16`, the deterministic first-stage bounds are `excess ≤ 240` and
`V ≤ 7.5`. In the exact-mass Bernstein cell estimate, use the complemented
tail witness (`|S| ≤ n/2`) and `λ=1`. With `d=2^-21`, the exponent per `n`
is at least

`d*m/2 - (1/2)*(13/18)*7.5`.

The state/subset entropy per `n` is about `log(2(m+1))`. At `m=2^27`, the
rate side is about `32 - 2.71 = 29.29`, versus entropy about `18.02`; this
leaves over 11 natural-log units per column before the small orientation
factor. Thus the local two-round B2 rate appears to work at `m=2^27`, far
below `2^34`, if the exact-mass/complement union can be re-used with this
deterministic first stage. The intended bag scale `m=2^30,n=16` has much more
slack. This is a hand calculation, not a checked certificate.

## Limitation: not a uniform first-stage F construction

The additive discrepancy `n-1` is not bounded independently of `n`, so it
cannot establish `F2SmallRank` for every `n ≥ 16`. In fact there are explicit
large-`n` counterexamples. Fix one output column `j`, and choose its source
columns to have the distinct residues `r=g1+1,…,g1+K` modulo `n`, with height
`h=r`; give the other columns height zero. Each selected column contributes
one in a row strictly above the bottom `g1`. With `K=80,000`, `n=2,000,000`,
and `m≥n`, the total input mass is
`K*(2*g1+K+1)/2 = 7,393,320,000`, below
`floor((128/4095) * 131040 * n) = 8,192,000,000`, but the selected output
column receives `80,000` top-row ones, exceeding the standard SR threshold
`f-g1=78,624`. So the cyclic scramble cannot simply replace the published
random first scramble uniformly in `n`.

For fixed `n=16`, SR and R1 hold for **every** first-round scramble: Lean proves
`jmax(16)=65,536`, below the SR threshold 78,625, the R1(a) threshold at least
104,834, and the R1(b) threshold at least 86,416. Thus the cyclic map and its
repository-defined flip satisfy SR/R1 without using their cyclic structure.
The remaining R2 scramble is chosen jointly with the B2 second-round
condition; the failure fractions `1/1000` and `1/10000` leave ample union-bound
slack.

## Formal B2 rate gate closed conditionally

`CyclicBulkRate.lean` kernel-checks the exact-mass second-round rate at
`m≥2^30`, with first-round error budget `E1=2^-24`, target `d=2^-21`, and
`λ=1`. It proves failure fraction at most `1/1000`, and proves that any
first-round scramble satisfying `FirstRoundCap16` (plus the same cap for its
flip) yields a two-sided semantic B2 pair. The rate has wide slack: the
certified logarithmic cost is paid by a coefficient at least `2^-23`, while
the exact-mass Bernstein rate is larger. This check does not formalize the
cyclic shift itself and therefore remains conditional on the cap theorem.

`CyclicFixed16SRR1.lean` kernel-checks the exact-mass argument that SR, R1(a),
and R1(b) hold for every width-16 scramble. `CyclicFixed16Provider.lean` then
combines the B2 failure share `1/1000` and R2 failure share `1/10000`, applies
the flip pigeonhole, and proves that the actual cyclic first scramble has a
single second scramble satisfying semantic B2 and standard F2 in both
orientations for `m≥2^30`. The focused Lean check passes.

## Next proof gate

`CyclicPermScratch.lean` now defines the row shift on `Fin 16` and kernel-checks
its modulo action. `CyclicResidueCount.lean` kernel-checks the generic
interval bound, including translated intervals: a fixed residue occurs at
most `ceil(length/16)` times. A small Python certificate under the ignored
local helper directory checks the 256 short-tail cases and 524,288 direct
count instances; the Lean lemma uses a quotient-block injection, so its
conclusion holds for every interval length. `CyclicCapBridge.lean` now
kernel-checks the source-column expansion of each destination total and sums
the 16 interval bounds, proving the exact-mass 15-cap for `cyclicScramble16`.
`CyclicFlipScratch.lean` mirrors the repository definition
`fun r => Fin.revPerm * σ (Fin.rev r) * Fin.revPerm`; it kernel-checks that
the flipped cyclic map is an affine shift by `1-m` modulo 16 and proves its
exact-mass 15-cap using the same interval argument. `CyclicFlipBridge.lean`
imports the repository `FlipSpec`, proves the mirrored definition equal to
the exported `flipScramble` by `rfl`, and transfers the cap theorem to that
actual identifier. The bridge has passed a focused Lean check. The ignored
Python certificate additionally checks the flip formula on 6,016
representative row/column cases across every residue of `m` modulo 16.
`CyclicSmall16F2Params.lean` tunes the width-16 fringe to `f=16000` and
`J=9000000`; at this width, SR/R1/R2n checks are deterministic after the B2
pair is selected. `CyclicSmall16Provider.lean` proves a same-pair,
both-orientation truncated-fringe/B2 result. `CyclicSmall16PaddedWitness.lean`
chooses `retainedRows=(a-1)/16`, handles exact multiples without a padding
boundary error, and packages a physical padded network for every
`2^34 <= a < 2^38`. It proves depth at most 1890, both arbitrary-cut crossing
bounds, both restricted rare-rank estimates, and the low-fringe fit from the
minimum scheduled up-flow. The ordinary kernel now accepts a provider-supplied
fringe coefficient, and the `1/9,000,000` scalar fits its recursive budget.
Focused direct Lean checks passed for these modules.

`AdaptivePaddedWitness.lean` now selects the tuned provider below `2^38` and
the standard provider at or above it. Both have a common actual-network,
crossing, high/low rare-rank, and low-fit contract; the standard `1/86M`
estimate is weakened to `1/9M` so the recursive coefficient is uniform.
The remaining local integration is to instantiate the high-suffix fit,
cohort bound, and low-prefix fit from the actual scheduled split at each bag,
then turn those estimates into the ordinary kernel's stranger-count fields.
The small-size construction remains fixed at 16 columns.
