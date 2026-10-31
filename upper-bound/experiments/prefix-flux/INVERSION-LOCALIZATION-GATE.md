# Inversion potential as a localization gate

2026-10-21. Codex (GPT-6). Exact combinatorial lemmas and a conditional
depth calculation; no new sorting bound is claimed.

## Exact link to prefix flux

Let `w` be a Boolean word of length `N` with `q` zeros. Write `Z(r)` for the
number of zeros in positions `[0,r)`, and define the prefix defect

```text
F(r) = min(q,r) - Z(r),   0 <= r <= N.
```

Then

```text
sum_{r=0}^{N-1} F(r) = inv(w),
```

where `inv(w)` is the number of pairs `i<j` with `w[i]=1,w[j]=0`.
Indeed, if the zero positions are `z_0<...<z_{q-1}`, then zero `z_k` has
exactly `z_k-k` preceding ones, so `inv(w)=sum_k(z_k-k)`. Also
`sum_r Z(r)=sum_k(N-1-z_k)`, and subtracting this from
`sum_r min(q,r)` gives the same expression. Thus the pointwise global
prefix-flux state already tracked in `PROFILE-GATE.md` has an exact aggregate
potential interpretation.

This does not show that the D2 stage contracts `inv`; prefix dominance only
shows it is nonincreasing.

## Small inversion count localizes every error

Every misplaced one at position `p<q` contributes at least `q-p` inversions:
there are at least `q-p` zeros after it. Every misplaced zero at `p>=q`
contributes at least `p-q` inversions from preceding ones. Consequently, if
`inv(w)<=I`, all wrong bits lie in the interval

```text
[max(0,q-I), min(N,q+I+1)),
```

of length at most `2I+1`. Outside it, the word is exactly `0*1*`. This gives
a positional localization contract from an aggregate potential; it is
stronger than merely bounding the number of wrong bits.

## Fixed cleanup and the coefficient gate

Suppose a fixed prefix network `P_n` has depth
`p*log2(n)+O(1)` and, on every Boolean input, leaves inversion count at most
`n^theta`. By the preceding lemma this leaves a contiguous dirty interval of
length at most `2*n^theta+1`, with zeros before it and ones after it. The
interval may depend on the input; the network may not.

The interval can be cleaned by a fixed recursive schedule. Let `B` be the
next power of two at least `2*n^theta+1`. For large `n`, partition into
`2B` chunks; if the final remainder is shorter than `B`, join it to the
previous chunk. Thus every chunk has length at least `B`, and every chunk
with two neighbors has length at least `2B`. Recursively sort every chunk in
parallel, then merge the suffix and prefix halves across each chunk boundary.
The seam windows are disjoint and each merge costs `log2(2B)+O(1)`. If the
dirty interval lies in one chunk, sorting that chunk fixes it. If it crosses
a boundary, its at most `B` bits imply that after chunk sorting all ones in
the left chunk and zeros in the right chunk lie in the seam halves; the seam
merge fixes them. Sorted surrounding portions remain in order. Bounded small
`n` cases are handled exactly as base cases.

If `F(n)` is the resulting exact sorting depth, this gives

```text
F(n) <= p*log2(n) + F(4*n^theta+O(1)) + theta*log2(n) + O(1),
limsup F(n)/log2(n) <= (p+theta)/(1-theta).
```

For the baseline UB-42 prefix budget `p=292.5`, reaching at most300 requires

```text
theta <= (300-292.5)/301 = 15/602 ~= 0.0249169.
```

Strictly below300 requires strict inequality (or some slack in `p`). This is
a concrete new terminal gate for UB-42: prove the actual priced prefix
schedule drives the global inversion count below `n^theta` for some
`theta<15/602`, then use the fixed cleanup above. The current rank-profile
tests do not establish such a bound; the exact root, provider, and all-depth
contraction remain open. If the prefix stage only gives a looser inversion
exponent, the displayed budget rejects this cleanup route at `p=292.5`.

The parameter screen has a more favorable but still conditional `(3,3,2)`
candidate: row height `2^13`, three-sort depth273, stage rate1, hence
`p=273`. Its cleanup gate is

```text
theta <= (300-273)/301 = 27/301 ~= 0.089701.
```

This gives substantially more room and is the better UB-42 parameter target
if the new row-height-13 provider and all-depth flow bounds can be proved.
The depth-30 fringe ratio and the sparse adversary runs below are finite
screens only; they do not establish either prerequisite.

## Finite ordered inversion screen

`sparse_probe.py` now accepts D2 parameters and row height and reports the
exact inversion count of its interval-encoded trace without expanding the
ambient word. The interval formula was exhaustively checked against all
Boolean words through length11. It asserts inversion nonincrease at every
oracle stage and prints a compact summary by default (`--verbose` retains the
full histories).

For `(3,3,2)`, row height8192, scale8192, threshold1/3, root error fraction
`10^-7`, and the assumed rank-tail oracle, the initial-band trace gives:

| flow depth | ambient `N` | final inversions | `log_N(inv)` | remaining wrong bits |
|---:|---:|---:|---:|---:|
| 12 | `2^49` | 46,225 | 0.3163 | 430 |
| 20 | `2^73` | 1,669,264 | 0.2832 | 2,584 |
| 24 | `2^85` | 3,845,521 | 0.2573 | 3,922 |

Each trace has zero wrong bits in every noncrossing terminal native block;
the displayed errors lie in the threshold-crossing block. At depth12, outer
and left-end initial bands also reached that terminal condition, with final
inversion counts834,415 and293,690 respectively. The three depth-specific
exponents trend downward but are far above `27/301`; the final counts are
small relative to `N`, not yet a certified power law. The oracle selects
input-dependent port outputs under assumed local tails, so these traces are
discovery evidence only and do not prove a fixed provider or a uniform
inversion bound.

## Candidate-parameter phase stress

I reran the relational oracle for the actual 13-row candidate parameters:
`(x,y,z)=(3,3,2)`, row height8192, scale8192,
`eps_F=1/3`, `delta=18/49816`, `eps_B=19/2000`, root band fraction`10^-20`,
and the mandatory first sort. For the band initializer, the final inversion
counts at depths24,32,48,56,64,72,80 are respectively
`839056, 341056, 559504, 1671849, 9216, 484, 2944656`. Their exponents
`log_N(inv)` are respectively
`.2315, .1686, .1216, .1142, .0642, .0389, .0849`.
The cleanup threshold is `27/301 ~= .08970`; thus depths64,72,80 pass this
finite trace screen while depths24 through56 do not. The nonmonotone counts
show substantial phase effects, so the later passes do not establish an
eventual bound.

At depth64, the same oracle with different initial profiles gives final
inversions384000 (`outer`, exponent`.09049`), 262080 (`left`,`.08780`), and
131136 (`right`,`.08293`). The outer trace narrowly misses the cleanup gate;
the stripe initializer hit a HiGHS model error and has no result. At depth80,
the outer trace gives5517680 inversions, exponent`.08852`, again just below
the gate. These adversarial profiles still use input-dependent choices, not
one fixed provider, and assume an exceptionally strong root-band premise.
Increasing the band root-error fraction from`10^-20` to`10^-7` at depth80
still gives only1151329 inversions, exponent`.07958`, under this oracle. Thus
the trace's low residual is not sensitive to that sampled relaxation of the
root premise. They motivate an all-depth, phase-sensitive inversion
recurrence but supply no theorem. Reproduce with `sparse_probe.py`, setting `--params 3 3 2`,
`--row-bits 13`, `--scale 8192`, `--eps-f 1/3`, `--delta 18/49816`,
`--root-eps 1/100000000000000000000`, and the stated depth/initializer.

## Phase diagnostic at larger depths

I instrumented `probe(..., trace_stages=True)` to record the affected schedule
roles and local bag at every stage. For the same band parameters above, the
terminal samples are:

| `d` | `log2 N` | stages | final inversions | `log_N(inv)` | mixed wrong bits |
|---:|---:|---:|---:|---:|---:|
| 80 | 253 | 225 | 2,944,656 | 0.08494 | 3,432 |
| 96 | 301 | 273 | 2,755,600 | 0.07108 | 3,320 |
| 112 | 349 | 321 | 314,721 | 0.05233 | 1,122 |
| 128 | 397 | 369 | 409,600 | 0.04696 | 1,280 |
| 144 | 445 | 417 | 3,489,424 | 0.04884 | 3,736 |

Each finishes with zero wrong bits in every noncrossing terminal native block.
All five sampled exponents are under `27/301`, but the residual count is
nonmonotone, so this does not imply an eventual power bound. The d=80 stage
trace reveals an exact two-phase port motif for the one affected `botDesc`
bag. At level `i`, the sampled visits occur at `t=3i-4` and `t=3i-2`; the
next strong visit is at level `i+1`, stage `t+3`. Across all 149 such events
in this trace, the normalized port sizes have exactly these two shapes:

| phase | up port | two edge child blocks | each of six interior child blocks |
|---|---:|---:|---:|
| strong (`t=3i-4`) | `15/256` | `49/512` | `1/8` |
| weak (`t=3i-2`) | `15/4096` | `1009/8192` | `1/8` |

The strong phase coincides with the large observed inversion drops; the weak
phase and intervening stages often give plateaus, and some strong visits also
act as the identity. In every recorded `botDesc` event, the bag's zero count
`H` equals the number `P` of its incoming zeros on global wires below the
threshold. Selected late strong visits show the contraction scale:

| stage / level | wrong bits before | wrong bits after |
|---:|---:|---:|
| 197 / 67 | 3,022,902,283,624 | 275,632,599,704 |
| 200 / 68 | 275,632,599,704 | 754,692,760 |
| 209 / 71 | 754,692,760 | 50,613,608 |
| 212 / 72 | 50,613,608 | 16,495,256 |
| 215 / 73 | 16,495,256 | 281,960 |
| 221 / 75 | 242,328 | 19,816 |
| 224 / 76 | 19,816 | 3,432 |

This suggests a two-phase weighted recurrence: bound the defects routed into
the up port and eight child blocks by the appropriate rank-tail contracts,
then compose from one strong visit to the next. Some strong visits leave the
error unchanged, so a uniform proof needs an envelope over the exact phase and
incoming profile, not just a per-stage contraction factor. It must also cover
branches not hit by this trace and the initial/root errors. Since `choose`
still selects local outputs as an input-dependent oracle, these data remain
discovery evidence, not a bound for the fixed separator.

The full reachable flow has many state types at the same schedule phase, so
the two trace shapes are not universal constants. The general state-sensitive
allocation and block formulas are given in `D2-PHASE-IDENTITIES.md`; setting
`G=low=high=0` recovers the trace's two shapes.

The next paper calculation is now specific. For each strong/weak visit, take
the 13-row uniform tail operator `Phi` from `PROFILE-GATE.md` and bound the
eight child-port and up-port threshold defects as functions of the incoming
column tail profile `T_c(b)`. Transfer those nine bounds through the exact
static-wire port intervals to the next strong visit, retaining the phase
(`15/256` versus `15/4096`) and partial-row remainder. The desired terminal
statement is a uniform global inversion bound `inv <= N^theta` with
`theta < 27/301`, for every input and one fixed common-witness separator.
The finite trace gives the phase geometry and a candidate state variable; it
does not yet give a closed recurrence, arbitrary root initialization, or a
uniform local provider.

Reproduce the table with `sparse_probe.probe` at `d=80,96,112,128,144`,
`horizon=10**9`, `root_eps=1/10^20`, `eps_b=19/2000`, `eps_f=1/3`,
`delta=18/49816`, `threshold=1/3`, `initial='band'`, `scale=8192`,
`params=(3,3,2)`, and `row_bits=13`.

## Alignment/local-defect split across initial profiles

Using the same candidate parameters at depth64, I split inversion into the
bag-sorted alignment term and the within-bag weighted-defect term at every
stage. For `outer`, alignment is zero at initialization and all stages; the
final inversion count is384000. For `left`, it is initially zero, is nonzero
only at stages1 and2, and returns to zero thereafter; the final inversion
count is262080. For `right`, the same two-stage transient occurs and alignment
then stays zero; the final inversion count is131136. The `band` depth80 trace
also has zero alignment throughout. All four traces end with zero wrong bits
in noncrossing terminal blocks.

This rules out using identically-zero alignment as an invariant for all
profiles, but suggests a possible decomposition of proof work: bound the
startup alignment transient (or its total contribution), then prove a uniform
later recurrence for local weighted defects. The traces are still from the
input-dependent relational oracle, with an assumed tiny initial band; they do
not establish a fixed-provider statement or show that the transient is
uniformly bounded independently of depth. Reproduce the d64 comparison by
calling `sparse_probe.probe` with the same parameters as above, `d=64`, and
`initial` in `outer,left,right`, with `trace_stages=True`.

I also measured the startup peak for `left` and `right` at depths32,40,48,56,
and64, keeping `root_eps=10^-20` and all other parameters fixed. The peak
alignment always occurred at stage1. Its normalized logarithm is already
large, rising from about1.34 at depth32 to1.65 at depth64; the corresponding
final inversion exponents fall from about.18--.19 to about.083--.088. Exact
sample values:

| `d` | `log₂ N` | left peak `log_N(A)` | right peak `log_N(A)` | left final `log_N(inv)` | right final `log_N(inv)` |
|---:|---:|---:|---:|---:|---:|
| 32 | 109 | 1.3484 | 1.3392 | 0.1890 | 0.1799 |
| 40 | 133 | 1.4660 | 1.4584 | 0.1544 | 0.1619 |
| 48 | 157 | 1.5476 | 1.5412 | 0.1335 | 0.1272 |
| 56 | 181 | 1.6076 | 1.6020 | 0.1147 | 0.1202 |
| 64 | 205 | 1.6535 | 1.6486 | 0.0878 | 0.0829 |

Thus an argument that simply charges startup alignment as a small additive
error cannot work for this root premise: the transient is much larger than
the target sublinear terminal potential. Any viable recurrence must absorb
and contract this large initial alignment together with local defects. The
decreasing terminal exponents are encouraging diagnostics, but these traces
remain oracle-selected and finite; they do not prove a contraction envelope.

## Additional depth-200 stress traces (2026-10-30)

Using the exact command parameters above at depth 200, the band initializer ended with 556,516 inversions (exponent 0.03114), and the outer initializer ended with 2,499,100 inversions (exponent 0.03467). Both runs reported 6,099,968 compressed states and 1,492 mixed wrong bits in the terminal block, below the conditional cleanup exponent 27/301. These deeper traces improve the finite stress evidence for these two initial profiles; they still use the input-dependent relational oracle and its assumed local/root contracts. They establish no fixed separator, all-input recurrence, or asymptotic inversion bound.

## Affected-sender sparsity gate (2026-10-30)

I instrumented the same `sparse_probe.probe` traces with `trace_stages=True`
and counted the number of affected sender bags at every stage. At depth80,
scale8192, parameters `(3,3,2)`, and the same root band (`root_eps=10^-20`),
first-sort restriction, moderate tail, and `eps_b=19/2000`, `eps_f=1/3`,
`delta=18/49816`, the results are:

| initializer | stages | max affected senders in one stage | stages with more than one | final inversion exponent |
|---|---:|---:|---:|---:|
| band | 225 | 1 | 0 | 0.08494 |
| outer | 225 | 2 | 1 | 0.08852 |
| left | 225 | 2 | 3 | 0.08364 |
| right | 225 | 2 | 3 | 0.08550 |

The FlowDAG had 376,268 interned states. This supports a useful proof
hypothesis: error support may follow one main sender per stage, with only a
bounded split near a phase boundary. It does not establish that hypothesis
for arbitrary inputs; the oracle still chooses outputs input-dependently and
uses a tiny root band plus the assumed local-tail contract. A depth200 rerun
was stopped before returning a result when it drove system memory below
250 MB; no depth200 sparsity evidence is claimed.

The next high-value paper gate is therefore a universal **support branching
lemma**: starting with an interval error support, prove from the fixed D2 port
maps and common dirty-band provider that each stage sends it to at most two
active senders, with the exceptional split phases identified exactly. If the
lemma fails for an arbitrary admissible profile, retain a weighted count of
support components instead. This attacks the spatial recurrence directly and
could turn the observed `O(log n)` support into polylogarithmic inversion,
which is below the `theta < 27/301` cleanup threshold. The current finite
oracle table is motivation only, not evidence that the lemma is true.
