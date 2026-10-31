# Amplification kill test (LB-35)

Claim labels:

- **[proved]** a complete argument here (not kernel-checked; no Lean was added).
- **[hand]** a hand-level argument with a step left informal.
- **[numeric]** a finite computation or sampled run, with no asymptotic force.
- **[published]** a cited result.
- **[conjecture]** a reading of the data.

## Verdict

**The amplification route does not beat 3.2706, and nothing here proves a
coefficient above it.** There are three results, at different strengths:

1. **Sound influence potentials are dead. [proved, one step hand]** The only
   sound per-layer growth bound known is the sum rule. Propagated, it equals the
   formula's leaf count, which is already far above `sqrt(n)` on the barrier
   schedule. Such a potential adds nothing to Kahale (§2).
2. **Middle sharpness can be added at no depth cost on every tested size.
   [numeric]** A hybrid with no extra depth repairs LB-33's defect on the
   *actual* network, not just in the independence model. At `d = 80`,
   `n = N_d = 393913`, the wires that are both sharp and correctly placed go from
   **2.2% on the barrier to 99.4%**. Heights and per-wire relaxations pass at
   `N_d` through `d = 80`. The pair relaxation is confirmed through `d = 56`
   (§4).
3. **This is not a proved rate barrier. [numeric]** The hybrid is one greedy
   heuristic. Its sharpness trend extrapolates to a coefficient of about 4.3, and
   meets `N_d` only near `d ~ 180` (§5). That is an upper estimate of what
   schedules need, so it gives no lower bound. It also does not show that
   amplification is free asymptotically.

**Correction to LB-33.** LB-33 called the barrier's failure an amplification
deficit with `c ~ 0.25`. That holds at the `sqrt(n)` scale only. Repairing it
drops the sharpness deficit to about 0.075 bits of `n` per stage, but *exact*
sorting of random inputs still lags `N_d` by about **0.21** bits per stage.
Structured inputs stay wrong by about 4% of `n` at every tested depth (§5).
Sharpness was the visible defect, not the only one.

**Assessment.** 3.5 looks out of reach with current techniques. The proposed
inequality (§6) needs a growth bound below the read-once rate on a non-read-once
object, and no such bound exists. A formula-only proof of 3.5 would need a
monotone majority formula bound of `n^3.5`, against a known `n^2` (§8).

## 1. Setup

The schedule family is in
[`kahale_amplification_kill.py`](../lower-bound/experiments/scripts/kahale_amplification_kill.py).
It runs the LB-02 barrier schedule for `d - K` stages. In the last `K` main
stages, a band of wires drops its barrier comparators and gets a new matching.
Two odd-even cleanup layers follow, so the total depth is `d + 2`, as in LB-24
and LB-33. The script asserts the width rule (W) for the total depth and disjoint
comparators in every layer.

Band rules:

| Rule | Matching |
|---|---|
| `drop` | none |
| `remix` | odd-even transposition |
| `bfly` | cycling butterfly: Valiant's alternating tree on wires with alternating index bits |
| `zadj`, `zq` | equal-height pairs, by index or by independence-model `q(1/2)` |
| `zh` | the barrier's halves, matched by closest curve |
| `zs`, `qs` | `zq`-style, keeping only pairs whose orientation agrees with position |
| `tr` | see below |

**Rule `tr`.** Each stage, sort the band's wires by mean rank, estimated on 64
design permutations of the actual network. Pair consecutive wires, dropping pairs
wider than (W) allows. Evaluation uses fresh permutations (a different seed), so
the results are not fit to the design sample.

**Metrics.**

- `sharp`: `std(R_i) <= sqrt(n)/2`, so the wire's width is within a constant of
  the sorted width.
- `placed`: `|mean R_i - i| <= sqrt(n)`.
- `sp`: the fraction of wires that are both.
- `exact`: the fraction of fresh permutations sorted completely.

Placement has to count. **[proved]** A standard network fixes the sorted input,
so any non-identity output relabeling fails on that input. A sharp but misplaced
wire cannot be repaired afterwards. That is why the early hybrids, though sharp,
are not a pass.

## 2. Sound influence bounds cannot bind

**[proved]** For monotone `f, g` under `mu_p`, we have
`q_{f and g} + q_{f or g} = q_f + q_g`. By Russo-Margulis,

```text
I(f and g) + I(f or g) = I(f) + I(g),      hence  I(out) <= I(a) + I(b).
```

So influence is exactly conserved across a comparator and total influence stays
`n`. One wire grows by at most a factor 2 per layer, or 4 per two layers. An exact
rational check on 200 random pairs of monotone functions on 7 variables at
`p = 3/10` found no failures.

**[proved]** Propagating the upper bound `U_out = U_a + U_b` from `U = 1` makes
`U_w` exactly the leaf count of the wire's formula, at most `2^d`.

**[hand]** Sorting needs `I(f_mid) ~ sqrt(n)`, which is `(1/2) log2 n` doublings.
The barrier's early stages are essentially fully active, so its middle wires have
leaf counts well above that. A potential built on the sum rule therefore passes
on the barrier itself, with no hybrid needed.

**The gap the ticket asks about.** The read-once rate is `4/phi^2 = 1.528` per two
layers, or `2/phi` per layer, at the fixed point of `1 - (1 - x^2)^2`. That is
**not a bound on networks**. **[hand]** Dependent inputs can reach up to 2 per
layer, and read-once is a special case of a network, not a limit on one.

**[proved]** `log2(2/phi) = 1 - log2 phi = 1/c`, with `c = 3.27056`. So read-once
sharpness to `n^(-1/2)` needs exactly `(c/2) log2 n = 1.635 log2 n` layers. The
factor `c/2` is an identity, not a numerical coincidence.

## 3. Idle slots are not enough, but a blind window exists [numeric]

The barrier has almost no idle slots to hide amplification in. So the ticket's
literal plan falls short:

| `d` | `n` | middle-half utilization | idle tail / `log2 n` |
|---:|---:|---:|---:|
| 48 | 738 | 0.934 | 0.315 |
| 56 | 3459 | 0.910 | 0.426 |
| 64 | 16530 | 0.890 | 0.500 |
| 72 | 80209 | 0.875 | 0.553 |

But most of those comparators are not needed by the relaxations. Delete every
comparator touching the middle half in the last `K` main stages, and put nothing
in their place. The heights and wire checks still pass up to `K_blind`:

| `d` | 40 | 48 | 56 | 64 | 72 | 80 | 96 |
|---|---:|---:|---:|---:|---:|---:|---:|
| `log2 n` | 7.33 | 9.53 | 11.76 | 14.01 | 16.29 | 18.59 | 23.22 |
| `K_blind` | 21 | 26 | 29 | 32 | 37 | 39 | 46 |
| `(d - K_blind)/log2 n` | 2.59 | 2.31 | 2.30 | 2.28 | 2.15 | 2.21 | 2.15 |

The binary search assumes monotonicity in `K`. The hybrids below were verified
directly at the `K` quoted.

The pair relaxation's blind window is a few stages shorter. `drop` passes at
`K = 23` and fails at 24 for `d = 48`. It passes at 26 and fails at 28 for
`d = 52`.

**Read-once budget.** The window offers `0.306 K_blind` bits of width. Compare
that with what the middle wire still needs at time `d - K_blind`:

| `d` | 48 | 56 | 64 | 72 | 80 |
|---|---:|---:|---:|---:|---:|
| width needed (bits) | 0.75 | 1.61 | 2.54 | 3.58 | 4.60 |
| read-once budget (bits) | 7.95 | 8.87 | 9.78 | 11.31 | 11.93 |
| surplus (bits) | 7.20 | 7.26 | 7.24 | 7.73 | 7.33 |

The surplus is flat over this range. Asymptotically it is undecided, because the
slopes of budget and need are too close to separate from this data. **No
frozen-window obstruction is claimed.**

**[hand]** The only rigorous constraint is fan-in. A wire needing certificates of
size about `n/2` must have been active for `log2 n - O(1)` stages. The observed
`~2 log2 n` is a property of this family, since a partner's large certificate can
make one output jump by more than a doubling.

## 4. The hybrid works at `N_d` with no extra depth [numeric]

This table uses rule `tr` on all wires (`frac = 1.0`), against the barrier. Both
are at `n = N_d`, depth `d + 2`, on fresh permutations.

| `d` | `n` | `K` | heights, wire | pair | `sp` barrier | `sp` hybrid | `exact` | wrong wires | median `std / sqrt n` |
|---:|---:|---:|---|---|---:|---:|---:|---:|---:|
| 40 | 161 | 20 | pass | pass | | 1.000 | 1.000 | 0.000 | 0.000 |
| 44 | 344 | 22 | pass | pass | | 1.000 | 1.000 | 0.000 | 0.000 |
| 48 | 738 | 20 | pass | pass | 0.984 | 1.000 | 0.670 | 0.002 | 0.002 |
| 52 | 1593 | 22 | pass | pass | | 1.000 | 0.000 | 0.016 | 0.005 |
| 56 | 3459 | 28 | pass | pass | 0.285 | 1.000 | 0.000 | 0.030 | 0.004 |
| 64 | 16530 | 32 | pass | not run | 0.133 | 1.000 | 0.000 | 0.173 | 0.005 |
| 72 | 80209 | 36 | pass | not run | 0.047 | 0.9999 | 0.000 | 0.546 | 0.006 |
| 80 | 393913 | 36 | pass | not run | 0.022 | 0.994 | 0.000 | 0.902 | 0.016 |

Samples were 512 for `d <= 52`, 256 for `d = 56, 64`, 128 for `d = 72` and 64 for
`d = 80`. The barrier's `d = 48` value is on 256 samples. At `d = 80`, `K = 40`
fails the heights and wire checks. The pair relaxation fails on `tr` at
`d = 48, K = 26` and at `d = 52, K = 26`, so its window is shorter there, as with
`drop`.

The design sample is not the limit: `M = 512` at `d = 56`, `K = 28` only moves
wrong wires from 0.030 to 0.018.

So **amplification needs no extra depth at `N_d` on the tested range**. A serial
append would cost about `1.635 log2 n` stages by read-once arithmetic, a
coefficient near 4.9. The band's last `K` stages do it in place instead.

**Independence model.** Width ratios for `tr` are grid-limited. The grid spacing
`0.1/sqrt(n)` pins `log2(width/sorted)` near `-3`, so read these as upper bounds,
not measurements. Even so, that is at least 8 times sharper than the sorted
threshold. **[hand]** No `n`-input monotone function does that at `p = 1/2`, since
majority is the sharpest. So the model overstates sharpness here, as LB-33 saw at
small `d`.

The actual network is what counts, and it confirms the sharpening is real. On
`zq` at `d = 64`, the middle wire's actual width matches the sorted width (0.01008
vs 0.01002), against 0.032 on the barrier.

**Other rules.**

- `zq` is sharp on 99.9% of wires at `d = 56` but degrades: 65% at `d = 64`, 19%
  at 72, 8% at 80. It sorts on `q` at the single point `p = 1/2`, which says
  nothing about wires with other thresholds.
- `qs` is better placed (92% at `d = 56`) but less sharp (83%).
- `remix` is no better than the barrier on independence width at `d = 64`.
- `bfly` gains about one bit at `d = 48`, and breaks the relaxations beyond the
  blind window.
- `zh` changes nothing.
- Filling idle slots helps only a little (`-0.49` to `-0.83` bits at `d = 48`).

## 5. Rate: the scan above `N_d` [numeric]

At `N_d`, depth/`log2 n` is 4.4 to 5.7, far above 3.27 or 3.5. So a pass at `N_d`
alone cannot separate those rates. The scan pushes `n` higher at fixed `d`:

| `d` | `n` | `n/N_d` | depth/`log2 n` | `sp` | `std / sqrt n` | relaxations |
|---:|---:|---:|---:|---:|---:|---|
| 48 | 23616 | 32 | 3.44 | 0.9994 | 0.035 | fail |
| 48 | 47232 | 64 | 3.22 | 0.9959 | 0.066 | fail |
| 48 | 94464 | 128 | 3.03 | 0.9873 | 0.122 | fail |
| 56 | 110688 | 32 | 3.46 | 0.9944 | 0.043 | fail |
| 56 | 221376 | 64 | 3.27 | 0.9855 | 0.080 | fail |
| 56 | 442752 | 128 | 3.09 | 0.9695 | 0.146 | fail |
| 60 | 241440 | 32 | 3.47 | 0.9888 | 0.048 | fail |
| 60 | 482880 | 64 | 3.28 | 0.9786 | 0.088 | fail |

The Kahale-type relaxations fail by `1.4 N_d` to `2.8 N_d` on this rule, while
`sp >= 0.97` persists to `64 N_d`. So **`sqrt(n)`-scale average-case sharpness and
placement survive well past the point where the relaxations themselves fail**, at
depth around `3.3 log2 n`. At these sizes, sharpness is not the binding constraint.
These are small sizes, and this says nothing about the limit.

**The trend is not flat.** A least-squares fit over the scan gives

```text
log2(std/sqrt n) = 0.064 d + 0.85 log2(n/N_d) - 12.4       (rms residual 0.29)
```

Holding `std/sqrt n` fixed loses `0.064/0.85 = 0.075` bits of `n` per stage. If the
trend persisted, this heuristic would meet `N_d` near `d ~ 180`, with coefficient
about **4.3**. LB-33's barrier loses 0.25 bits per stage. The fit uses one rule
with `K = d/2`. It is a trend, not a law, it bounds only this rule, and a better
rule could lower it.

**Exact sorting does not follow sharpness.** This is the interpolated `n` sorted
exactly half the time:

| `d` | 36 | 40 | 44 | 48 | 52 | 56 | 60 | 64 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| `n_exact` | 536 | 678 | 835 | 1141 | 1290 | 1502 | 1708 | 2066 |
| `log2(N_d / n_exact)` | -2.82 | -2.07 | -1.28 | -0.63 | 0.30 | 1.20 | 2.14 | 3.00 |

That is **0.21 bits per stage** (64 samples, half-bit grid), a coefficient near 10
if extrapolated, and well above the 0.02 that 3.5 would need. It is again an
upper estimate from one heuristic. At `d = 48`, `n_exact` is about 28 times
LB-33's `n_true` (a different criterion, so the comparison is only indicative).

**Structured inputs do not improve.** On the reverse and organ-pipe inputs, the
largest rank error stays at 2.4% to 5.1% of `n` on `tr` for every `d` from 48 to 80.
The barrier, measured at `d = 48` only, is at 5.7%. Sawtooth sits at 0% to 3.4% and
half rotation below 0.5%. Four inputs are only a probe, but this error is linear
in `n` and the sharpness repair does not touch it.

So three scales separate:

| Scale | Deficit on this family | Status |
|---|---|---|
| `sqrt(n)` sharpness, random inputs | about 0.075 bits/stage; none at tested `N_d` | repaired at tested sizes |
| exact rank, random inputs | about 0.21 bits/stage | not repaired |
| structured inputs | error about `0.04 n`, no trend | not repaired |

## 6. The combined inequality, and why it is not a theorem

The natural statement charges middle wires for certificates and for sharpness
separately. Suppose a wire needs `a log2 n` stages for certificates, sharpness
grows by at most `kappa` per layer, and the two **cannot share a comparator**. Then

```text
d >= (a + 1/(2 log2 kappa)) log2 n.          [conditional, not proved]
```

| `a` | `kappa` | coefficient | status |
|---:|---:|---:|---|
| 1 | 2 | 1.50 | `a`, `kappa` sound; "no sharing" is not |
| 2 | 2 | 2.50 | `a = 2` is family-only |
| 1 | `2/phi` | 2.64 | `kappa` not sound |
| 2 | `2/phi` | **3.64** | the only case above 3.5; nothing sound |

Reaching 3.5 with `a = 2` needs `kappa <= 2^(1/3) = 1.26`, barely above read-once
(1.236). Three ingredients are missing:

1. **`kappa` is the weakest step.** The sound value is 2. Any gain needs a bound
   on the correlation of pivotal events, the saturated object of LB-33 §3. Since
   read-once networks exist, the true value cannot be below `2/phi`, so the target
   window `[1.236, 1.26]` is very narrow. No technique is known to enter it.
2. **`a`.** Only `a = 1` is sound, from fan-in.
3. **No sharing.** Each comparator can double a size and sharpen in the same stage.
   The data point the wrong way: at `d = 48`, depth `3.03 log2 n` has
   `sp = 0.987`. That contradicts the 3.64 reading unless the additive constant
   exceeds about 10 stages, which finite data cannot exclude.

**Not provable with current tools.** The gap between factor 4 per two layers
(sound) and `4/phi^2 = 1.53` (read-once) is the entire content, and it is open.

## 7. What is left

**[conjecture]** The scales in §5 line up with Valiant's read-once analysis:

```text
to width n^(-1/2)      (c/2) log2 n = 1.635 log2 n     part of the next line
bias 1/n to constant    c    log2 n = 3.27  log2 n     rank-exact gap
error to 2^(-n)        +2    log2 n                    all inputs
total                   5.27 log2 n                    Valiant's 5.3
```

The total is 2.635 iterations of two layers each. LB-33's width measures only the
first line. Exact ranks need the second, whose read-once cost is exactly Kahale's
constant, so a read-once argument there still stops at 3.27.

Any gain would have to come from the third line: **the cost of pushing failure
down to `2^(-n)` on non-random inputs**. No potential tested so far reads this,
because product and slice measures average it away. In this picture, 3.5 needs
11.5% of that line to add to Kahale's depth rather than overlap it. None of this
is sound for networks, which are not read-once.

**Recommended next step: LB-34 (mixed-polarity restriction families), aimed at
worst-case inputs.** Use the `tr` hybrid as the new adversary. It passes the
relaxations and is sharp on random inputs, so a useful potential must fail on
*it*. A cheap first test is to search for the 0-1 inputs that break it and see
whether they share a restriction structure. Separately, a better rule in the
exact-rank regime would show whether 0.21 is a heuristic artifact.

## 8. The monotone-formula view

Each output of a depth-`d` network is a monotone formula with at most `2^d` leaves
(tree unfolding), and the median output computes majority. So **[proved]**
`D(n) >= log2 L_mon(MAJ_n)`.

| Quantity | Value | Source |
|---|---:|---|
| Best formula lower bound for majority | `Omega(n^2)`, monotone or not | **[published]** [Gál, Tal, Trejo Nuñez 2018](https://eccc.weizmann.ac.il/report/2018/160/download) |
| Monotone threshold bound | `floor(k/2) n log(n/(k-1))` for `TH_k`, `2 <= k <= n/2` | **[published]** [Radhakrishnan, JCSS 1997](https://www.tcs.tifr.res.in/~jaikumar/Publications/RadhakrishnanJCSS97.pdf) |
| Khrapchenko, all De Morgan formulas | `(n/2)(n/2 + 1)` for majority | Khrapchenko 1971; calculation below |
| Best upper bound | `O(n^5.3)` monotone | **[published]** [Valiant 1984](https://www.wisdom.weizmann.ac.il/~oded/PDF/mono-maj.pdf) |
| Read-once amplification | `n^3.27`, optimal for read-once | **[published]** Boppana 1989, via [Dubiner–Zwick 1997](https://epubs.siam.org/doi/10.1137/S009753979223633X) |
| Depth bound implied by `n^2` | `2 log2 n` | weaker than Kahale |
| What 3.5 needs, formula-only | `n^3.5` | beats the known bound by `n^1.5` |

Khrapchenko calculation **[proved]**: take `A` = weight `n/2` and `B` = weight
`n/2 + 1`. The edges number `|B|(n/2 + 1) = |A|(n/2)`, so
`|E|^2/(|A||B|) = (n/2)(n/2 + 1)`.

**What 3.5 would imply.** A proof using only "the middle output is a small monotone
formula for majority" would give `L_mon(MAJ_n) >= n^3.5`. That would be a major
breakthrough, and it would also pass the read-once exponent 3.27. **[hand]**
Influence methods look like the wrong tool: Khrapchenko is an influence-style
argument and stops at `n^2`, just as the sum rule stops at 2.5 in §6.

**Can the network structure get around this? Partly, and it already has.** Kahale
reaches 3.27, well above the formula bound of 2, by using what formulas lack:

- **All thresholds at once.** Edge outputs are small thresholds with their own
  certificate constraints, and that is where Kahale's counting lives.
- **Width.** There are only `n` registers per layer, with shared sub-formulas.
  Unfolding to a formula erases this.
- **Paired outputs.** Each comparator yields both `min` and `max`, which is what
  the conservation law in §2 expresses.

**[hand]** Kahale's use of these is essentially read-once: edge certificates are
tree-like (LB-33 §3), which is why it lands on Boppana's exponent.

So a depth proof of 3.5 would not need a monotone-formula breakthrough, **provided
it depends on one of those structural features**. It would, however, have to
control the middle of the network, where sharing is heavy. §5 suggests the middle
does not bind at the sharpness scale. If width is the lever, the natural object is
amplification in width-`n` circuits with fan-out, and I know of no lower-bound
technique for it.

The literature checks ran on 2026-10-31 and were not exhaustive. Nothing newer than
2018 surfaced on monotone majority formula bounds, so later work may exist.
[Hoory, Magen, Pitassi, RANDOM 2006](https://www.cs.toronto.edu/~toni/publications.html)
modify Valiant's construction. I could not confirm its constants, so it is not
used above.

## Not verified

- No asymptotic claim here is proved. All of §3 to §5 is finite and sampled.
- `sp`, `exact` and the error figures are sampled on random permutations, with few
  samples at the top: 64 at `d = 80`, 16 to 32 in the extended scan.
- Pair relaxation on `tr` was not run above `d = 56`. On `zq` it passes at
  `d = 60`, `K = 26`; the `K = 30` run was stopped unfinished.
- The extended scan stops at `d = 64`, `n/N_d = 32` (one row at that depth). The
  planned `d = 68, 72` rows and the rest of `d = 64` were not run. The fit did not
  move when the last rows were added.
- Correlation relaxations (LB-33) were not rerun. Harris potentials equal the sizes
  relaxation by LB-33 §2, and BK is vacuous on the middle.
- The structured inputs are four examples, not a worst-case search.
- The `K_blind` search assumes monotonicity in `K`.

## Reproduce

Run from the repository root. The full set takes a few hours on 4 cores, mostly in
the `d >= 72` rows and the pair runs.

```sh
S=lower-bound/experiments/scripts/kahale_amplification_kill.py
python -B $S valiant
python -B $S idle 32 40 48 56 64 72
python -B $S blind 40 48 56 64 72 80 96
python -B $S budget 40 21 48 26 56 29 64 32 72 37 80 39 --P 100
python -B $S run 56 --sched zq --K 28 --P 200 --smax 3
python -B $S ranks 56 --sched tr --K 28 --frac 1.0 --samples 256
python -B $S run 56 --sched tr --K 28 --frac 1.0 --P 60 --smax 0
python -B $S pairk 56 --sched tr --frac 1.0 --Ks 24,28
python -B $S nscan 48 --grid=-8,8 --samples 64 --M 128 > nscan.out
python -B $S nscan 48 --grid=10,14 --samples 32 --M 64 > ext.out
python -B $S fit nscan.out ext.out
```

Outputs: [`kahale-amplification-kill-output.txt`](kahale-amplification-kill-output.txt).
These are finite computations of relaxations and sampled runs. They make no sorting
claim and add no Lean.
