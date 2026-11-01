# Worst-case inputs of the `tr` hybrid (LB-34)

Claim labels:

- **[proved]** a complete argument here (not kernel-checked; no Lean was added).
- **[hand]** a hand-level argument with a step left informal.
- **[numeric]** a finite computation or search, with no asymptotic force.
- **[published]** a cited result.
- **[conjecture]** a reading of the data.

## Verdict

**No coefficient above 3.2706 comes out of this ticket. The mixed-polarity family
is rejected. The worst-case search found something stronger than the ticket asked
for, but it is a test on one network, not a bound.**

1. **`tr` breaks badly, and from a single stray. [numeric]** At `n = N_d` the
   worst rank error found is 11% of `n` at `d = 48`, 22% at `d = 56` and **29% at
   `d = 64`, wire 7314, against about 4% on the LB-35 structured inputs.** Every
   witness is re-simulated. The misplacement stays small: 1 to 10 wrong wires on
   these witnesses, and at most about 1% of `n` on the best inputs found per
   threshold. So this is a stray, not a badly sorted network.
2. **The ticket's recurrence passes `tr`, for a structural reason. [proved, numeric]**
   The `(1,0)`-forcing pair family with supports finds no inversion at `d = 40, 44`,
   where inversions exist. Mixed polarity cannot help: at the endpoint every pair
   witness projects to a zero certificate and back (§4.1), and compatibility only
   deletes candidates (§4.3).
3. **A one-polarity recurrence fails on `tr`, the barrier and a randomly wired
   barrier at `N_d`, `d >= 40`. [numeric]** Keep,
   per wire, one input set: at an OR take the set of the child with the smaller
   *uncapped LB-24 tree cost*, at an AND take the union. This adds one thing to
   LB-24: the union of the leaves of its own argmin tree, instead of their count.
   It is one forward pass, and it gives a rank error of 27% of `n` at `d = 64` on
   `tr`, and it fails on the barrier too (§4.4). It is the first closed-form
   upper recurrence in this line that fails on both.
4. **That failure is not charged to every network. [proved, numeric]** Each failure
   is a true proof that *that network* does not sort, and nothing more. Real sorters
   pass (Batcher fits at `N_d` through `d = 44`), so `tr`'s failure at `d = 40, 44`
   is a defect of `tr`, not of the depth. No optimum over schedules can be evaluated,
   so **no rate is reported** (§6).

**Assessment.** The route is exhausted as a source of potentials. What is left is
the same open core as LB-24 and LB-35, stated more sharply: lower-bound the overlap
of certificates in *every* network. No tool for this is known.

## 1. Setup

The network is LB-35's `tr` with `frac = 1`, at `n = N_d`, depth `d + 2`, with
LB-35's `K`: 20, 20, 28, 32, 36, 36 at `d = 40, 48, 56, 64, 72, 80`, and `K = d/2`
at the other depths. It is imported from
[`kahale_amplification_kill.py`](../lower-bound/experiments/scripts/kahale_amplification_kill.py).
The tail generator in the new script reproduces it exactly at `d = 40..64`
(comparator sets compared layer by layer).

For a 0-1 input with `k` zeros let:

- `m(x)`, the misplacement: the ones in the first `k` outputs.
- `E(x) = max(k - f, l - k + 1, 0)`, with `f` the first one and `l` the last zero.

**The identity. [proved]** Let `z_w`, `o_w` be the true minimum zero and one
certificate sizes of output wire `w`. Then

```text
worst rank error over all permutations
    = max over 0-1 x of E(x)
    = max_w max(w + 1 - z_w, n - w - o_w).
```

If `S` is a zero certificate of `w`, take the input with zeros exactly `S`, and
give them ranks `0..|S|-1`. Wire `w` then holds a rank `<= |S| - 1`, an error of at
least `w + 1 - |S|`. Conversely, if wire `w` holds rank `v < w`, the inputs of rank
`<= v` force `w` to zero once all others are one, and by monotonicity they form a
certificate of size `v + 1`. The one side is dual. Brute force on 60 random
networks with 5 to 7 wires agrees (`validate`). **So a search for breaking inputs is
a search for small certificates**, and that is what the search below does.

**Proof-tree search.** Compute the LB-24 tree cost forward, uncapped, then walk back
from a target wire: both inputs at an AND, the cheaper input at an OR. The leaves are
a valid certificate. Repeat with low prices on the current set. This found far more
than hill climbing on inputs did, which from random starts reaches only 2% to 23% of
the proof-tree error on the same sizes.

## 2. Question 1: adversarial inputs

**Exact results. [numeric, exact]**

| `d` | `n` | method | result |
|---:|---:|---|---|
| 24, 28 | 8, 18 | all `2^n` inputs | sorts |
| 32 | 36 | image product after 3 layers (1.4M images); z3 | sorts (both methods) |
| 36 | 76 | z3 `QF_FD` | sorts (unsat in 36 s) |
| 40 | 161 | z3 `QF_FD` | **does not sort** (sat); search finds `E = 5` |

So `tr` is a true sorter through `d = 36`, and the first failure in this grid is at
`d = 40`.

**Worst rank error found at `N_d`. [numeric]** These are lower bounds on the true
worst error. Every value is a re-simulated witness.

| `d` | `n` | best `E` | `E/n` | wire, side | certificate size | wires tested | targets with `E > 0` | structured (LB-35) |
|---:|---:|---:|---:|---|---:|---:|---:|---:|
| 40 | 161 | 5 | 0.031 | 82, one | 74 | all | 3.1% | |
| 44 | 344 | 43 | 0.125 | 158, one | 143 | all | 17.6% | |
| 48 | 738 | 84 | 0.114 | 599, zero | 516 | all | 23.4% | up to 0.051 |
| 52 | 1593 | 239 | 0.150 | 753, zero | 515 | all | 29.3% | |
| 56 | 3459 | 778 | 0.225 | 2177, zero | 1400 | all | 36.1% | up to 0.051 |
| 64 | 16530 | 4816 | **0.291** | 7314, one | 4400 | every 6th | 31.2% | up to 0.051 |
| 72 | 80209 | 27109 | 0.338 | 32768, one | 20332 | every 512th | 53.2% | up to 0.051 |
| 80 | 393913 | 81405 | 0.207 (partial) | 35840, one | 276668 | every 512th, wires < 36000 only | 50% of those | up to 0.051 |

The error on random inputs at these depths is far smaller. It is 0.012 of `n` at
`d = 48` and 0.033 at `d = 52` over 64 samples.

**Does the error scale linearly in `n`? [numeric]** Yes or faster, on this range.
`E/n` does not settle: it rises from 0.11 to 0.34 between `n = 738` and `n = 80209`.
It cannot grow without limit, since `E < n`, so "about `n^1.3`" on this range is a
finite trend only. At fixed `d = 56`, `K = 28` (a thinner scan, every 16th wire):

| `n/N_d` | 1/4 | 1/2 | 1 | 2 | 4 |
|---|---:|---:|---:|---:|---:|
| `E/n` | 0.063 | 0.152 | 0.225 | 0.304 | 0.355 |

**Per threshold. [numeric]** For 17 values of `k`, the worst `k`-zero input found by
a greedy multi-wire cover, then hill climbing with swaps. The random baseline is the
mean over 32 random `k`-zero inputs.

| `d` | `n` | max `m` found | `m/n` | at `k` | random `m` at the same `k` | max `E` in this mode |
|---:|---:|---:|---:|---:|---:|---:|
| 40 | 161 | 0 | 0 | | 0 | 0 |
| 48 | 738 | 5 | 0.007 | 277 | 0 | 28 |
| 56 | 3459 | 34 | 0.010 | 1946 | 0.06 | 280 |
| 64 | 16530 | 157 | 0.0095 | 9298 | 0.28 | 2035 |

The profile is flat across the middle thresholds and falls at the ends. At `d = 64`,
`m` runs 42, 76, 112, 106, 124, 124, 126, 145, 157, 128, 116, 117, 107, 44, 42 over
`k/n = 1/16 .. 15/16`. This mode is weaker than the proof-tree scan: it misses the
`d = 40` witness entirely, and its `E` is 40% of the scan's at `d = 64`. So these
`m` are only lower bounds, and the grid does not hit every `k`.

Worst `E` and worst `m` are different quantities. The single-wire witnesses have
`m` between 1 and 10. So the rank error is linear in `n`, while the misplacement found
is about 1% of `n`, with no evidence yet that the true maximum of `m` is that small.

## 3. Question 2: structure of the breaking inputs

**A shared structure was found on the network side, and none on the input side.**

**The witness anatomy. [numeric, top 40 witnesses at each of `d = 44..64`]**

Walk back from the target wire through the proof tree of the certificate.

- **The tail is AND-free.** In all 200 of those witnesses the tree is a *single
  wire* from the output back to its last AND gate. So one wire `u` at time `t*` forces
  the target, through min outputs only.
- **`t*` sits at the barrier/tail boundary.** The median distance of the last AND
  from the end is 23, 25, 31, 35 at `d = 48, 52, 56, 64`, against `K + 2` = 22, 24,
  30, 34.
- **The target is the reach limit of `u`.** In 198 of the 200, `w` equals the lowest
  output reachable from `u` through the tail (the highest, on the one side). The stray goes as far as the tail allows and stops.
- **The tail is local.** Median reach is 7 wires in the last 8 layers and about 40
  in the last 20 at `d = 48`, against 87 and 354 on the barrier. The drift `|u - w|`
  is 62, 124, 281, 1300 at those depths.
- **The tree behind `t*` grows like Kahale's tree.** The width of the proof tree per
  layer backward has median growth 1.49, 1.52, 1.59, 1.58 at `d = 48, 52, 56, 64`,
  against `phi = 1.618`, until it saturates at `|S|`.
- **The tree is heavily shared.** Leaves with multiplicity are 50 to 24000 times
  `|S|`. This is why every closed size recurrence is capped here. At wire 599, `d = 48`,
  LB-24 gives `n = 738`, and the true certificate has at most 516 inputs.

**Statement. [numeric]** A breaking input is a *stray*: a single wire at the boundary
`d - K` with a Fibonacci-grown, heavily shared proof tree, whose certificate is much
smaller than its index; it then falls along an AND-free path to its reach limit.
Odd wires carry the zero-side errors and even wires the one-side errors, because the
last cleanup layer makes odd wires min outputs. That part is trivial.

**The input side. [numeric]** No structure was found. On top witnesses at
`d = 48, 56, 64`:

- first-layer comparators hold 0, 1, 2 certificate inputs at binomial frequencies,
  to within about 0.06;
- index-bit correlation is about 0.05 or less;
- the density by index sixteenth is flat, and the two sides of a first-layer comparator
  have equal density.

A witness looks locally like a density-`p` random set, yet it is exponentially rare
under that measure: random inputs at those densities never show it. It has no short
description visible to these tests. No small set of input wires, and no partial
assignment on a wire pair, is shared: Jaccard overlap of certificates at `d = 48, 52`
is 0.15 to 0.56.

**A correction to the obvious reading.** Reach looks like the cause, but it is not
sufficient. Rule `tw` replaces alternate tail stages with wide comparators by mean-rank
gap, so median reach at `s = 24` rises from 115 to 324 at `d = 52`. `E/n` only moves
from 0.147 to 0.144, and wrong wires on random inputs go from 1.7% to 33%. After that
change the witness has a few ANDs in the tail, with width 2 to 5. A second stray is
cheap, because strays are plentiful: 53% of targets at `d = 72` have `E > 0`.

**Why LB-24's window does not see it. [proved, numeric]** A reach-graded test is sound
for every network. If `r_t(u)` is the lowest output reachable from `u` at time `t`, a
sorter has `z_u(t) >= r_t(u) + 1`, since the zero on `u` ends at a wire `>= r_t(u)`
and must end below `|S|`. The width rule is the case `r_t(u) >= u - 2^s + 1`. Applied
to LB-24's upper bounds, this test still passes on `tr` at `d = 40..56`, with worst
margin 0 at the first layer, which is trivial, because the bound on `z_u(t)` is capped
at `n` in the stretch that matters. Tail reach only moves
the failure to where the sizes are saturated.

## 4. Question 3: the recurrences

### 4.1 Mixed polarity adds no witness [proved]

If `(S, T)` forces `(out_i, out_j) = (1, 0)` then `S` is a zero certificate of `j` and
`T` a one certificate of `i`. Conversely, if `|S| <= j` for a zero certificate `S`
of `j`, then on the input with zeros exactly `S` some `i < j` holds a one, and
`(S, complement of S)` forces `(1, 0)` on `(i, j)`. This is LB-24's endpoint
equivalence. So:

- an inversion exists iff a zero certificate has size `<= j`;
- every member of a mixed family projects to a member of a single-polarity family
  with the same `S`, and the compatibility condition can only remove members.

Also **[proved]** any inversion on `i < j` has
`|S| + |T| >= z_j + o_i >= n + 1 + (j - i) - 2E`. A witness pins a constant fraction
of the inputs even at `E = 0.29 n`, so a family has to build near-total assignments.

### 4.2 The recurrences

| Name | State per wire or pair | Rule | Upper-closed? |
|---|---|---|---|
| LB-24 wire | one size | `min`, `min(n, sum)` | yes |
| zero beam `B` | `B` input sets | OR: both beams; AND: all unions; keep the `B` smallest by true size | yes |
| pair family `B` (the ticket's) | `B` restrictions `(S, T)` per ordered pair | each option is one pair fact, or two merged if compatible; keep the `B` smallest by size, or by summed tree cost | yes |
| tree family | one input set and one uncapped cost | OR: the set of the child of smaller cost; AND: the union, cost `sum` | yes |

"Upper-closed" means that every member is a true forcing assignment. `pair_family`
members were re-simulated with free inputs all 0 and all 1, on 200 random members plus
all terminal inversions, and witnesses from the others are checked by `check_cert`.

### 4.3 The ticket's family passes `tr` [numeric, structural reason proved in part]

| `d` | `n` | schedule | true `E` found | rank | `B` | terminal inversions |
|---:|---:|---|---:|---|---:|---:|
| 40 | 161 | `tr` | 5 | size | 1, 4 | 0 |
| 40 | 161 | `tr` | 5 | tree | 1, 4 | 0 |
| 40 | 161 | barrier | 11 | size | 1, 4 | 0 |
| 44 | 344 | `tr` | 43 | size | 1, 4 | 0 |
| 44 | 344 | `tr` | 43 | tree | 1, 4 | 0 |

The family is alive early and dies. At `d = 44`, `B = 4`, size rank, inversions number
32592 at layer 11, 186 at layer 17 and 0 from layer 23. Nonempty pairs fall from 77%
to 4% (1.2% under tree rank). Merges are not rare: 60% to 98% of the attempted merges
are compatible.

**Why it is blind.** The witness in §4.1 is `(S, complement of S)`. The `T` part exists
only in hindsight, once `S` is known. To build it through a recurrence, every
intermediate step needs a pair fact on the right pair, and each conjunction needs
two facts that were kept and that agree. So compatibility is a cost with no
compensating information, by §4.1. The tree family below finds these same errors with
no `T` at all, and with the same ranking the pair family does not.

### 4.4 Ranking is what matters

| `d` | `n` | LB-24 wire | zero beam `B = 16` | tree family | search |
|---:|---:|---|---|---:|---:|
| 44 | 344 | pass | pass (`B = 64` too) | **0.073** | 0.125 |
| 48 | 738 | pass | pass (`B = 64` too) | **0.084** | 0.114 |
| 52 | 1593 | pass | pass | **0.129** | 0.150 |
| 56 | 3459 | pass | pass (`B = 8`) | **0.195** | 0.225 |
| 60 | 7545 | pass | not run | **0.242** | not run |
| 64 | 16530 | pass | not run | **0.275** | 0.291 |
| 72 | 80209 | pass | not run | **0.334** | 0.338 |

Entries are `E/n` on `tr`. At a worst wire the certificate sizes are:

| `d` | wire | need | LB-24 | beam 16 | tree | search |
|---:|---:|---:|---:|---:|---:|---:|
| 48 | 599 | 600 | 738 | 699 | 540 | 516 |
| 52 | 753 | 754 | 1593 | 1462 | 554 | 515 |
| 56 | 2177 | 2178 | 3459 | 3118 | 1518 | 1400 |

So a beam of true set sizes is blind and a single set ranked by tree cost is not.
**[conjecture]** Set size is the wrong signal once sets saturate, while tree cost
measures how much AND demand a wire carries, and low-demand sets share leaves.

**The tree family's relation to LB-24. [proved]** By induction `|S_w| <= c_w`, where
`c_w` is the uncapped LB-24 cost. So wherever the LB-24 terminal test fails, this test
fails too. With LB-24's graded windows and (W) added, it is at least as strong as the
wire relaxation.

**Controls. [numeric]** Soundness requires that sorters pass, and they do: the tree
family and the search find nothing on Batcher at `n = 32, 64, 344, 738`, or on `tr` at
`d <= 36`, where z3 confirms it is a sorter.

**Which schedules fail. [numeric]** Entries are tree-family `E/n`.

| `d` | `n` | barrier | `tr` | random wiring | random prefix, `tr` tail |
|---:|---:|---:|---:|---:|---:|
| 44 | 344 | 0.084 | 0.073 | 0.111 | 0.064 |
| 48 | 738 | 0.098 | 0.084 | 0.107 | 0.102 |
| 52 | 1593 | 0.119 | 0.129 | 0.136 | 0.148 |

"Random wiring" keeps the barrier's blocks and heights and randomizes the bijection
between halves, so the heights and wire relaxations pass unchanged. It does not help,
and the sharing is not an artifact of structured wiring. I had expected the reverse.

## 5. Is the failure charged to every network?

**Soundly, yes, but only as a statement about that network. [proved]** A witness is a
true input that the network does not sort. A failure on `tr` proves that `tr` is not a
sorter, and nothing about a different schedule.

**Real sorters at `N_d`. [published, proved]** Batcher's odd-even merge sort has depth
`k(k+1)/2` on `2^k` wires, and deleting top wires keeps a sorter. So at `d = 40`
(depth 36 on 256 wires) and `d = 44` (depth 45 on 512 wires) there is a sorter on
`N_d` wires within depth `d + 2`. **Every sound test passes there, so the failure of
`tr` at `d = 40, 44` is `tr`'s, not the depth's.** From `d = 48` no sorter I know fits
(Batcher needs 55 at 738 wires, against 50), but that is ignorance, not a barrier.

**Repair by counterexample. [numeric]** Keep the barrier prefix. In each tail stage,
compare the first misplaced one and the last misplaced zero of the banked witnesses,
and give the other wires the `tr` pairing. Heights and wire relaxations pass in every
round. `E` below uses the weaker scan each round, so it is less than the §2 numbers.

| adversary | `d` | rounds | `E/n` round 0 | best round | last round | wrong wires, random inputs |
|---|---:|---:|---:|---:|---:|---:|
| search | 44 | 14 | 0.087 | 0.032 | 0.032 | 0 to 3.8% |
| search | 48 | 12 | 0.080 | 0.054 | 0.075 | 0.2% to 22% |
| tree | 48 | 60 | 0.084 | 0.030 | 0.045 | 0.2% to 66% |

The tree test was never passed in those 60 rounds. Against a weak adversary (4 search
rounds per wire) the error reached 0 at `d = 44` within 4 rounds, which only shows that
the adversary was weak. So a simple repair lowers the error by at most about
3 times, it never clears it, and it gives up random-input sharpness to do so: `exact`
falls to 0. This repair is crude, and nothing here shows that a better one fails.

**Largest `n` passing the tree test, by schedule. [numeric]** Grid `N_d 2^(j/2)`; the
test is not monotone in `n`, so this is the largest passing grid point.

| `d` | 44 | 48 | 52 | 56 | 60 | 64 |
|---|---:|---:|---:|---:|---:|---:|
| `N_d` | 344 | 738 | 1593 | 3459 | 7545 | 16530 |
| barrier | 30 | 33 | 35 | 38 | 42 | 46 |
| `tr` | 172 | 184 | 199 | 216 | 333 | 365 |
| Batcher at depth `d + 2` | 512 | 512 | 512 | 1024 | 1024 | 2048 |

Batcher beats both constructions at every one of these depths. **So the flat rows are
defects of those two schedules**, and their slopes are not a rate of the test.

## 6. Question 4: rate

**No coefficient is reported.** A schedule-specific failure proves nothing about the
rate, and the optimum of the test over all schedules cannot be evaluated here. What
can be said:

- **[proved]** Let `c_tree` be the coefficient the tree test would force with windows
  and (W) included. It is at least 3.2706, by §4.4, and at most any proved upper
  coefficient, since sorters pass. In this repository that interval is
  `[3.2706, 789.75]`.
- **[hand]** Whether it exceeds 3.2706 is not a finite computation. LB-24's method
  worked because a schedule meeting the relaxation at `N_d` was a kill test. Here no
  schedule was found that passes the tree test at `N_d` for `d >= 48`, so there is no
  kill. That is **not** evidence of a rate, because at `d <= 44` the passing schedule
  is a real sorter, and no finite search of this kind separates "no such schedule
  exists" from "I did not find it".
- **[hand]** The test is a greedy rule, so its verdict depends on how costs happen to
  rank children. A schedule can in principle bias those ranks with comparators that
  do little. Any theorem would need to hold over all selection rules, and the
  strongest version of that is `min_S |S|`, the exact `z_w`, whose schedule optimum
  is `D(n)` itself.

**What a theorem would need. [conjecture]** A bound of this shape, for every network:
a wire with proof tree of multiplicity `L >= n` has a certificate of size at most
`f(L, n) < w + 1`. That is a lower bound on forced overlap. The observed sharing
factors say the overlap is large on these schedules, and random wiring does not reduce
it. Yet sorters show that the overlap must be avoidable at some depth. This is the
same gap LB-24 §5 asked for, and LB-35 §6 called "no sharing". LB-33 already shows that
Harris and BK do not give it. No technique is known.

The numbers fit LB-35 §7's third line in spirit: a stray is an event of probability
about `2^(-cn)` under the threshold measure, invisible to product measures. That reading
is **[conjecture]**, and it is not sound for networks.

## 7. Next step

Stop the certificate-potential line: LB-02, LB-22, LB-24, LB-33, LB-35 and this ticket
all end at the same overlap question. The one bounded screen left is **LB-08**, a 6 to
7 wire exact LP with a clean Farkas outcome. If it comes back infeasible, stop.
LB-03 reopens the charging problem of LB-26 and has no comparable cheap test.

The `tree` recurrence should be kept as a tool. It runs in seconds, and it is a far
better non-sorter certificate than random or structured inputs.

## Not verified

- Every `E` is a lower bound on the true worst error, except at `d <= 36`, where the
  network sorts. The exact worst error is unknown from `d = 40` on: z3 on
  "`E >= 6` at `d = 40`" returned unknown after 900 s, and the MILP bound is useless.
- Scans at `d = 64, 72, 80` test only every 6th, 512th and 512th wire. Fractions of
  targets at those depths are sampled.
- The `d = 80` scan ran out of budget in the lowest tenth of the wires, so its `E/n` is not
  comparable with the other rows and is left out of the trend.
- `m` values are weak lower bounds on a 17-point grid of `k`. "About 1% of `n`" is what
  the search found, not a measured maximum.
- MILP gave no exact certificate sizes: the LP bound stayed near 2 to 4 at `n = 36`.
- The anatomy statistics cover the top 40 witnesses at `d = 44..64`, not all of them.
  At `d = 40` only 10 targets have `E > 0`, and they were not tabulated.
- The pair family ran on `tr` only at `d <= 44` and `B <= 4`, and on the barrier only at
  `d = 40`. Its behaviour at larger `B` or `d` is unknown.
- CEGAR nets were checked for heights and wire only, not the pair relaxation, and the
  final nets got no full-strength scan.
- The tail variants `tw` and `rbtr` are a few heuristics. Random wiring used one seed.
- Search `E` in the §4.4 schedule table is not shown, since the 30 s budget there is
  below the §2 scans.
- Batcher's depth bound at `d <= 44` is applied by formula. The generated network was
  run on random permutations only at `n <= 64`, and only searched at 344 and 738.
- Literature was not searched for depth records at 738 or more wires.

## Reproduce

Run from the repository root. Set `LB34_CACHE` to a scratch directory to cache networks.
Total is about 90 minutes on 4 cores, mostly `scan` and `thresh`.

```sh
S=lower-bound/experiments/scripts/kahale_worst_case_inputs.py
python -B $S validate
python -B $S exact 24 28
python -B $S exact 32 --T 3
python -B $S exact 32 36 40 --z3 1500
python -B $S exact 40 --ge 6 --tlimit 900
python -B $S scan 24 28 32 36 40 44 48 52 --iters 8 --budget 150 --top 40 --save W
python -B $S scan 56 --iters 8 --budget 1200 --top 60 --save W
python -B $S scan 64 --iters 5 --stride 6 --budget 1800 --top 60 --save W
python -B $S scan 72 80 --iters 6 --stride 512 --budget 1500 --top 24 --save W
python -B $S scan 56 --n 13836 --K 28 --iters 6 --stride 16 --budget 500 --top 20   # also 6918 1729 864
python -B $S thresh 40 48 --grid 17 --tlimit 15 --steps 600
python -B $S thresh 56 64 --grid 17 --tlimit 25 --steps 300 --batch 64
python -B $S struct 40 44 48 52 56 64 --save W --show 40
python -B $S fib 48 52 56 64 --save W
python -B $S dump 40 44 48 52 56 64 --save W
python -B $S family 32 40 44 48 52 --kind zero --B 1,4,16
python -B $S family 44 48 --kind zero --B 64 --scheds tr
python -B $S family 40 44 --kind pair --B 1,4 --scheds tr
python -B $S family 32 40 44 --kind pair --B 1,4 --scheds tr --rank tree
python -B $S family 40 --kind pair --B 1,4 --scheds barrier
python -B $S tree 36 40 44 48 52 56 --alpha 1,0.5 --reps 8
python -B $S tree 60 64 72 --scheds tr
python -B $S compare 48 52 56 --save W
python -B $S matrix 44 48 52 --budget 30 --stride 3
python -B $S repair 48 52 --wide 2,3 --budget 60 --iters 4
python -B $S batcher 32 64 344 738
python -B $S cegar 44 --rounds 16                        # weak adversary
python -B $S cegar 44 --rounds 14 --iters 30 --stride 3
python -B $S cegar 48 --rounds 12 --iters 30 --stride 6
python -B $S cegar 48 --adv tree --rounds 60 --add 128 --stride 4 --final 120
python -B $S treepass 32 36 40 44 48 52 56 60 64
python -B $S treepass 44 48 52 56 60 64 --grid=-30,-11 --scheds tr,barrier,rb
```

Outputs: [`kahale-worst-case-inputs-output.txt`](kahale-worst-case-inputs-output.txt),
including hex witnesses that can be checked against the rebuilt networks. These are
finite computations and searches. They make no sorting claim beyond the networks
named, and add no Lean.
