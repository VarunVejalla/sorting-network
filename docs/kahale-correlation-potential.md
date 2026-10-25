# Correlation (Harris / BK / Reimer) potentials on the barrier schedule (LB-33)

## Verdict

**Negative for correlation potentials.** No potential built from FKG/Harris
and van den Berg–Kesten/Reimer inequalities sees the middle-wire defect of
the LB-02/LB-24 barrier schedule. Such a potential is killed at
`1/(1 - log2 phi) = 3.27056`, for three reasons:

1. **Harris lower bounds are the sizes relaxation in disguise (proof, §2).**
   Lower bounds on zero-event probabilities built from `mu(A n B) >= mu(A)mu(B)`
   and `mu(A u B) >= max` stay monomials `p^c`. Here `c` is exactly the bound
   of the corresponding min-plus sizes recurrence (per-wire, pair or k-wise).
   Because `p^m <= P(Bin(n,p) >= m)`, the probabilistic window requirement is
   violated iff the sizes requirement is. So the rates are identical. Per-wire
   (LB-02) and pair (LB-24) are already killed at `N_d`.
2. **BK is vacuous on middle wires (exact, §3).** BK gives
   `mu(A box B) <= mu(A)mu(B) <= mu(A n B)`. Its only use is to bound the joint
   mass by the disjoint part plus the overlap-only mass. On middle
   comparators the overlap-only share of `mu(A n B)` rises to `>= 0.96`
   within about `log2 n + 7` stages and reaches 1.000 in the last stages
   (exhaustive, `n = 10, 12, 14`). The sorted target itself has zero disjoint
   mass on every middle pair. Correlation is what sorting requires, so it
   cannot be charged as a cost. This is the probabilistic face of LB-24's
   saturation at `z = n`.
3. **Mixed polarity is invisible.** For an increasing event `A` and a
   decreasing event `B`, Harris and Reimer give only *upper* bounds on
   `mu(A n B)`. The terminal condition `mu(out_i = 1, out_j = 0) = 0`
   (`i < j`) needs lower bounds, and only Fréchet's `mu(A) + mu(B) - 1`
   provides one.

**Positive diagnostic (not sound, but quantitative).** The defect *is*
exponential in `d`, and it is an **amplification deficit, not a correlation
effect**. Propagate the barrier schedule under independence (the read-once
tree unfolding, where each comparator sees fresh independent copies). The
10–90% threshold width of the middle wire then stays at about `0.03` for
every `d`, while sorting needs width `~ 2.56 sqrt(p(1-p)/n)`.

- `log2(width_ind / width_sorted)` grows by **0.125 per stage**
  (`-0.49, 0.05, 0.47, 1.04, 1.46, 2.02` at `d = 48, 52, ..., 68`).
- Since width scales as `n^(-1/2)`, this is a loss of
  **`c ≈ 0.25` bits of `n` per stage**.
- The sampled actual network agrees. The largest `n` at which the barrier
  network approximately sorts (`V <= 0.02`, below) has
  `log2(N_d / n) = -1.75, -0.69, 0.17, 1.12, 2.08, 3.07, 4.17` at
  `d = 24, ..., 48`. That is a slope of about `0.25` per stage, and
  `n_true` stalls near 40.
- At large `d` the independent model reproduces the true window violations
  almost exactly. At `d = 56`, `s = 6, 5, 4, 3` gives `V_ind = 0.04, 0.18,
  0.26, 0.36` against `V_true = 0.07, 0.20, 0.27, 0.39`.

So `c ≈ 0.25`, roughly 12 times the `0.02` that 3.5 would need, is present
on the barrier schedule. A potential that sees it must bound **middle-wire
sharpness (total influence)**, not correlation. None of the inequalities
tested here gives a sound bound of that kind; see §5.

## 1. The potential

Inputs are `x in {0,1}^n`, i.i.d. with `mu_p(x_k = 0) = p`. These are the
threshold images of a random permutation mixed over `Bin(n, p)` weights.
Wire `w` after `t` stages computes a monotone `f_w`; set
`q_w(p) = mu_p(f_w = 0)`.

For `A = {a = 0}` and `B = {b = 0}` (decreasing events), a comparator
`(lo < hi)` acts as follows:

- `min -> lo`: `A u B`;
- `max -> hi`: `A n B`;
- it conserves `q_lo' + q_hi' = q_a + q_b`.

Write `A box B` for "zeros(x) contains disjoint zero certificates of `a` and
of `b`". Then:

```text
Harris/FKG:   mu(A n B) >= mu(A) mu(B)
BK/Reimer:    mu(A box B) <= mu(A) mu(B)
hence         0 <= mu(A n B) - mu(A)mu(B) <= Ov := mu(A n B) - mu(A box B)
```

`Ov` is the overlap-only mass: both outputs are zero, and every pair of
witnesses intersects. The covariance excess, which is the only thing a
correlation potential can charge, is paid for by overlapping certificates,
as the ticket intended. The propagated state is, per wire (or pair, or
k-tuple), the interval of zero-probabilities at every `p` consistent with
these inequalities.

**Requirements.** These are the sized graded window (G) of LB-02/LB-24,
taken pointwise in `p`. With `s` stages remaining, `w = 2^s` and
`T_m(p) = P(Bin(n,p) >= m)`:

```text
zero side  q_i(p) <= T_{i-w+1}(p)      one side  q_i(p) >= T_{i+w+1}(p)
terminal   q_i(p) = T_{i+1}(p)          for all p in (0,1)
```

These are necessary for a sorting network, since wire `i` being zero
forces at least `i - w + 1` zeros. The script reports
`V_s = max_{i,p}` of the violation.

## 2. Harris-only potentials equal the sizes relaxation (proof)

**Claim.** Fix `p in (0,1)`. Take any family of lower bounds `L(E)` on
`mu_p(E)` for events `E` = "all wires in a set `U` are zero" (`|U| <= k`),
generated from

- `L(x_k = 0) = p`;
- `L(A n B) >= L(A)L(B)` (Harris);
- `L(A u B) >= max(L(A), L(B))`;
- monotonicity under inclusion;
- the floor `p^n`.

Then every derived bound is `p^{c(E)}`, where `c(E)` is the value of the
same derivation in the (min, +) sizes semiring, with costs `1` per input
and cap `n`.

*Proof.* Induct on the derivation. Products of monomials are monomials with
added exponents, a max of monomials is the monomial of the min exponent,
and the floor is the cap. ∎

LB-24's pair recurrence is exactly such a derivation (`Z_xy <-> -log_p J_xy`),
and so is any k-wise version.

**Equivalence of requirements.** Let `m = i - w + 1`.

- If `c >= m`, then `p^c <= p^m <= T_m(p)`, since `p^m` is the probability
  that `m` fixed inputs are zero. So the probability requirement holds at
  every `p`.
- If `c < m`, then `p^c > T_m(p) ~ C(n,m) p^m` as `p -> 0`.

Hence the probabilistic relaxation detects a failure **iff** the sizes
relaxation does, and its optimal rate is the sizes rate: 3.2706 per-wire
(LB-02) and pair (LB-24). This needs no computation. The magnitude
information at moderate `p` is lost, because Harris never improves on a
product.

Getting anything else requires *lower* bounds on unions,
`mu(A u B) = mu(A) + mu(B) - mu(A n B)`. Those need *upper* bounds on the
joint mass, and the only correlation-inequality source of such bounds is
BK: `mu(A n B) <= mu(A)mu(B) + Ov`.

## 3. BK is vacuous where the defect lives (exact enumeration)

The run uses all `2^n` inputs at `p = 1/2`, with barrier schedule
`d = 26` plus 2 cleanup layers. `mu(A box B)` is computed exactly by
subset convolution (ranked zeta/Möbius). These small networks do sort.
"mid" means a comparator touching the middle half of the wires. The
table gives stage sums over the stage's middle comparators.

| `n` | `t` | `mu(A n B)` | `mu(A)mu(B)` | `mu(A box B)` | overlap-only share |
|---:|---:|---:|---:|---:|---:|
| 14 | 3 | 1.336 | 1.336 | 1.336 | 0.00 |
| 14 | 6 | 1.065 | 0.911 | 0.407 | 0.62 |
| 14 | 9 | 1.354 | 1.242 | 0.517 | 0.62 |
| 14 | 11 | 0.725 | 0.563 | 0.029 | 0.96 |
| 14 | 13 | 0.452 | 0.321 | 0.001 | 0.998 |
| 14 | 15–20 | | | 0.000 | 1.000 |
| 12 | 11–17 | | | `<= 0.01` | 0.97–1.00 |

- Edge comparators carry covariance below 0.01. Even there, most of that
  covariance is overlap-only.
- In the last ~`log2 n` stages, BK's left side `mu(A box B)` is 0. So
  `mu(A box B) <= mu(A)mu(B)` says nothing, and the joint mass is
  unconstrained below `min(mu(A), mu(B))`.
- At the sorted endpoint, a zero certificate of wire `j` has `j+1` inputs.
  Two disjoint certificates of middle wires `j, j'` would need
  `j + j' + 2 > n` zeros, so `mu(A box B) = 0` for every middle pair. The
  correct network is maximally overlap-correlated:
  `mu(out_j = 0, out_{j+1} = 0) ~ 1/2` against a product of `1/4` at the
  median.

So a potential that charges correlation charges the target. This is the
measure-theoretic form of the LB-24 saturation: certificates of size
`~n/2` all intersect.

## 4. The defect is an amplification deficit (independent vs. actual)

**Middle-wire threshold width** (10% to 90% in `p`) at `n = N_d`. The
independent model uses a 400-point `p` grid. The actual-network widths are
sampled (1024 permutations, 96-point grid).

| `d` | `N_d` | width, independent | width, sorted | `log2` ratio | width, actual |
|---:|---:|---:|---:|---:|---:|
| 36 | 76 | 0.042 | 0.146 | -1.80 | 0.150 |
| 40 | 161 | 0.040 | 0.101 | -1.34 | 0.110 |
| 44 | 344 | 0.036 | 0.069 | -0.93 | 0.080 |
| 48 | 738 | 0.034 | 0.047 | -0.49 | 0.059 |
| 52 | 1593 | 0.033 | 0.032 | 0.05 | 0.048 |
| 56 | 3459 | 0.030 | 0.022 | 0.47 | 0.039 |
| 60 | 7545 | 0.031 | 0.015 | 1.04 | |
| 64 | 16530 | 0.029 | 0.010 | 1.46 | |
| 68 | 36352 | 0.028 | 0.0070 | 2.02 | |
| 72 | 80209 | 0.028 | 0.0056 | 2.33 | |

At `d = 72` the sorted width is close to the grid spacing (0.0025), so its
ratio is grid-limited. Slopes use `d <= 68`. At `d = 64` (512 samples,
64-point grid) the actual width is 0.034, against 0.030 independent.

On the barrier schedule the middle wires get `O(1)` effective
amplification. The skip-wide rule idles over-wide middle blocks, and the
late width restriction only allows short comparators.

At small `d`, the independent model is too *sharp*, sharper than any
function of `n` inputs can be. That is the `n`-input analogue of the size
cap: dependence is forced. At large `d` it is too *flat*. In the large-`d`
regime its window violations track the actual network's almost exactly
(`V_ind` vs `V_true` at `d = 52`, `s = 4, 3, 2`: `0.087/0.113`,
`0.173/0.187`, `0.211/0.221`; at `d = 64`, `n = 16530`, 512 samples,
`s = 8, 7, 6`: `0.18/0.22`, `0.32/0.37`, `0.39/0.42`). The defect of the actual network is
therefore already present without any correlation. Correlation only makes
it slightly worse: the actual widths are 1.2 to 1.5 times the independent
ones.

**`c` on the barrier schedule.** The independent width deficit grows at
0.125 bits per stage, which is `c ≈ 0.25` bits of `n` per stage.

The truth scan (sampled `V_s <= 0.02` for all `s <= 14`) finds the largest
`n` at which the barrier network approximately sorts:

| `d` | 24 | 28 | 32 | 36 | 40 | 44 | 48 |
|---|---:|---:|---:|---:|---:|---:|---:|
| `n_true` | 27 | 29 | 32 | 35 | 38 | 41 | 41 |
| `log2(N_d/n_true)` | -1.75 | -0.69 | 0.17 | 1.12 | 2.08 | 3.07 | 4.17 |

The slope is about `0.25` per stage, and `n_true` stalls. The barrier
schedule is exponentially far from sorting, with `c ≈ 0.25`, about 12 times
the `0.02` a 3.5 rate needs. This is a property of that one schedule, not
a lower bound.

## 5. Kill test, and what a rate-bearing potential would need

**Kill test: passed, so the potential class is dead.**

- Harris-type potentials pass at `N_d` up to polynomial factors exactly
  when sizes do (§2), and LB-02/LB-24 showed that sizes do.
- BK adds nothing on middle wires (§3).

The events that look independent are the low-height edge certificates
counted by Kahale's bound, which are tree-like (§3 edge rows: covariance
`< 0.01`). There BK and Harris are both nearly equalities, and that is why
3.2706 is the "read-once" barrier. Boppana showed that read-once monotone
formulas amplifying `(p - 1/n, p + 1/n)` to `(1/4, 3/4)` need size
`Omega(n^alpha)`, with `alpha = log_{sqrt5 - 1} 2 = 3.27`. This was
verified: Dubiner–Zwick, SIAM J. Comput. 26(1), 1997, attribute it to
Boppana (1989) and show Valiant's construction is optimal for read-once
formulas. `alpha` is exactly `1/(1 - log2 phi)`. The coincidence is real:
the per-stage factor `4/phi^2` is the same.

**No positive `c` from correlation**, so there is no correlation theorem
chain to state. The only rate-bearing chain the data suggest is for
amplification:

```text
(A1) sorting  =>  middle wire i ~ n/2 has threshold width <= C n^(-1/2)
                  (exact: q_i = T_{i+1}),
                  i.e. total influence I(f_i) >= c sqrt(n)
                  (Russo-Margulis: dq/dp = I / (p(1-p)))
(A2) per-layer influence growth bound: for a = min, b = max of (u, v),
     I(a) + I(b) <= kappa * (I(u) + I(v)) with kappa depending on the
     correlation of the pivotal events of u and v
(A3) combine with Kahale's edge counts on the same schedule
     => n <= N_d 2^(-c d)
```

The weakest step is (A2). The sound worst-case factor is the sum rule,
which gives growth 4 per two layers against read-once's `4/phi^2 = 1.53`.
Any gain over the sum rule must come from pivotal-event correlation, and
that is the same saturated object as §3. (A3) is also unproven. The
optimal schedule could amplify middle wires in otherwise idle slots. Read
once, middle sharpness alone costs only about `1.64 log2 n` stages, far
below `3.27 log2 n`. No Lean is warranted. If (A2)–(A3) ever closed, Lean
would need the Russo–Margulis formula, the influence calculus of
AND/OR under `mu_p`, and the barrier-schedule interaction lemma.

**Recommended next step (cheap kill test for the amplification route).**
Build a *hybrid* schedule: the barrier schedule plus read-once-optimal
middle amplification placed in idle slots, respecting (W). Check
Kahale/LB-24 feasibility and the independent-model middle width at `N_d`.
If both pass, then even the optimistic read-once amplification potential
cannot beat 3.2706. Any sound influence bound is at least as permissive,
so amplification-plus-Kahale would be dead too, and the remaining live
route is LB-34 (mixed-polarity restriction families).

## Literature check

Searched 2026-10-24. No depth lower bound beyond `(3.27 - o(1)) log2 n`
is known.

- Kahale, Leighton, Ma, Plaxton, Suel, Szemerédi (STOC 1995) remains the
  record.
- Two later papers still cite it as the record:
  - Dobrokhotova-Maikova, Kozachinskiy, Podolskii, ITCS 2023
    ([ECCC TR22-116](https://eccc.weizmann.ac.il/report/2022/116/download));
  - Kozachinskiy and Podolskii, *Towards simpler sorting networks and
    monotone circuits for majority*, APPROX/RANDOM 2024
    ([LIPIcs](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.APPROX/RANDOM.2024.50),
    [ECCC TR23-153](https://eccc.weizmann.ac.il/report/2023/153/download)).
- Recent work found in the search is fixed-`n` *upper* bounds, e.g. depth
  13 for 27–28 channels, [arXiv 2511.04107](https://arxiv.org/abs/2511.04107).
- Read-once amplification:
  [Dubiner–Zwick, SIAM J. Comput. 1997](https://epubs.siam.org/doi/10.1137/S009753979223633X)
  states Boppana's bound and Valiant's `O(n^(alpha+2))`.

The search was not exhaustive for 2025–26.

## Reproduce

Run from the repository root (about 10 minutes in total, single core).

```sh
S=lower-bound/experiments/scripts/kahale_correlation_potential.py
python -B $S bk 10 12 14 --depth 26
python -B $S ind 32 36 40 44 48 52 56 60 64 68 72 --P 400 --smax 14
python -B $S truth 36 40 44 48 52 56 --samples 1024 --smax 14
python -B $S scan 24 28 32 36 40 44 48 --models truth --samples 1024
```

Outputs: [`kahale-correlation-potential-output.txt`](kahale-correlation-potential-output.txt).
These are finite computations of a relaxation, exact enumerations and
sampled runs of the actual network. They make no sorting claim and add no
Lean.
