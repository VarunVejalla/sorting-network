# Round 2 of the walk bound: weak duality and negative association

UB-29 · 2026-10-18 · Claude (Opus 5.5). **Claim level: hand proof (unaudited) of BULK2's round-2
predicate; the deterministic steps are checked exhaustively on small cases, the probabilistic step
in simulation.** This replaces the round-2 sketch of `WALK-BOUND.md` §4 and closes obligation 1 of
`README.md`. Notation follows `WALK-BOUND.md` and `upper-bound/best/notes/two-round/BULK2.md`.

## Summary

The sketch bounded the round-2 excess by peeling plus Cauchy–Schwarz. That left an unproved
concentration step and a `ln ln m` factor. Both disappear with two changes:

1. **Weak duality** in place of peeling. For any fixed `lam > 0`,
   `sum_j X_j(delta_j) <= lam * sum_j |delta_j| + sum_j Y_j(lam)`, where
   `Y_j(lam) = sup_h (X_j(h) - lam |h|)` is the supremum of a walk with drift `-lam`. Each `Y_j` is
   dominated by exponentials (Ville's inequality), with no union over scales.
2. **Negative association** in place of McDiarmid. Within a row the indicators `[sigma_r(j) in S]`
   form a uniformly random `s`-subset, which is negatively associated (NA). Each `Y_j` is a monotone
   function of its own column, so `E exp(t sum_j Y_j) <= prod_j E exp(t Y_j)`. Chernoff then gives
   the union over `S` and the base row at its true cost.

| | BULK2 route | walk sketch (WALK-BOUND §4) | **this note** |
|---|---|---|---|
| round-2 constant `C2` in `d = 2 C2 sqrt(E1/m)`, `lg m = 39`, `n = 16` | — (carries `sqrt(ln m)`) | 2.95 | **1.66** |
| `lg m` for the 1419 package's bulk target `d = 1/59e6` | 41.66 | 38.65 | **37.53** (37.57 for all `n >= 16`) |
| status | proved (Lean) | sketch | hand proof |

The same NA argument also re-proves round 1, but that gains only 1% (`K1` 1.174 → 1.162 at
`n = 16`). The round-1 proof of `WALK-BOUND.md` §3 stays, and `E1` is taken from either route.

## 1. Statement

**Setting.** `sigma = (sigma_r)_{r<m}` are independent uniform permutations of the `n` columns.
For a set `S` of output columns, `s = |S|`, `p = s/n`, and a column `j`, put
`xi_{r,j} = [sigma_r(j) in S]` and `W_j(h) = sum_{r<h} (xi_{r,j} - p)`. For a base row `b`, put
`X_j^b(delta) = W_j(b + delta) - W_j(b)` for `-b <= delta <= m - b`.

**Theorem R2.** Fix `m, n >= 2`, `R > 0`, `eta in (0,1)`, a grid `Gamma` of `G` base rows such that
every `i in [1, m]` has some `b in Gamma` with `|i - b| <= g/2`, and, for every `s = 1..n-1`, numbers
`lam_s > 0` and `0 < t_s < min(theta_+, theta_-)` (defined in §3). Put `R' = R + n g / 2` and

```text
x_s = ( n ln M_s(t_s) + ln binom(n, s) + ln G + ln((n-1)/eta) ) / t_s ,
M_s(t) = al/(al-t) + be/(be-t) - (al+be)/(al+be-t),   al = theta*(p, lam_s),  be = theta*(1-p, lam_s).
```

Then, with probability at least `1 - eta` over `sigma`, every state `c'` of exact mass
`total(c') = n i` with `sum_j |c'_j - i| <= R` satisfies

```text
onesAboveBottom(c', sigma, i)  <  max_{1<=s<n} ( lam_s R' + x_s ).
```

(Strict, because the excluded event is `sum_j Y_j >= x_s`.)

**Use in BULK2.** Round 2's admissible states have exact mass and `exc(c', i) < (E1/2) m n`, so
`sum_j |c'_j - i| = 2 exc < E1 m n =: R`. If the right-hand side is below `(d/2) m n`, then
`HasCombinatorialPropertyB2 sigma2 E1 d` holds. The theorem holds for every admissible `c'` at once,
so it applies to the random `c'` produced by round 1; `sigma2` need not be independent of `sigma1`.

**Orientation.** BULK2 and Lean put a column's ones at the high row indices. Reversing the row
order (`sigma_r -> sigma_{m-1-r}`, and `b -> m - b` on the grid) is a measure-preserving bijection
of scrambles that carries Lean's `onesAboveBottom` onto the one used here, as `WALK-BOUND.md` §6
records for round 1. So the theorem transfers verbatim.

## 2. Deterministic part (exact)

Fix `S`, a state `c'` of mass `n i`, and any base row `b`.

1. **Reduction.** As in `WALK-BOUND.md` §2, `sum_{T in S} count(T) = sum_j N_j(c'_j)`. At exact mass,
   `i s = p sum_j c'_j`, so `sum_{T in S} (count(T) - i) = sum_j W_j(c'_j)`, with equality.
2. **Any base row works.** `sum_j W_j(b) = sum_{r<b} (sum_j xi_{r,j} - n p) = sum_{r<b} (s - s) = 0`,
   because each row's permutation puts exactly `s` of the columns into `S`. Hence
   `sum_j W_j(c'_j) = sum_j X_j^b(c'_j - b)`.
3. **Weak duality.** `X_j^b(delta) <= lam |delta| + Y_j^b(lam)` for every `delta`, by definition
   of `Y_j^b(lam) = max_{-b <= h <= m-b} (X_j^b(h) - lam |h|) >= 0`. Summing over `j`,
   `sum_j W_j(c'_j) <= lam sum_j |c'_j - b| + sum_j Y_j^b(lam)`.
4. **Grid.** Taking `b in Gamma` with `|i - b| <= g/2`, `sum_j |c'_j - b| <= R + n g/2 = R'`.
5. `onesAboveBottom(c', sigma, i) = max_S sum_{T in S} (count(T) - i)` (take `S` the columns above
   `i`). Sizes `s = 0` and `s = n` give 0, so `1 <= s <= n-1` suffice.

So `onesAboveBottom(c', sigma, i) <= max_{s} max_{|S| = s} max_{b in Gamma} (lam_s R' + sum_j Y_j^{S,b}(lam_s))`,
and the right-hand side depends on `sigma` only. Steps 1–3 and 5 are checked exhaustively in
`check_round2.py` part (1): every exact-mass state, every `S`, every base row, and
`lam in {0, 0.1, 0.3, 1}`, for 4 random scrambles at `(m, n)` = (4,4), (5,4), (6,5), (5,5), (8,4).

## 3. One column: exponential domination

Fix `S`, `b`, `lam` and a column `j`. The `xi_{r,j}`, `r < m`, are independent Bernoulli(`p`):
`sigma_r(j)` is uniform, and different rows use independent permutations.

* **Forward side.** `U_h = sum_{r=b}^{b+h-1} (xi_{r,j} - p - lam)`. Let `theta* = theta*(p, lam)` be
  the positive root of `ln(1 - p + p e^theta) = theta (p + lam)`. It exists and is unique when
  `p + lam < 1`: the left side minus the right is convex in `theta`, 0 at `theta = 0`, with slope
  `-lam` there and slope `1 - p - lam > 0` at infinity. Then `exp(theta* U_h)` is a non-negative
  martingale with mean 1, so Ville's inequality gives `P(Y_+ >= x) <= exp(-theta* x)` for
  `Y_+ = max_h U_h`. If `p + lam >= 1` every increment is `<= 0` and `Y_+ = 0`.
* **Backward side.** `X_j^b(-h) - lam h = sum_{r=b-h}^{b-1} ((1 - xi_{r,j}) - (1-p) - lam)`. That is
  the same walk for Bernoulli(`1-p`), so `P(Y_- >= x) <= exp(-theta*(1-p, lam) x)`.
* `Y_j = max(Y_+, Y_-)`, and `Y_+, Y_-` are independent (disjoint rows). With `al, be` the two
  rates, `P(Y_j >= x) <= 1 - (1 - e^{-al x})(1 - e^{-be x})`, and integrating
  `E e^{t Y_j} = 1 + int_0^inf t e^{t x} P(Y_j >= x) dx` gives `E e^{t Y_j} <= M_s(t)` for
  `t < min(al, be)`.

For small `lam`, `theta* ≈ 2 lam / (p(1-p))`: `Y_+` is about exponential with mean `v/(2 lam)`,
the classical supremum of a Brownian motion with drift. `check_round2.py` part (2) compares the
simulated tail with `e^{-theta* x}` at `p = 1/2, 1/16, 15/16`. The bound holds within sampling
error (4000 trials; at `p = 15/16` one entry reads 0.051 against 0.050, standard error 0.0035). It is
nearly tight at `p = 15/16`, where the walk is close to a diffusion, and loose by about 10% elsewhere.

## 4. Across columns: negative association

Joag-Dev and Proschan (Ann. Statist. 11, 1983) give the following properties of negative
association.

* **(P1)** A random permutation of a fixed vector is NA (their Theorem 2.11). So for each row `r`,
  `(xi_{r,j})_j`, the indicator of a uniform `s`-subset, is NA, and so is `(1 - xi_{r,j})_j`.
* **(P2)** A union of independent NA families is NA (their P7).
* **(P3)** Non-decreasing functions of disjoint sets of NA variables are NA (their P6).
* **(P4)** If `Y_1..Y_n` are NA and `t >= 0`, then `E exp(t sum Y_j) <= prod E exp(t Y_j)`. This
  follows from the definition, by induction with the non-negative non-decreasing functions `e^{t y}`.

Fix `S` and `b`. Put `zeta_{r,j} = xi_{r,j}` for `r >= b` and `zeta_{r,j} = 1 - xi_{r,j}` for
`r < b`. By (P1) and (P2), `{zeta_{r,j}}` is NA, since the rows are independent. By §3, `Y_j` is a
coordinatewise non-decreasing function of column `j`'s variables `(zeta_{r,j})_r`. The forward
walk increases in `xi` on rows `>= b`, and the backward walk increases in `1 - xi` on rows `< b`. By
(P3) `(Y_j)_j` is NA, and by (P4) `E exp(t sum_j Y_j) <= M_s(t)^n`.

## 5. Union and conclusion

By Markov, `P(sum_j Y_j^{S,b}(lam_s) >= x_s) <= M_s(t_s)^n e^{-t_s x_s} = eta / ((n-1) binom(n,s) G)`.
Summing over `s`, the `binom(n, s)` sets of size `s` and the `G` grid rows gives at most `eta`.
Outside that event §2 applies, which proves Theorem R2. ∎

Round 2 needs no Freedman or McDiarmid inequality, only Ville's inequality, the Bernoulli moment
generating function, and the four NA facts. (Round 1's NA variant in `na_precision.py` still uses
Freedman's tail for each column maximum.)

## 6. Numbers

`na_precision.py` minimizes over `lam_s` and `t_s`, and over the grid spacing
`g ≈ gamma E1 m` (rounded to an odd integer) with `gamma in {0, 0.0025, …, 0.2}`. For
`lg m >= 30` the best is `gamma = 0.02`, an interior optimum (0.01 and 0.05 are both worse), and
0.05 is best below that. It roughly halves the `ln m` cost of the base-row union for a 1% increase
in `R`. Results at `n = 16`, `eta2 = 1/1000`
(BULK2's split), from `na_precision.out`:

| `lg m` | BULK2 `d` | sketch `d` | **R2 `d`** |
|---:|---:|---:|---:|
| 30 | 5.75e-6 | 1.47e-6 | 8.32e-7 |
| 39 | 6.44e-8 | 1.42e-8 | 7.91e-9 |
| 42 | 1.43e-8 | 3.01e-9 | 1.68e-9 |

`C2 = d / (2 sqrt(E1/m))` grows slowly, from 1.57 at `lg m = 20` to 1.67 at 42. The growth comes
only from the grid's `ln G ≈ ln(1/(gamma E1))` spread over `n` columns. It falls with `n`: 1.50,
1.40 and 1.32 at `n = 32, 64, 256` (`lg m = 39`).

**Tightness.** At `m = 4096`, `n = 16` and one fixed `S` and base row (`check_round2.py` part
(3)), the exact primal `sup { sum_j X_j(delta_j) : sum |delta_j| <= R }`, computed by a (max,+)
convolution, averages 169 for `s = 8`. The dual `lam R + sum Y_j` at the theorem's `lam` averages
170, and its 95% Chernoff bound is 210 against an empirical 95th percentile of 187. Duality and the
NA product therefore lose almost nothing. The remaining slack is the union over `S` and the base
rows, at about `ln 2 + (ln G)/n` per column.

**Uniformity in `n`.** BULK2's theorem is for all `n >= 16`. The per-column cost
`(ln binom(n,s) + ln G + ln((n-1)/eta))/n` is at most `H(p) + (ln G + ln(15/eta))/16` for every
`n >= 16`, because `ln((n-1)/eta)/n` and `ln(G)/n` decrease in `n`. The same holds in round 1, and
round 2 then takes the `n`-uniform `E1`. `na_precision.py` (`uniform=True`, `p` on a 1/64 grid)
gives, at `lg m = 37.5`, `E1` 5.27e-6 → 5.40e-6 and `d` 1.72e-8 → 1.76e-8. The bulk threshold moves
from 37.53 to **37.57**, and the re-pricing uses this form. A certificate still needs a rigorous
supremum over continuous `p in (0,1)`, which is a 1-D interval computation.

## 7. What remains for a certified round 2

* **Interval arithmetic.** `theta*`, the Chernoff minimizations and the supremum over `p` are
  floating point here. Any fixed `(lam_s, t_s, g)` gives a valid bound, so certification only has
  to evaluate the closed form of `x_s` in interval arithmetic at chosen rational parameters. No
  optimization needs to be certified. It must use a verified **lower** enclosure of each `theta*`
  (any `theta <= theta*` keeps the supermartingale), since a float root can sit slightly above the
  true one.
* **Lean.** NA of permutation distributions is not in Mathlib as far as I know. A Lean-friendlier
  replacement for (P1)–(P4) is the hypergeometric-to-binomial MGF comparison that BULK2 already uses
  (`avg_exp_hit_le`), but `Y_j` is not a sum over rows, so that lemma does not apply verbatim. The
  NA step is the main formalization cost.

## 8. Review (2026-10-18)

An independent reviewer, working in a fresh context, checked §1–§6 against BULK2.md and the code.
It reran both scripts and added two cross-checks of its own: `theta_star` and the round-1 MGF
integral against 50-digit mpmath, and a Monte Carlo test of `E e^{t Y_j} <= M_s(t)` and of the NA
product at `m = 400`, `n = 8`.

**Confirmed.**
* The theorem gives exactly BULK2's `HasCombinatorialPropertyB2`: quantifiers, exact mass and
  strictness.
* The §2 identities and the delta ranges.
* The Ville bound, the backward-walk mapping and the MGF formula.
* The legitimacy of the row-wise sign flip under NA, and the citations.
* The union accounting. The parameters are independent of `sigma`.
* The code's formulas. A suboptimal optimizer can only loosen the bound.
* All quoted numbers reproduce.

**Corrections (applied).**
1. The `n`-uniform form was incomplete: it still contained `n`, it ignored round 1, and no script
   produced its figure. It is now `uniform=True` in both rounds, with threshold 37.57 (§6).
2. Orientation is now addressed (§1).
3. The grid spacing is rounded to an odd integer, so `G = ceil(m/g)` is exact. Before, the code
   undercounted `G` by a negligible amount.
4. The outputs were regenerated.
5. Wording: "within sampling error" in §3, and the `gamma` search was refined in §6.
6. The rates are renamed `al, be`, because `b` is the base row.
7. Certification must use a lower enclosure of `theta*` (§7).

During the regeneration, `theta_star` overflowed for `p + lam` close to 1. It now uses the stable
form `theta + log(p + (1-p) e^{-theta})` for large `theta`.
