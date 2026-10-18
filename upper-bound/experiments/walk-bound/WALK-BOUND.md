# Walk-maximum bound: Property B without the union over input states

UB-29 · 2026-10-18 · Claude (Opus 5.5). **Claim level: round 1 is a hand proof (unaudited) whose
deterministic step is checked exhaustively on small cases; round 2 is a sketch.** Notation
follows `upper-bound/best/notes/two-round/BULK2.md`.

## Summary

Property B for a sort-based separator is currently proved by a union bound over all `(m+1)^n`
column-height vectors. That union is the source of the `ln m` in Lemma 6.1's
`E1 = sqrt(2(1+ln m)/m)`, and `backlog/ruled-out.md` (first item) records it as inherent to
union-bound arguments.

**Here the union over inputs is avoided altogether.** After centering by the mass, the excess
splits into a sum over input columns. The adversary's choice of each column's height becomes a
supremum of that column's own random walk, which a maximal inequality controls without any
union. Only a union over the `2^n` output sets `S` remains, costing `ln 2` per column instead of
`ln(m+1)`.

| | one round | two rounds |
|---|---|---|
| precision gain over the current route (`lg m` = 16 … 42) | 2.1x – 3.3x | 2.8x – 4.7x |
| column height for the 1419 package's bulk target `d = 1/59e6` | 58.0 → 54.1 | **41.66 → 38.65** |

(These figures use the constants as corrected by review, §6: swap-Lipschitz constant 1,
certified at the smallest column count `n = 16` with failure budget `eta = 1/100`, and round 2's
extra union over the base row `i`.)

(`walk_precision.py`, `walk_precision.out`.) The fringe proof (Property F) needs a matching
improvement before the 1419 design can use this, because its fringe binds at nearly the same
height.

## 1. Setting

A Boolean `m x n` matrix with sorted columns: column `j` holds `c_j` ones in its bottom rows
`0..c_j-1`. A row scramble applies independent uniform permutations `sigma_r` of the `n` columns,
one per row `r`. Output column `T` then holds

```text
count(T) = #{ r : c_{sigma_r^{-1}(T)} > r },     onesAboveBottom(c, sigma, i) = sum_T (count(T) - i)_+ .
```

BULK2's round-1 predicate: for every `c` and every `i` with `total(c) <= n i`,
`onesAboveBottom(c, sigma, i) < (E1/2) m n`.

## 2. The deterministic reduction (exact)

For a set `S` of output columns, `|S| = s`, `p = s/n`:

```text
sum_{T in S} count(T) = sum_r |sigma_r(H_r) ∩ S| = sum_j N_j(c_j),   N_j(h) = #{ r < h : sigma_r(j) in S },
```

where `H_r = {j : c_j > r}`. Since `total(c) <= n i`, we have `i s >= sum_j c_j p`. Hence

```text
sum_{T in S} (count(T) - i) <= sum_j W_j^S(c_j),   W_j^S(h) = sum_{r<h} ( [sigma_r(j) in S] - p ),
```

and so, for every `c` and `i` at once,

```text
onesAboveBottom(c, sigma, i) = max_S sum_{T in S}(count(T) - i) <= B(sigma) := max_S sum_j max_{0<=h<=m} W_j^S(h).
```

`B` depends only on `sigma`. **Check:** `check_walk_bound.py` verifies the inequality over all
`c` and all admissible `i` for 30 random scrambles at `(m,n)` = (4,4), (5,5), (6,5), (6,6), (8,5).
It holds in every case, and the ratio true worst case / `B` is up to 1.00, so the reduction is
often exactly tight (`check_walk_bound.out`).

## 3. Round 1: bounding `B`

Fix `S`. For column `j`, the increments `[sigma_r(j) in S] - p` are independent over `r` with
variance `p(1-p)`, because different rows use independent permutations. Write
`F(S) = sum_j max_h W_j^S(h)`.

* **Mean.** By Freedman's maximal inequality for a martingale with unit-bounded increments and
  variance `v = m p(1-p)`, `P(max_h W >= x) <= exp(-x^2/(2(v + x/3)))`. Integrating,
  `E max_h W_j^S(h) <= sqrt(pi v/2) (1 + o(1))`. So `E F(S) <= sqrt(pi/2) n sqrt(m p(1-p))`.
* **Concentration.** `F` is a function of the `m` independent random `s`-subsets
  `sigma_r^{-1}(S)`. Swapping one element of one row's subset flips two increments, changing two
  walks by 1 from that row on, hence `F` by at most 2. McDiarmid's inequality for random subsets
  (cited in UB-20's LATERAL-LEMMA.md and confirmed by its reviewer) gives
  `P(F - E F >= t) <= exp(-t^2/(2 m min(s, n-s)))`.
* **Union over `S`.** At most `binom(n,s) <= exp(n H(p))` sets of each size. With
  `t_s = sqrt(2 m min(s,n-s) (n H(p) + ln(2n/eta)))`, the total failure probability is at most
  `eta`.

Therefore, with probability at least `1 - eta`, for every input and every `i`:

```text
onesAboveBottom <= n sqrt(m) max_p [ sqrt(pi/2) sqrt(p(1-p)) + sqrt(2 p' H(p)) ] + o(n sqrt m)
                = 1.459 n sqrt(m),      p' = min(p, 1-p),  maximum at p = 1/2,
```

so `E1_new = 2.92/sqrt(m)`, against Lemma 6.1's `sqrt(2(1+ln m)/m)`.

**Empirical scale.** A local search over `S` at `m` up to 1024 finds `B ≈ 0.53 n sqrt(m)`
(`scale_walk_bound.out`). That is about 2.7 times below the theorem's constant, which is mostly
the union over `S`, so the constant can probably be sharpened.

## 4. Round 2 (sketch)

Round 2 acts on `c'`, the round-1 column counts at the same threshold, with exact mass
`n i` and `sum_j |c'_j - i| = 2 exc(c', i) < R := E1 m n` by round 1. The reduction of §2 applies
with `sigma2`, and since `sum_j W_j^S(i) = sum_{r<i}(s - s) = 0` exactly,

```text
onesAboveBottom(c', sigma2, i) <= max_S sup_{ delta : sum_j |delta_j| <= R } sum_j X_j^S(delta_j),
X_j^S(delta) = W_j^S(i + delta) - W_j^S(i)     (a two-sided walk from row i).
```

**Peeling.** Let `Z_j(L) = max_{|h| <= L} X_j(h)` and `Q_j = max_q Z_j(2^q)^2 / 2^q`. For
`2^q <= L_j < 2^{q+1}`, `Z_j(L_j) <= sqrt(2 L_j Q_j)`, so by Cauchy–Schwarz

```text
sum_j Z_j(|delta_j|) <= sqrt( 2 R sum_j Q_j ).
```

Each `Q_j` is a maximum over `log2 m` scales of normalized walk maxima with sub-Gaussian tails
`P >= y` at most about `2 e^{-y/(2v)}`, `v = p(1-p) <= 1/4`. So `E Q_j <= 2v(ln(2 log2 m) + 1)`.
Allowing `2 ln 2` per column for the union over `S` gives
`sum_j Q_j <= 2 n v (ln(2 log2 m) + 1 + 2 ln 2)` with high probability. With `v = 1/4`:

```text
d_new = 2 sqrt( E1 (ln(2 log2 m) + 1 + 2 ln 2) / m )  ~  m^{-3/4} sqrt(ln ln m).
```

BULK2's route instead gives `d ~ sqrt(E1 ln m / m)`, with `E1` itself carrying a `sqrt(ln m)`.

**Not yet proved in round 2:** the concentration of `sum_j Q_j` across the `2^n` sets `S`. The
`Q_j` are dependent through the row permutations, and they are not uniformly Lipschitz, so
McDiarmid does not apply directly; this needs Bernstein-type concentration or another peeling.
The `2 ln 2` allowance per column is a placeholder.

## 5. What this does and does not change

* **It applies to every sort-based separator** in the repository (the 1419 package, tapered,
  lateral), wherever Property B is the binding constraint. It does not change the network, only
  the proof of its guarantee.
* **The fringe (Property F) is untouched.** F2ROUND uses its own counting (tops and Y-counts over
  truncated profiles). At the 1419 parameters the fringe binds at `lg m ≈ 41.65`, about the bulk's
  old threshold, so using the bulk gain there needs a walk-type fringe argument too. That is the
  natural next item.
* **Rigor.** §2 is exact. §3 is a complete hand proof modulo Freedman's maximal inequality and
  McDiarmid's inequality for random subsets, both standard. §4 is a sketch. Nothing is in Lean.

## 6. Review (2026-10-18)

An independent reviewer checked §2–§4 against BULK2.md, the Lean predicate, and ruled-out.md.

**Confirmed.**
* §2 is correct in both orientations. In Lean's convention (ones at high row indices, `sigma r`
  acting on the columns of row `r`) the walks run downward. The suffix version of `B` for `S`
  equals the prefix version for the complement of `S`, because `sum_j W_j^S(m) = 0`. The reviewer
  re-checked this exhaustively in Lean's orientation.
* The argument genuinely avoids the union over inputs. ruled-out.md's "inherent" claim applies
  only to arguments that union over inputs.
* §3's independence over rows, the Freedman maximal inequality, and slice McDiarmid all hold.
* The result proves the same predicate, `HasCombinatorialPropertyBOnPipeline sigma E1`, with the
  same quantifiers, so BULK2 round 2 can take the smaller `E1` directly.

**Corrections (applied in `walk_precision.py`).**
1. **The swap-Lipschitz constant is 1, not 2.** A swap lowers one walk and raises another by 1,
   moving their maxima in opposite directions. This improves `K1` to 1.043 as `n -> infinity`.
2. **The `n`-dependent term is not `o(1)`.** `t_s` contains `ln(2n/eta)`, so the constant is
   `K1(n, eta) = max_p [ sqrt(pi/2) sqrt(p(1-p)) + sqrt(p'(H(p) + ln(2n/eta)/n)/2) ]`. That is
   **1.174 at `n = 16`, `eta = 1/100`**, the value used for certification.
3. **The mean's `o(1)` is a rigorous `+2/3` per column** (numerical integration of Freedman's
   tail), which is negligible.
4. **Round 2 needs a union over the base row `i`.** `X_j^S` depends on `i`, and with no union
   over `c'` the bound must hold for every `i`. That adds `(ln m + ln(1/eta))/n` per column, so
   `K2 = ln(2 log2 m) + 1 + 2 ln 2 + (ln m + ln(1/eta))/n`. At `n = 16` the 1419 bulk threshold is
   then 38.65 instead of 38.62.

**Still open (round 2).**
* A Bernstein-type tail for `Q_j` valid for every `p`; the claimed sub-Gaussian tail fails for
  small `p`. Its claimed mean holds in simulation, at ratios 0.48–0.71.
* Concentration of `sum_j Q_j`, uniformly over `S` and `i`, under the within-row dependence
  (negative association may work).

**Lean cost.** Freedman's maximal inequality and slice McDiarmid are not in Mathlib, as far as
the reviewer knows. Lemma 6.1's interface (`lemma61FailBound_onPipeline`, `heps`, the
Theorem 5.1 parameter constraints) would be replaced.
