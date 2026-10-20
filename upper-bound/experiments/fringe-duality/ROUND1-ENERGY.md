# The round-1 energy problem (UB-34)

Claude (Opus 5.5), 2026-10-20. Research note: problem statement, facts and candidate routes. No
result yet.

## Statement

Take `σ = (σ_0, …, σ_{m−1})`, independent uniform permutations of `[n]` (one per row). An adversary
picks, **after seeing σ**, a nested family `H_0 ⊇ H_1 ⊇ … ⊇ H_{m−1} ⊆ [n]` with `Σ_r |H_r| = j`. This
is the staircase of input column heights after the first column sort. Output heights are
`z_T = #{r : σ_r⁻¹(T) ∈ H_r}`. We need, with high probability over σ and for every family at once,

    E = Σ_T z_T²  ≤  C₁ j + C₂ j²/n          (or the centred E_b = Σ_T (z_T − b)₊² ≤ C₁ j)

with small constants. Round 2 of the fringe needs `E` (its convex-cost duality charges `μ E`). Today
the bound is `E ≲ 120–180 j`; the 731.25 fringe needs roughly `E ≲ 10 j`.

## Facts

1. **Pair identity (exact).** `E = j + 2 Σ_{r<r'} |σ_r(H_r) ∩ σ_{r'}(H_{r'})|`.
2. **Fixed family.** Each row is an independent uniform `|H_r|`-subset of targets. `z_T` is
   Poisson-binomial with mean `j/n` for every `T`, and the `z_T` are negatively associated. So
   `E[E] ≤ j + j²/n`, and tall columns are super-exponentially rare: `P(z_T ≥ k) ≤ (e j/(n k))^k`.
3. **True worst case** (`adversary_energy.py`). A structured attack reaches `E/j ≈ 3` in the sparse
   regime and `≈ 3 + j/n` in general: pick targets `A` and set `H_r ⊇ σ_r⁻¹(A)` for `r < k`, at cost
   about `|A| k²/2`. Greedy local search does worse. So the target is `C₁ ≈ 3–5`, `C₂ ≈ 1`.
4. **Why duality plus union over output sets loses.** The per-set walk duality
   (`Σ_{T∈S} z_T ≤ λ j + Σ_c max_h (N_c^S(h) − λ h)`) is near-tight for each set. But a union over
   sets `S` of size `s` costs `s ln(en/s)`, and for moderately tall columns (`k ≲ ln(n)/t`) that cost
   lets `s_k ≈ j/k`. Summing over scales loses a factor of order `ln n`.
   * Weighting the scales jointly with one λ fails: one Chernoff parameter cannot serve jump sizes
     from 1 to `√j`.
   * Splitting the scales reintroduces separate `λ_g j` budgets.
5. **Why a union over families loses.** The number of families is `exp(Θ(min(n, j) ln))`, comparable
   to the whole mass budget. The walk bound avoided this union; the energy needs it in some form.

## Candidate routes

* **(a) Rank structure.** Order each target's hits by row. The `i`-th hit is at a row `≥ i − 1`, so
  its source column has height `≥ i`. `E = Σ_{hits} (2·rank − 1)`. A high-rank hit needs a source
  column that is tall *and* whose cell lands on an already-hit target. For tall input columns this
  stacking is rare (random targets), which is what the pair identity measures. Goal: charge each pair
  `(r < r')` collision to the mass of the cheaper of the two cells, and union only over the "cheap"
  low-row structure (rows `< R`, entropy `~ Σ_{r<R} |H_r| ln`), handling rows `≥ R` by
  concentration for the fixed low part.
* **(b) Chaining over nested families.** `X_{rr'} = |σ_r(H_r) ∩ σ_{r'}(H_{r'})|` is a U-statistic in
  the independent rows. Generic chaining over the nested families with the `j`-mass constraint may
  give `E − E[E] = O(j)` with the entropy measured at the right scale (sets of size `|H_r|` at each
  row) instead of all families at once.
* **(c) Truncate and duality.** `E ≤ L j + Σ_{z ≥ L} z²`. Bound the tall part with the set duality
  restricted to `s ≤ j/L²` (small entropy). The obstruction in fact 4 applies only to `k ≲ ln n`,
  i.e. to the part already covered by `L j`. Feasibility depends on `L ≈ ln(n)/t` being small enough;
  with `t ∝ ln n` it is `O(1)`. **This is the cheapest test**: rerun `s_profile_fast` with
  `t ∝ ln n` and the `L j` truncation, and see whether the tall part stays `O(j)`.

## Findings (2026-10-20)

**Route (c) is ruled out.** `n = 2^20`, `j = 600000` (`s_profile_fast`, `t ∝ ln n`):
* `s_k = j/k` (the trivial cap) for `k ≤ 12`.
* For `k ≥ 50`, `s_k ≈ 4–5 × 2j/k²`.
* `E/j = 116`. Truncation at `L j` with `L` from 5 to 40 leaves 104–114 `j`.

**Per-height bounds lose `ln K` in principle.** Even the exact cost profile `s_k = 2j/k²`, summed as
`Σ(2k−1)s_k`, gives `4j ln K ≈ 28 j`. The per-height maxima cannot hold at once, since they share the
mass `j`; the true worst case is `≈ 3 j`. **Any proof must be joint across heights.**

**Route (a), useful-hit charging.** For a set `A` of tall targets, order each target's hits by row:
`Σ_{T∈A} z_T²/2 ≤ Σ_{T∈A} Σ_i (r_i + 1) = Σ_c W_c`, where `W_c` sums `(r + 1)` over column `c`'s
cells `r < h_c` that land in `A`. If a column has at most one such cell, `W_c ≤ h_c`, so
`E_A ≤ 2 j + 2 · (multi-use bonus)`. The bonus comes from columns with two or more useful cells.
* The union then runs only over the small set `A`.
* As written the bonus bound `(U_c − 1)₊ h_c` is too crude: full-height input columns, which only
  create background, are charged `~ m s/n` each.
* The next step is to separate the background (charged through `j²/n`, the `C₂` term) from genuine
  stacking. For example, weight a column's useful cells by their rank in their own targets rather
  than by row.

## Route (d): energy only on round-2 source sets (2026-10-20, promising)

The fringe bound always binds at one round-2 column `v`, with `w_v = #{r : z_{u_r} > r}`, where
`u_r = σ₂,r⁻¹(v)`. Only rows `r < K` matter, `K ≥ max z ≈ (6j)^{1/3}`. So round 2 needs the round-1
energy **only on the source set** `U_v = {u_r : r < K}`. It has `K` columns, is fixed by `σ₂` and `v`,
and needs a union over just `n` choices of `v` (or over round-2 sets `S`, with `U = ∪_{r<K} σ₂,r⁻¹(S)`).

1. **Cost.** The `W` rows with `z_{u_r} > r` force `Σ_{T ∈ U_v} z_T² ≥ Σ_{i<W} (i+1)² ≈ W³/3`.
2. **Round-1 energy on U.** Take weights `a_T = z_T ≤ K` on `U`, and weighted duality with one λ.
   * The main term is deterministic: each target has one source per row, and
     `Σ_r (a_T − λ(r+1))₊ ≈ a_T²/(2λ)`.
   * Other hits in the same input column (the background of `U`) reduce the drift by
     `ρ_U = Σ_{T∈U} a_T/n ≲ K²/(2n)`.
   * So `Σ_{U} z² ≤ λ j + Σ_U z²/(2(λ − ρ_U)) + dev`, i.e. `Σ_U z² ≲ 2(1 + ρ_U) j + O(dev)`.
3. **Deviation and union.** The union runs over `(v, a|_U)`: entropy `≈ ln n + K ln K`. Weights are
   at most `K`, so a Bernstein/Chernoff deviation costs about `K · (entropy) ≈ K² ln(nK)`. With
   `j ≈ K³/6` this is about `(6 ln(nK)/K)·j`, **small relative to `j`**. That is the point: heavy weights
   only appear when the mass is already cubic in `K`.
4. Hence `W ≲ (6(1 + ρ_U)(1 + o(1)) j)^{1/3}`, the heuristic optimum up to `(1 + ρ_U)^{1/3}`.
   * Dense regime: centre at `b = j/n`; `w − b ≲ (3 E_{b,U})^{1/3}`.
   * Multi-column escapes follow from the cost `≈ (f − b + e)³/3` per column with excess `e`, so
     escapes are `≲ 0.9 j/f²`.
   * Prediction: `f ≈ √(0.9 J)·(1 + small)`, i.e. about 1300 at `J = 1.66e6`, against the ceiling 4023.

**To do.** Make step 3 rigorous: the collision term with weights, Bernstein over the union, and
`ρ_U` as a random quantity. Then model the numbers at the 731.25 point.

### Route (d) with a row split: model numbers (`route_d_model.py`, `route_d_model.out`)

Split v's rows at `R0 = c (6j)^{1/3}`:
* **Rows `< R0`.** Use the source-set energy on `U = {u_r : r < R0}` with weights capped at `R0`. The
  counted rows only need `z_{u_r} ≥ r + 1`, so the cap is free. Entropy `R0 ln R0`, deviation
  `~ R0² ln R0 ≪ j`.
* **Rows `≥ R0`.** These need a round-1 column taller than `R0`. There are at most
  `s_{R0} ≲ 9 j/R0²` (profile bound), and each serves about one of v's rows.

At `J = 1.66e6` (the 731.25 point), least f for one round-2 column:

| j | n = 2^20 | n = 2^40 |
|---|---:|---:|
| J | 369 | 360 |
| 10 J | 821 | 717 |
| 40 J | 1471 | 1076 |
| 100 J | 2231 | 1367 |
| 300 J (≈ jmax at 2^20) | **3711** | 1743 |
| 800 J | (beyond jmax) | 1959 |

Round-1 energy on the source sets is `Q/j ≈ 4–6` sparse (true value ≈ 3) and up to ≈ 13 near jmax at
`n = 2^20`.
* **Inside the ceiling 4023 everywhere checked.** The binding case is `n = 2^20` near jmax, where the
  background `b = j/n ≈ 475` is large.
* For larger n, `b ≤ δ_F f = 500` stays bounded, the allowance `j/J` grows faster than the load, and
  the worst case stays near 2000.

**Status: model only.** The 40–60× loss of the earlier route is gone. Still open:
1. a rigorous round-1 lemma on fixed sets with capped weights (main term `Σ a²/(2(λ−ρ))`, the
   collision/background term, Bernstein over the union of capped profiles);
2. the high-row count, via a union over tall sets;
3. multi-column escapes (sets `S`, `|U| = R0 s2`);
4. certification and Lean.

### Route (d), multi-level and centred: the 731.25 fringe passes in the model

Two refinements (`route_d_model.py`, `route_d_model.out`):
* **Centring.** With weights `a = (z − b)₊`, `b = j/n`, and drift `λ = ρ + λ'` (`ρ = Σ_U a / n`), the
  duality's `ρ j` term equals `b Σ a` and cancels the background part of `Σ_U a z`. So
  `Σ_U (z − b)₊² ≲ 2 j + dev`, the same as the sparse case.
* **Geometric row levels** `[R_i, R_{i+1})`. Each level uses the source-set energy with weights
  capped at `R_{i+1}` (entropy `(R_{i+1} − R_i) s2 ln R_{i+1}`). Every counted row costs
  `≥ (R_i + 1)²`.

Escapes at `f = 3900`, `J = 1.66e6`, `δ_F = 1/8`, against the allowance `j/J`, worst over round-2 set
sizes `s2 ≤ 4096`:

| n | jmax | result |
|---|---|---|
| 2^20 | 308 J | all OK (0 escapes up to jmax) |
| 2^26 | 19708 J | all OK; worst 4450 vs 19000 at 19000 J |
| 2^34 | 5.0e6 J | all OK up to 1e6 J; worst 182229 vs 1e6 |

**So route (d) clears the 731.25 class-A fringe window (`f + 1 ≤ 4024`, `J ≈ 1.66e6`) in the model
with margin.** It is the first fringe route to do so.

**Program for a kernel-checked 731.25:**
1. Paper proof of the round-1 lemma on a fixed source set: capped and centred weights,
   deterministic main term, collision/background drift, Bernstein deviation over the union of
   profiles. Then the multi-level composition and the escapes bound.
2. Interval certificate (as `cert_walk.py`), plus a review.
3. Lean, reusing `FringeDualityDet/Tail/Prob`:
   * weighted per-column tails (jumps `≤ R`);
   * the source-set structure from `σ₂`;
   * the multi-level composition.
4. A generic fringe interface in the padded separator (a `ColumnF2` contract), and `R1At73125`. The
   bulk `R1Cells25`/`R2Cells25` is already done.
