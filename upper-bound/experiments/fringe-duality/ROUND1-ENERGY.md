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

## Route (d): proof plan for the fixed-set round-1 lemma

**Setting.** `U ⊆ [n]` is fixed (it depends on `σ₂` only, so it is independent of `σ₁`), `|U| = u`.
Weights are capped at `R`, and `b ≥ 0`.

**Lemma (fixed-set centred energy).** With probability `≥ 1 − η` over `σ₁`, for every input of mass
`j` and every `a ∈ {0, …, R}^U`, with `ρ = Σ_U a_T / n`:

    Σ_{T∈U} a_T (z_T − b) ≤ λ' j + Σ_c Y_c,    Y_c = max_h Σ_{r<h} (a(σ₁,r(c)) − ρ − λ'),

where `b = j/n` exactly. The `ρ j` part of `λ j` cancels `b Σ a`. Then `Σ_c Y_c ≤ x(a)` on that event.
Taking `a_T = min(R, (z_T − b)₊)` gives `Σ_U min(R,(z−b)₊)² ≤ λ' j + x(a)`.

**Proof steps.**
1. **Deterministic.** This is `weighted_duality` (Lean, `FringeDualityDet`) with `λ = ρ + λ'`, plus
   mass conservation.
2. **Per-column tail, two bounds, take the minimum.**
   * Ville: let `θ*(a)` solve `e^{−θ(ρ+λ')} (1 + (1/n) Σ_U (e^{θ a_T} − 1)) = 1`. The increments are
     iid over rows, since column `c` lands on a uniform target in each independent row. So
     `P(Y_c ≥ y) ≤ e^{−θ* y}`.
   * Level crossing: `Y_c > y` needs either one hit `(r, T)` with `a_T − (ρ+λ')(r+1) + (background) > y`,
     or two or more hits in the first `H(y)` rows. In the sparse regime this gives
     `P(Y_c > y) ≲ (1/n) Σ_T (a_T − y)₊ / λ' + P_2(y)`.
3. **Moment.** `E e^{tY_c}` by the discrete layer cake (Lean: `sum_exp_le_layer`) on the minimum of
   the two tails.
4. **Across columns.** NA, as in `fixed_mgf_cost` (Lean, `FringeDualityProb`): the per-row target
   vector is a permutation of a fixed vector; weights `≥ 0`.
5. **Union.** Over profiles: at most `(R+1)^u` of them, organized by statistics. The profile enters
   only through `Σ_U (e^{θ a} − 1 − θ a)`, which is at most `(Σ a²/R²)(e^{θR} − 1 − θR)` by convexity
   with the cap. Plus a union over `U` (`n` targets `v`, or round-2 sets `S`) and over the `λ'` grid.

**Composition** (multi-level, per round-2 set `S`; deterministic, partly in Lean):
* levels `[R_i, R_{i+1})`;
* counted rows at level `i` cost `≥ (R_i + 1 − b)²` each in the centred energy;
* escapes are bounded through `escapes_le` and `sum_posPart_le_of_sets`.

Next: a rigorous numeric screen of this lemma (Ville + level crossing with weighted jumps), replacing
the Bernstein model in `route_d_model.py`; then interval certification.

## Route (d): the Kingman MGF lemma (rigorous in form; `route_d_rigorous.py`)

This replaces the Bernstein/collision model. There is no collision term and no `P(Y_c > 0)` loss.

**Per-column MGF.** Let `X` be iid with `E X = −λ < 0`, and `M = sup_{h≥0} S_h ≥ Y_c` (infinite horizon).
1. `M =_d max(0, X + M')`, and `e^{t max(0,y)} = e^{ty} + (1 − e^{−t y₋})`. Hence
   `G(1 − φ(t)) = E[1 − e^{−t (X+M')₋}]`.
2. This is `≤ 1 − e^{−t E(X+M')₋}` by concavity, and `E(X+M')₋ = −E X = λ` by stationarity.
3. So `E e^{tY_c} ≤ (1 − e^{−tλ}) / (1 − φ(t))` whenever `φ(t) < 1`.

To first order this is Kingman's bound, `E Y_c ≤ Var X / (2λ)`.

**Our walk.** The increments are `X = a_{σ₁,r(c)} − ρ − λ`, with `ρ = Σ_U a/n` and `a ∈ {0..R}^U`.
* By convexity of `g(s)/s²` (`g(s) = e^s − 1 − s`) and `e^{−y}(1 + y) ≤ 1`:
  `φ(t) ≤ e^{−tλ}(1 + A g(tR)/(n R²))`, with `A = Σ a²`.
* Hence `n ln G ≤ −n ln(1 − A g(tR) / (n R² (e^{tλ} − 1)))`. For small `tR` this is `≈ t A/(2λ)`, so
  it is **independent of n** apart from the union.
* NA (per-row permutations of a fixed vector, independent rows; `Y_c` nondecreasing on disjoint
  coordinates) and Chernoff give `Σ_c Y_c ≤ x(A) = min_t [n ln G + Ent]/t` for all `a` at once, with
  `Ent = u ln(R+1) + ln(#U choices / η)`.
* The event does not depend on `j`.

**Deterministic step.** With `b = j/n`, `Σ_U a(z − b) ≤ λ j + Σ_c Y_c`, since the `ρ j` term equals
`b Σ a`. Take `a_T = min(R, ⌊(z_T − b)₊⌋)`. Then `A ≤ λ j + x(A)`, which excludes every `A` above a
threshold `A*`. Per `A`, choose `λ` and `t` freely; the script verifies the exclusion on intervals.

**Round 2** (per set `S` of `s2` round-2 columns; `σ₂` only). Split v's rows into free rows
`< L0` (with `L0 ≥ ⌈b⌉`) and geometric levels `[lo, hi)` up to `top = b + Kmax + 1`. Here `Kmax` is
the single-column (`u = 1`) bound, so no round-1 column exceeds it. Then:
* `count_i ≤ A*_i / ⌊lo + 1 − b⌋² + Σ_u (M_u − 1)₊`, where `M_u = #{r ∈ [lo,hi) : σ₂,r(u) ∈ S}`.
  The second term is a multiplicity excess with `M_u ~ Bin`, NA across `u`, Chernoff plus a union
  over `S`.
* `escapes(S) ≤ s2·L0 + Σ_i min(s2 (hi − lo), count_i) − f·s2`.

Two refinements were needed for large `u = (hi − lo)·s2`:
* **Per-level weights.** Use `a_T = min(R, ⌊z_T − b⌋)·1{z_T − b ≥ d}`, with `d = ⌊lo + 1 − b⌋`. Still
  `a(z − b) ≥ a²`, and the support is at most `A/d²`. The union is then over
  `≤ (k+1) binom(u, k) (R − d + 1)^k` vectors (`k = A/d²`), applied per `A`-interval, instead of
  `(R+1)^u`. Without this, `Ent = u ln R > 2nλ` and nothing is excluded.
* **Multiplicity, top-k.** Only the `k` active sources count, so
  `count_i ≤ min_c [k c + max_S Σ_u (M_u − c)₊]`. The `c = 1` version summed the excess over all `n`
  sources (≈ 1e11 at the top levels).
* The `s2` grid runs over powers of 4 up to `j/f`; at most `j/f` columns can be overloaded.
  Intermediate `s2` is not checked yet (a certification item).

Lean gap: `NegAssoc` covers images of one set (`powersetCard`). The weighted walk needs NA for a
random permutation of a fixed vector, via a chain of nested level sets or the general theorem.

### Coverage of all set sizes and all j (2026-10-21)

* **Set sizes.** Every count term is nondecreasing in `|S|`:
  * larger `U`;
  * entropy `lbinom(n, s)` for `s ≤ n/2` (here `s ≤ j/f ≤ n/8`);
  * `kmax_sources`;
  * `Bin(H, s/n)`.

  The term `−(f − L0)|S|` is decreasing. So `escapes(sb, …, s2_lo = sa)` bounds every `|S| ∈ [sa, sb]`.
  `route_d_rigorous.py` now checks `s2 = 1` and every interval `[2^i, 2^{i+1}]` up to `j/f`. At most `j/f`
  columns can be overloaded. Runs: `rd_iv/`.
* **All j (design; not run yet).** For `j ∈ [j_a, j_b]`, use:
  * `λ j_b` in `A*`;
  * the cap `R = ⌈hi − b_a⌉`;
  * the level floor `d = ⌊lo + 1 − b_b⌋` (with the indicator `1{z − b ≥ d}`);
  * free rows `L0 = ⌈b_b⌉ + x`;
  * `Kmax` at `j_b`;
  * the allowance `j_a/J`.

  Each term then bounds every j in the interval. A geometric j-grid with ratio about 1.2 up to jmax
  needs a faster evaluator first. The pure-Python `A*` and `mult_excess` loops take hours per large j.
  Port them to vectorised or compiled code, or cache across j.

## Route (d) gap: uniformity in n (2026-10-21)

The construction needs every n: the separator's column count is `n ≈ a/m`, which is unbounded as
`N → ∞`. But route (d) as written is **not n-uniform**.
* The union over target columns and sets costs `ln n` (and `s2 ln(n/s2)`).
* In the Kingman lemma, t is capped near `κ/R`, because the main term grows like `e^κ`.
* So the loss is about `R·Ent/κ`, which grows with `ln n`.

Single-column load from `route_d_rigorous.escapes` (`s2 = 1`, f = 4000):

| n | 2^20 | 2^40 | 2^80 | 2^160 | 2^320 | 2^640 |
|---|---:|---:|---:|---:|---:|---:|
| load at j = J | 392 | 366 | 350 | 349 | 359 | 371 |
| load at j = 100J | 1743 | 1525 | 1504 | 1500 | 1503 | 1514 |

This is harmless for any n that could ever be realised, but it is unbounded, so it does not give the
limsup.

**The truth is n-uniform.** The adversary's power is mass-limited, `Σ_all z² ≈ 3j`, and coincidences of
v's sources become rarer as n grows.

**Fix (n large): deterministic main term plus a collision term**, as in "Sharper round 1" above. Since each
`σ₁,r` is a bijection, `Σ_c Σ_{hits} (a − λ(r+1))₊ = Σ_r Σ_T (a_T − λ(r+1))₊` exactly.
* With at most one relevant hit, `Y_c` equals its single-hit value.
* Otherwise `Δ_c ≤ R·N_c(h*)`, with `N_c(h*) ≥ max(2, λh*/R)`. This needs at least two hits on `U` early, or
  a hit rate above `λ/R`.
* Its tails are about `(C R u/(λn))^k`. So `t ≈ ln(nλ/(CRu))/(2R)` is allowed, giving
  `x_Δ ≈ 2R (c u R + u ln R + ln n)/ln(nλ/(CRu))`. **This is bounded as n → ∞.**
* It is useful only when `ln(n/(uR)) ≳ 20`, i.e. for `n ≳ e^{20} u R`.
* Kingman covers moderate n (the table above, at least up to `2^640`). Use the smaller of the two bounds
  per level.

**Status:** open. It needs this collision lemma written out and evaluated. Until then, route (d)
certifies the 731.25 fringe only for `n ≤ 2^640`, which is not enough for a limsup.

### Collision lemma implemented (`A_coll` in `route_d_rigorous.py`)

Uncentred weights `a_T = min(R, z_T)·1{z_T ≥ d}` on a fixed `U`.
* **Deterministic.** Let `h*` be the argmax of column c's walk. If only one hit on U precedes `h*`, then
  `Y_c ≤ (a − λ(r+1))₊`. Otherwise `Y_c ≤ R·M_c`, where `M_c = max{N(h) : N(h) ≥ 2, N(h) ≥ λh/R}` and
  `N(h)` counts hits on U.
* **Main term.** Each row is a bijection, so `Σ_c Σ_hits (a − λ(r+1))₊ = Σ_r Σ_T (a_T − λ(r+1))₊ ≤ A/(2λ)`.
* **Collision term.** `M_c` depends on U only, so there is **no union over profiles**.
  * `P(M_c ≥ k) ≤ q^k/(1−q)`, with `q = eRu/(λn)`.
  * NA across columns. Chernoff with `s = tR` up to `ln(1/q)`.
* **Result.** `A ≤ (λj + x_Δ)/(1 − 1/(2λ))`, with `x_Δ = R [n ln(1 + (qe^s)²/((1−q)(1−qe^s))) + Ent]/s`.
* **As n → ∞:** `q → 0`, the `n ln`-term tends to 0, and `R·Ent/s → R(1 + s2)`. The bound is
  **n-uniform**.

Single-column load with the better of Kingman and collision at each level (f = 4000):

| n | 2^20 | 2^40 | 2^80 | 2^160 | 2^320 | 2^640 |
|---|---:|---:|---:|---:|---:|---:|
| j = J | 392 | 307 | 294 | 291 | 292 | 297 |
| j = 100J | 1743 | 1355 | 1320 | 1316 | 1316 | 1323 |

The remaining drift (+6 up to 2^640) comes from the Kingman branch inside `Kmax`. The collision branch alone
has a finite limit.

**Remaining for an all-n statement:**
1. Show each collision term is monotone in n beyond some `n₀` (e.g. `2^640`): `Ent/ln(nλ/(eRu))` is
   eventually decreasing towards its limit.
2. Rerun the j × s2 sweeps with this code. The `rd_sweep` runs use the Kingman-only version, which is
   valid but looser.

### All set sizes at once: the average load is monotone

`L(s) = max_{|S|=s} Σ_{v∈S} w_v` is the sum of the s largest loads, so `L(s)/s` is nonincreasing. If the
bound `L_b(s₀) ≥ L(s₀)` has `L_b(s₀)/s₀ < f`, then for every `s ≥ s₀`:

    escapes(s) = L(s) − f s ≤ s (L(s₀)/s₀ − f) < 0.

`worst_interval` therefore evaluates exact `s = 1, 2, …` until the average drops below f (usually at
`s = 1`). Intervals `[s, 2s]` are only a fallback past 64.

The earlier `[2^i, 2^{i+1}]` interval sweep (`rd_sweep_old/`) produced false FAILs: an interval loses a
factor 2 in the linear credit, so it fails whenever the load exceeds about f/2. Those FAILs are superseded.

The j-intervals use ratio 1.15. The sweeps in `rd_sweep/` take the better of Kingman and collision at each
level.
