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

### Sweep status (2026-10-21; `rd_sweep/`, `rd_alln/`; better of Kingman and collision at each level)

Each sweep covers every j in `[1, jmax]` by intervals of ratio 1.15, and every set size (exact points until
the average load is below f, then monotone 1.05-intervals). Parameters: f = 4000, J = 1.66e6,
`δ_F = 1/8`, η = 1e-4.

**Range of n.** n runs over the powers of two from `2^18` up: bags below the 731.25 point's Batcher
threshold `2^43` are sorted directly, and `m ≤ 2^25`.

| n | status |
|---|---|
| `2^18, 2^19, 2^21 – 2^25`, `2^20`, `2^26` | **complete through jmax, 0 FAIL** |
| `2^34` | 0 FAIL through `2.8e6 J` (jmax `5.2e6 J`); margins about 2.6× |
| `2^27 – 2^33`, `2^35 – 2^40` | 0 FAIL so far, up to `4e4 – 1e5 J`; margins about 3× |

Below `2^18` (`rd_alln/below_batcher/`) there are genuine FAILs at `n = 16, 64`. Those n are never used.

**Remaining before a claim:**
1. Finish the sweeps.
2. An n → ∞ argument for both regimes:
   * sparse: the collision branch is monotone in n;
   * dense, `j ∝ n`: the allowance is about n, the trivial bound for small sets is `s·sqrt(2j)`, and for
     large sets the centred Kingman entropy is about `s ln(n/s)`.
3. Interval arithmetic in place of floats.
4. Review.
5. Lean.

## Route (d) for n → ∞: the dense regime and a cube-root structure (2026-10-22)

The sweep range grows with n (`jmax = f n/8`, so the density `b = j/n ≤ f/8`). Measurements at fixed b
(`rd_dense/`, and `load_bound` at `s = 1`):

| b | n | `L_b(1) − f` | allowance j/J | ratio |
|---|---|---:|---:|---:|
| 10 | 2^30 | 1777 | 2.15e4 | 0.083 (worst over all s: 0.095, at `s = 1`) |
| 10 | 2^40 | 52880 | 2.2e7 | 2.4e-3 |
| 10 | 2^50 | 5.56e5 | 2.25e10 | 2.5e-5 |
| 10 | 2^60 | 5.50e6 | 2.31e13 | 2.4e-7 |
| 100 | 2^30 … 2^60 | 8.4e3 … 1.2e7 | 2.2e5 … 2.3e14 | 0.039 … 5e-8 |

The single-column bound grows like `j^{1/3}` (×97 per ×2^20 in n, against ×101 for `j^{1/3}`). The allowance
grows like j. In this regime `Kmax` is the trivial `sqrt(2j)` (`A*` excludes nothing), so the per-level
bounds do the work.

**Why `j^{1/3}` is the truth.**
* A round-1 output column of height k costs the adversary about `k²/2` input mass (fact 3).
* A round-2 column v gains load at row r only if its row-r source column has height `> r`.
* So load L costs about `Σ_{r<L} r²/2 = L³/6`: `L(1) ≲ (6j)^{1/3}`.
* For s columns with disjoint sources, `L(s) ≈ s^{2/3}(6j)^{1/3}`. Then `escapes(s) = L(s) − f s` peaks at
  `s ≈ (8/27)(6j)/f³`, with value about `(4/27)(6j)/f² ≈ 5.6e-8·j`, against the allowance `j/J = 2e-6·j`.
  That is a ratio of about 0.03, **independent of n**.

**n-uniform lemma to prove (replaces the per-n sweeps for `n ≥ n₀`).** With probability `≥ 1 − η` over
`(σ₁, σ₂)`, for every input of mass j and every set S of s round-2 columns:

    L(S) ≤ s·L₀ + C·s^{2/3} (j + n)^{1/3} · polylog-free constant,

with C explicit.

**Route.**
1. **Round 1:** the level count `N(h) = #{round-1 columns with z > h}` satisfies `Σ_h h·N(h) ≲ C₁ j`. This is
   the energy `E = Σ z² ≤ C₁ j + C₂ j²/n` that route (d) already bounds by levels. In the dense regime the
   `j²/n` term is `b·j`.
2. **Round 2, deterministic plus a σ₂-only union:** v's load at levels `≥ L₀` is
   `Σ_r 1[z_{src_r(v)} > r]`. It is at most `Σ_r 1[src_r(v) ∈ T_r]`, where `T_r` is the set of the `N(r)`
   tallest round-1 columns. A union over the level profile `(N(r))_r` would be too large, because profiles
   number `e^{Θ(√j)}`.
3. **Bucketing:** `N(r) ≤ C₁ j/r²` from step 1 (Markov on the energy) bounds the profile pointwise. Hence
   `P_r := N(r)/n ≤ C₁ b/r²`. The load at rows `≥ L₀` is then dominated by a Poisson-binomial with mean
   `Σ_{r≥L₀} C₁ b/r² ≈ C₁ b/L₀`.
   * For a **fixed** family of sets `T_r`: union over v (n) and over the `T_r` choices. Only the nested
     sets of the top `C₁ j/r²` columns matter, determined by round 1's outcome, and σ₂ is independent of
     σ₁. Conditionally on round 1, `T_r` is fixed, so **no union over profiles** is needed beyond a union
     over inputs' induced `T_r`.
   * That last union is the remaining difficulty. It is the same entropy as route (d)'s union over U.

So the n → ∞ argument is the energy bound `Σ_h h N(h) ≤ C₁ j` (n-uniform: the collision lemma) plus a
σ₂-side union over nested tall-column sets. The sweeps show the evaluator already exhibits the cube-root
behaviour.

**Status:** plan with measurements. The proof is open.

### Scaled evaluator (`rd_scaled.py`, work in progress): low and mid levels fine, high levels need a new lemma

At fixed `(b, σ) = (j/n, s₂/n)`, every term of `escapes` is n times an n-free quantity plus `O(ln n)` pieces:
* `lbinom(n, σn) ≤ n σ ln(e/σ)`;
* `n lnG(αn) = −n ln(1 − q)`, with q n-free;
* `Bin(H, σ)` multiplicities;
* `kmax_sources(αn, d, σn) = n·(σw + …)`.

`rd_scaled.py` evaluates these per unit n, with a slack ε for the `ln n/n` parts. Its per-level counts
are small: at `b = 10`, `σ = 1e-6`, levels near offset 1e4 give about `3e-6` per n each.

**Obstacle: the high levels.**
* The finite evaluator caps the levels at `top = b + Kmax + 1`, and in this regime Kmax is the trivial
  `sqrt(2j) ∝ √n`.
* Each level's multiplicity term pays its own union over S, about `σ ln(e/σ)/t` per n.
* With geometric levels up to √n, the sum grows like `ln n`. **So the per-level structure is not n-uniform
  as it stands.**

The ad hoc tail term in `rd_scaled.py` (A* at a single top level, divided by d) is **not valid**: it
ignores multiplicity. It is left in only as a placeholder and gives FAILs.

**Needed: a high-level lemma.** For a set S (`|S| = σn`), rows at offsets `≥ D` above b total

    Σ_{v∈S} #{r ≥ D : z_{src_r(v)} > r} = Σ_T M_T,   M_T = #{r ∈ [D, z_T) : σ₂,r(T) ∈ S}.

* Conditionally on round 1, `M_T ~ Bin(z_T − D, σ)`, negatively associated across T. Rows are independent,
  and within a row the events form a hypergeometric family.
* The mean is `σ Σ_T (z_T − D)₊ ≤ σ·E_{≥D}/(D − b)`, where `E_{≥D} = Σ_{z−b ≥ D}(z − b)²` is the round-1
  energy above level D. That is route (d)'s `A*` with `U = [n]`, `u = n`, an n-uniform per-n quantity.
* A **single** union over S, with no per-level unions, and one over the tall-column profile (at most
  `E_{≥D}/D²` columns per n) then bounds all levels above D at once.

The open question is whether the profile union, about `(E_{≥D}/D²)·ln(D²/E_{≥D})` per n, is paid for by
the Chernoff margin. A large D makes it small, since `E_{≥D}/D²` falls.

**Status:** the plan is sharpened. The evaluator is incomplete above a level D, which needs the lemma
above.

### Scaled evaluator with the single-union high-rows lemma (`rd_scaled.py`, `rd_scaled_out/`)

**High-rows lemma** (`high_rows_s`). Rows at offsets `≥ D` above b, for any S with `|S| = σn`, total
`Σ_T M_T`. Conditionally on round 1, `M_T ~ Bin((z_T − b − D)₊, σ)`, NA. So

    Rows_{≥D}(S)/n ≤ min_t [σ(e^t − 1)·w_D + σ ln(e/σ) + pe_D + ε]/t,

with one union over S, and:
* `w_D = Σ_i α_i/d_i`, the round-1 level energies with `U = [n]` (A*, `u = n`);
* `pe_D = N(ln(e/N) + ln(e(w/N + 1)))` the profile union, `N = Σ α_i/d_i²`.

**Level tail** (`round1_level_tail`). For `d ≥ 10⁶`, every α in `[ahat, R b]` is excluded (mass bound
`Σ(z−b)² ≤ R j`), with `t = s/R`, `s = 1/(2b)`, `q ≤ 1/2`. The relative inequality is monotone in d. Measured
`ahat/b` is 2.03 – 2.44 for `d₀ = 10⁶ … 10²⁰`.

**Grid** (old tail constant; to rerun with the verified tail). Escapes per n against the allowance `b/J`:

| b | σ = 1e-12 … 1e-9 | σ = 1e-8 … 1e-3 |
|---|---|---|
| 1 | 1.2e-7 … 4.8e-7, all `< 2e-6` | negative |
| 10 | 1.3e-7 … 3.9e-6, all `< 2e-5` | negative |
| 100 | ≤ 1.1e-5 at 1e-9 and 2.8e-5 at 1e-8, all `< 2e-4` | negative from 1e-7 |
| 496 | ≤ 1.6e-4 up to 1e-7, all `< 9.9e-4` | negative from 1e-6 |

`σ ≥ 1e-3` follows from the monotone average: at `σ = 1e-3`, `L/σ = f + escapes/σ ≈ 887 < f`. The raw
`σ = 1e-2` FAIL rows are moot.

**Regimes for the full n → ∞ argument.**
* **(B) dense, `j ≥ C·J·ln n`.** The absolute `O(ln n)` union pieces (ε) are small against `j/J`. The scaled
  evaluator applies, pending:
  * the cell-monotone `(b, σ)` cover;
  * the rerun with the verified tail;
  * the σ → 0 limit, where the per-n terms are bounded by `(pe + ε)/t`, which is ∝ b.
* **(A) sparse, `j ≤ C·J·ln n`, so `b → 0`.** The `ln n` union terms rival the allowance. Only the collision
  branch survives, since it divides `ln n` by `s ≈ ln(1/q) ≈ ln n`. Needed:
  1. the collision-only evaluator is nonincreasing in n for `n ≥ n₀`, term by term;
  2. its n = ∞ limit, a single-column load of about `290 (j/J)^{1/3}` (extrapolating the 2^160 table);
  3. a j-scaling argument at n = ∞ for `j → ∞`, the b = 0 analogue of this scaled evaluator.

**Status:** (B) is numerically in hand at grid points with large slack. (A) is structured but not built.

**Regime (B) as b → 0** (`n0_of_b`). In (B), `j = bn ≥ C·J·ln n` (C = 800) forces
`n ≥ n₀(b) = (CJ/b)·ln(CJ/b)`. So the absolute ln-terms satisfy `ε(n) ≤ c_ln ln n₀/n₀ ≈ 0.1·b/J`.

| b | σ/b = 1e-9 | 1e-6 | 1e-3 | allowance b/J |
|---|---:|---:|---:|---:|
| 1e-2 | −7.4e-9 | −3.6e-5 | −3.9e-2 | 2e-8 |
| 1e-4 | −8.1e-11 | −3.6e-7 | −3.9e-4 | 2e-10 |
| 1e-6 | −8.3e-13 | −3.6e-9 | −3.9e-6 | 2e-12 |

The escapes are negative throughout and scale linearly in b, so (B) is uniform as b → 0.

**Regime (A), `j ≤ C·J·ln n`.** For each j, (A) needs every `n ≥ n_A(j) = max(2^40, e^{j/(CJ)})`.
* For `j ≤ CJ·ln 2^40 ≈ 1.1e10`, that is `n ≥ 2^40`.
* Above that, n is super-exponential in j.

Plan:
1. **Collision-type terms**, `min_s R[n·F(s, c/n) + E₀ + s₂ ln n]/s`: take `s(n) = s₀ + ½ ln(n/n₀)`. Then
   `n(q e^s)²` is constant and `n ln(1 + a/n) ≤ a`, so the term is at most a Möbius function of `ln(n/n₀)`.
   Its sup over `n ≥ n₀` is the max of its value at n₀ and its limit `2R s₂`.
2. **Kingman-type terms** (`ln n` entropy over `t ≈ κ/R`) are not n-uniform. In (A), replace them by
   collision-type terms, or use them only below n₁.
3. A j-grid sweep up to `j ≈ 1.1e10` with the sup-over-`n ≥ 2^40` evaluator.
4. For larger j (`n ≥ e^{j/CJ}`), the n = ∞ collision evaluator, with a scaling argument in j.

### Regime (A) via the merged collision evaluator (`rd_sparse.py`: `escapes_merged`, `worst_merged`)

**Structure** (for every n ≥ n₀ at once, with `ln n₀` a parameter):
* rows below offset D are counted in full (`s₂·(⌈b₀⌉ + D)`);
* above D, levels `[d_i, R_i)` with source counts `k_i ≤ A_i/d_i²`. Here `A_i` is the collision bound's sup
  over n (`s(n) = s* + ½ ln(n/n₀)`); the Möbius map's sup is `max(value at n₀, 2R L_c)`, and the per-level
  union is summable;
* **one** multiplicity union over all rows `[D, top)`, using `Σ_i(x_i − c)₊ ≤ (Σ_i x_i − c)₊`. With
  `t(n) = t* + ln(n/n₀)` its sup is `max(value at n₀, L_c)`;
* `top = b₀ + sqrt(2j) + 2`, since a round-1 column has `z(z+1)/2 ≤ j`.

So the count is `≤ c Σ_i A_i/d_i² + mult_tot`, with `Σ_i A_i/d_i² ≈ 2j/(0.61 D²)`. This is below `j/J` once
`D ≳ 1800`, and is uniform in j.

**Regime boundary moved to C = 100.** (B) still passes there, including tiny σ. So (A) is `j ≤ 100·J·ln n`,
i.e. n₀(j) = `max(2^40, e^{j/(100J)})`.

| j | worst escapes (all n ≥ n₀) | allowance | worst at |
|---|---:|---:|---|
| 300J | −2522 | 300 | s₂ = 1 |
| 1000J | −1655 | 1000 | s₂ = 1 |
| 2770J | −844 | 2770 | s₂ = 1 |
| 3000J | −750 | 2609 | s₂ = 1 |
| 1e4 J | 222 | 8696 | s₂ = 1 |
| 1e5 J | 6843 | 8.7e4 | s₂ ≤ 5 |

Pointwise checks at s₂ ∈ {1, 10, 1000} out to `j = 1e20·J` give escapes about `1e-7·j`, against the
allowance `j/J = 2e-6·j`.

**Still to do for route (d)'s n → ∞:**
* j-interval cells (monotone conventions) for (A), and `(b, σ)` cells for (B);
* a j → ∞ statement for (A): the bound is `≈ 2cj/(0.61D²) + O(√j·s₂)`, linear in j with coefficient
  `< 1/J`;
* the finite range `n < 2^40`: the existing sweeps, or (A) with a smaller n₀;
* interval certification;
* review.

### Coverage map for route (d) at every n ≥ 2^13 (2026-10-22, floats, unreviewed)

| range | method | status |
|---|---|---|
| `2^13 ≤ n ≤ 2^30`, all `j ≤ f n/8` | per-n sweeps (`rd_pkg/`, Kingman plus collision) | 2^13 – 2^17, 2^20, 2^26 complete, 0 FAIL; 2^30 nearly complete; **2^18, 2^19, 2^21 – 2^25, 2^27 – 2^29 not run**; non-power-of-two n not addressed |
| `n ≥ 2^30`, `j ≥ 100·J·ln n` (B) | scaled evaluator, floor `n_min = 2^30` (`rd_scaled_out/floor30_B.out`) | passes at the grid points b ∈ {1, 10, 100, 496}, σ/b = 1e-12 … 1e-3; σ beyond that covered by the monotone average |
| `n ≥ 2^30`, `j ≤ 100·J·ln n` (A) | merged collision evaluator, `n₀ = max(2^30, e^{j/(100J)})` | passes at j = J, 100J (floor 2^30); 300J – 1e6 J (floor 2^40) |
| (A), `j ≥ 1e6·J` | analytic (below) | done in sketch |

**(A) for `j ≥ 1e6·J`.** Then `ln n₀ = j/(CJ) ≥ 1e4`.
1. Choosing `s = ½ ln n₀ − ln(eRu/λ)` gives `g₀ ≤ 1` and
   `v₀ ≤ 2RL_c(1 + δ)`, `δ ≤ (5 ln j + E₀/L_c)/(j/CJ) ≈ 0.014`.
2. The multiplicity sup is at most `L_c(1 + o(1))`.
3. With `λ = 1`, `r = 2`, `D = 3000`:

       escapes ≤ s₂(1 + D) + 2.67 j/D² + 16(s₂+1)(1+δ)/D + (s₂+1) − f s₂ ≤ −965 s₂ + 3.0e-7·j + 1.01
               < j/J = 2e-6·j        for every s₂ ≥ 1.

**Remaining for route (d):**
1. The per-n sweeps at the missing powers of two up to 2^30, plus an argument for n between powers of two.
2. Cell covers: j-intervals for (A), `(b, σ)` boxes for (B). Pointwise grids are not proofs.
3. (A) between 2^30 and 2^40 at j up to `100·J·ln n` (the 1000J and 2080J points were still running).
4. Interval arithmetic throughout.
5. Review.

**Two coverage gaps found (2026-10-22), from R1's geometry (`R1-PROOF.md` §4).**
1. **n is arbitrary.** `n = ⌊π/(2(f+1))⌋`, and `m = ⌈a/n⌉ − 1` must stay in the row window, so n cannot be
   rounded to a power of two.
   * (A) and (B) are sups over all real `n ≥ n₀`, so they are fine.
   * The per-n sweeps (n < 2^30) need an n-interval version. Every term is monotone in n: use `n_lo` for
     `n lnG`, the collision q and the multiplicity tails; `n_hi` for the entropies;
     `b ∈ [j_lo/n_hi, j_hi/n_lo]` with the existing j-interval conventions.
2. **The fringe class f varies**, from 3967 (mid) up to about 1e7 (sparse botDesc), and each class needs
   `j ≤ f n/8`.
   * Escapes decrease in f (the `−f s₂` term), so for `j ∈ [j_a, j_b]` the worst class is
     `f = max(3967, 8 j_a/n)`.
   * The sweeps must run to `j = f_max n/8` with that f (`--fladder`).
   * (B) needs b up to `f_max/8 ≈ 1.25e6`, at `f = 8b`.
   * (A) is independent of f (worst at f = 3967).

**(B) across the fringe-class ladder** (`rd_scaled_out/fladder_B*.out`, f = 8b, floor 2^30). The evaluator
needed four fixes, each of which only tightens a valid bound:
* tall-column count `N ≤ 1` per n;
* the level-tail cutoff scales with b;
* adaptive s in the tail check (each α-interval uses the largest s with `q ≤ 1/2`);
* **mass cap `α ≤ R·b` per n** (`Σ_level (z−b)² ≤ R Σ (z−b)₊ ≤ R j`). This is what makes large b work.

| b (f = 8b) | worst esc/n over σ/b ∈ {1e-12 … 1e-4} | average load L/σ | f |
|---|---|---:|---:|
| 1e3 | 2.4e-5 (allowance 2e-3) | ≤ 3.2e4 at σ = 1e-9, 1510 at 1e-3 | 8000 |
| 1e4 | negative | 1.3e4 – 5e4 | 8e4 |
| 1e5 | negative | 1.0e5 – 1.3e5 | 8e5 |
| 1.25e6 | negative | 1.26e6 – 1.37e6 | 1e7 |
