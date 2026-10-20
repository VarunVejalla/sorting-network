# Fringe by double weak duality (UB-34)

Claude (Opus 5.5), 2026-10-20. **Claim level: model.** Floats only. The probability steps are
rigorous in form (level-crossing tails, NA, Chernoff, unions), but nothing is interval-certified and
nothing is reviewed. Script: `fringe_duality.py` (zero escapes); `dense_check.py` (the dense regime).

## Why

The certified fringe route (`best/notes/two-round/F2ROUND.md`, per-E route in `F2D*`) needs
`f = 7934` at `J = 190000`, `δ_F = 1/8`, which is about `18√J`. In the R1 model this fringe floor
co-binds the row count. A heuristic adversary (`../sub500-screen/SCREEN.md`) needs only
`f ≈ √(0.9J) ≈ 414`. The certified route loses because of its union over input tops
(F2ROUND item 4). This note applies the walk bound's weak-duality idea to the fringe instead.

## The argument

Boolean threshold with `j` ones (the top `j` keys). After the first column sort the input is a
staircase `h` with `Σh = j`. Round 1 gives column heights `z`, round 2 gives `w`. The escapes are
`Σ_v (w_v − f)₊`. The contract is: escapes `< j/J` for every `0 < j ≤ jmax = δ_F f n`, so zero
escapes for `j < J`.

1. **Round 1 (exact identity).** For any set `S` of output columns,
   `Σ_{v∈S} z_v = Σ_c N_c^S(h_c)`, with `N_c^S(h) = #{r < h : σ1_r(c) ∈ S}`. This holds because the
   one-cell `(r, c)` with `r < h_c` lands in column `σ1_r(c)`. For every `λ > 0`,
   `N ≤ λh + Y_c^S(λ)` with `Y_c^S(λ) = max_h (N_c^S(h) − λh)`. Summing over `c`:
   `Σ_{v∈S} z_v ≤ λj + Y^S(λ)`.
2. **Round-1 probability.** The `Y_c^S` are monotone in disjoint sets of negatively associated
   indicators (ROUND2.md §4), so `E e^{tY^S} ≤ Π_c E e^{tY_c^S}`. The per-column tails come from level
   crossing: `P(Y > y) ≤ Σ_k P(Bin(t_k(y), p) ≥ k)`, with `t_k(y)` the last time level `k` still beats
   the drift. A Chernoff bound plus a union over the `binom(n, s)` sets of each size gives
   `Y^S(λ) ≤ x_s(λ)` for all `S` at once.
3. **Profile of `z`.** `s_k = #{u : z_u ≥ k}` satisfies `k·s_k ≤ λj + x_{s_k}(λ)` for **every**
   `λ`. This bounds `Q(j) = Σ_u z_u² = Σ_k (2k − 1) s_k`.
4. **Round 2 (exact identity with a convex cost).** `Σ_{v∈S′} w_v = Σ_u N′_u(z_u) ≤ μQ(j) + Y′^{S′}(μ)`,
   with `Y′ = Σ_u max_h (N′_u(h) − μh²)`. This is a walk with quadratic drift, bounded the same way.
5. **Escapes.** `Σ_v (w_v − f)₊ = max_{S′} Σ_{v∈S′}(w_v − f)`. So the escapes are at most
   `max_s [min_μ (μQ(j) + x′_s(μ)) − f s]`.

The quadratic cost in round 2 is the source of the gain. Round 1 can make only a few tall columns
(`Q ≈ 70–95·j` here, not `j²`), so round 2's adversary pays a cubic price.

## Numbers (n = 2^20, failure 1e-4, `duality_n2e20.out`)

| j | Q / j | zero escapes for f ≥ | (6j)^{1/3} | √(0.9 j) |
|---:|---:|---:|---:|---:|
| 1 000 | 71 | 198 | 18 | 30 |
| 10 000 | 82 | 388 | 39 | 95 |
| 100 000 | 92 | 775 | 84 | 300 |
| **190 000** | 95 | **950** | 104 | 414 |

The certified route needs f = 7934 at J = 190000. **This route needs about 950–1140 at j = J,
7–8× smaller.**

**The dense regime is not yet closed** (`dense2.out`, centred round-2 cost
`φ(h) = λh + μ(h − b)₊²`). The contract also needs escapes `< j/J` for `J < j ≤ jmax = δ f n`. With
the present constants the least f grows with j: 1139 at `j = J`, 1980 at `j = 5J`, still binding on a
single column. The run was stopped for low memory before `30J … jmax`.
* The heuristic adversary needs only `(6j)^{1/3} + j/n` there (≈ 180 at 5J).
* The loss is in round 1's tall-column profile: `Q/j ≈ 160–190`, from the union over output sets
  (`s ln(n/s)` per set).

So the route is promising but its constants are not yet good enough to claim a fringe below 7934
across the whole range. The open step is a sharper round-1 profile bound.

## What it would buy (R1 model, `../sub500-screen/refined.out`)

| package | cost |
|---|---:|
| fringe f/7.9, nothing else | **731.25** ((4,5,3), rows < 2^25) |
| f/7.9 + band repair | 642.5 |
| f/7.9 + band + merge | 595.5 |
| f/7.9 + band + merge + R2 κ=1/2 + T=2 | 495 |

The first row is the step the 2026-10-19 parameter search found blocked. That search reported
"731.25 needs f ≈ 4022 at J ≥ 235k", and the (4.2) sibling term binds as well. A smaller fringe
allows a larger `J`, hence a smaller `δ`, a smaller sibling term, and room for `ε_B`. The model's
731.25 point uses `ε_F ≈ 6e-7` (`J ≈ 1.7e6`).

## Next steps

1. A sharper round-1 profile (s_k) bound, then finish the dense regime up to `jmax`; then `J ≈ 1.7e6`
   (the 731.25 point's fringe).
2. Tighten the constants: rigorous Binomial tails instead of Chernoff; the union over `S` only
   where it is needed.
3. Make it a certificate: interval arithmetic in the style of `cert_walk.py`, plus a review.
4. Lean:
   * the two exact identities and the convex-cost duality (deterministic);
   * the level-crossing tail;
   * NA and Ville-type steps (`NegAssoc`, `Ville` exist in `best/AKS/Sub800`).

   It plugs into `FringeCert`/`nodeSpec_padded` through a new fringe predicate in place of
   `SRd/R1d/R2nd`.
5. A new point `R1At73125` (q = 25) with the generic R1 layer: new bulk cells on `[2^24.5, 2^25]`
   and new fringe classes.
