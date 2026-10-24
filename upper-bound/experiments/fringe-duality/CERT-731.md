# Route (d) fringe certificate at the 731.25 point (UB-43)

Claude (Opus 5.5), 2026-10-24. Runs and drivers: `rd731/`. Evaluators are unchanged
(`route_d_rigorous_nr.py`, `rd_scaled[_iv].py`, `rd_sparse[_iv].py`). Only the drivers are new and
parametrized: `rd731/params731.py`, `sweep731.py`, `coverA731_iv.py`, `coverB731_iv.py`, `bzero731.py`.
`rd731/summarize.py` tabulates every output.

## Parameter point

* Design P, R1 architecture, schedule (4,5,3), separator rows `m ∈ [27254890, 2^25]`, three full column
  sorts.
* **No band repair** in this package, so the REVIEW-v7 band-stage leak term is **not** added.
* Property F (`R1-PROOF.md` §3–4): escapes `< j/J` for `j ≤ jmax = δ_F f n` real keys, with
  `δ_F = 1/8`. Escapes are 0 (bound `< 1`) for `j < J`.
* **`J = 1651190`**, exactly the least admissible J at this point.
* Fringe classes:
  * class A: `f + 1 ∈ (3329, 4024]`, i.e. `f ∈ [3329, 4023]`;
  * class B: `f + 1 ∈ (210012, 258048]`, i.e. `f ∈ [210012, 258047]`.
* Every f in a class is covered. Escapes decrease in f, and the constraint is `j ≤ f n/8`, so a mass j at
  column count `≤ n_hi` is evaluated at `f_eff = max(f_lo, 8 j_lo/n_hi)` of the first class with
  `f_hi ≥ 8 j_lo/n_hi` (`params731.f_eff`). Masses with `8j/n ∈ (4023, 210012]` exist only in class B,
  so they use `f = 210012`.
* **Columns: every real `n ≥ 2^17`.** Large senders have `a > 2^q` with q the Batcher threshold
  (largest q with `q(q+1)/2 ≤` stage depth), and `n ≥ a/(m+1) > 2^q/2^25`:
  * the 731.25 package (stage depth 975) has q = 43, so `n ≥ 2^18`;
  * the floor `2^17` also covers q = 42 (stage depth about 920, the merge-first variant).
* No upper limit on n: every n up to infinity is addressed below.

## Coverage table

Notation: `b = j/n`. The (A)/(B) boundary uses `C = 800`: (B) is `j ≥ 800 J ln n`. With `C = 100`, (B)'s
absolute ln-term slack `ε = 80 ln n₀/n₀` is about 0.85 of the allowance at `b ≈ 3`, and pointwise (B)
fails there (rel 1.02). With `C = 800` the worst pointwise value is about 0.6.

| n | j | method | type | outputs | result |
|---|---|---|---|---|---|
| `[2^17, 2^30)`, by octaves `[2^k, 2^{k+1}]` | all `j ≤ jmax` (both classes), k = 17 … 25 | per-n sweeps: NR = 2, j-ratio 1.15, class-aware f | float | `sweeps/s17 … s25.out` | 0 FAIL except k = 21, 22, 23 (5 intervals, worst 1.096) |
| the k = 21, 22, 23 FAIL intervals | `[900,1300] J`, `[2100,2600] J`, `[3700,5100] J` | fine sweeps: NR = 2^{1/4} (4 sub-octaves), j-ratio 1.05 | float | `sweeps_fine/` | 0 FAIL, worst 0.643. **The FAILs are discretization artifacts.** |
| `[2^26, 2^30)`, k = 26 … 29 | `j ≤ 150·2^{k+1}` (b < 150) | per-n sweeps, NR = 2 | float | `sweeps/s26 … s29.out` | PENDING |
| `≥ 2^25` | `b ∈ [150, f_max/8]` | (B) cells: floor 2^25, C = 10 (so `n₀(b) ≤ 2^25` for every b ≥ 150) | **interval** | `coverB25/` | 57 cells, all CERT-OK |
| `[2^30, 2^40)`, k = 30 … 39 | `j ≤ 800 J ln(2^{k+1})` | per-n sweeps, NR = 2 | float | `sweeps/s30 … s39.out` | PENDING |
| `≥ max(2^30, n₀(b))`, which contains every `j ≥ 800 J ln n` | `b ∈ [1e-6, f_max/8 = 32256]` | (B) cells: floor 2^30, C = 800, b-ratio 1.1, adaptive σ-bisection | **interval** | `coverB/` | 254 cells, all CERT-OK |
| `≥ 2^40` | `j ≤ 2507 J` | (A) cells, floor 2^40 | **interval** | `coverA/` | CERT-OK |
| `≥ e^{j_a/(800J)}`, for `j ≥ 3.1e4 J` | `j ∈ [3.1e4 J, 1e6 J]` | (A) cells, floor 2^40, C = 800 (here `ln n₀ = j_a/(800J) ≥ 38.8`) | **interval** | `coverA/` | CERT-OK (184 cells in all) |
| `j ∈ [2507, 3.1e4] J`, large n | | (A) ladder: floor 2^44 for `[2507, 5798] J`, 2^48 for `[5798, 15420] J`, 2^52 for `[15420, 26970] J`, 2^56 for `[26970, 31020] J` | **interval** | `coverA_ladder/A44 … A56.out` | 22 cells, all CERT-OK |
| `[2^40, 2^56)` below the ladder floor | j from the ladder's lower end to `800 J ln(2^{k+1})`: `[2400 J, ·]` for k = 40 – 43, `[5000 J, ·]` for 44 – 47, `[1.5e4 J, ·]` for 48 – 51, `[2.6e4 J, ·]` for 52 – 55 | per-n sweeps, NR = 2 | float | `sweeps_gap/s40 … s55.out` | worst 0.40 so far; PENDING |
| (A), `j > 1e6 J` | | analytic bound (below) | sketch | | passes, ratio 0.49 |
| (B), `b < 1e-6` | | per-b numerics plus the limit sketch of ROUND1-ENERGY.md | float + sketch | `explore/bzero731.out` | PENDING |

**Superseded.** `coverA/` has 18 CERT-FAIL cells, `j ∈ [2507, 3.1e4] J`, from the single floor 2^40. With
`n₀ = 2^40`, the collision ratio `q₀ = eRu/(λ n₀)` reaches 1 at about 12 columns, so the load bound becomes
trivial and the monotone-average closure never happens (worst at `s₂` in the millions). These are real
evaluator limits at that floor, not discretization. They are replaced by the ladder rows and the gap
sweeps above.

**Why each region is closed.**
* (B) at floor `2^F` with constant C covers every `n ≥ max(2^F, n₀(b))`, `n₀(b) = (CJ/b) ln(CJ/b)`.
  * `j ≥ CJ ln n` implies `n ≥ n₀(b)`.
  * ε is evaluated at the smaller `n₀`, which is conservative.
* The sweeps stop at `800 J ln(n_hi)`, so every `n′ ≤ n_hi` is handed to (B) at its own boundary.
* (A) cells certify every `n ≥ max(2^F, e^{j_a/(CJ)})`. For `n ≥ 2^40` and `j ≤ 800 J ln n`:
  * `j ≤ 2507 J`: A40.
  * `j ∈ [2507 J, 3.1e4 J]`: the ladder floor F(j) covers `n ≥ 2^{F(j)}`, and gap sweeps k = 40 … F(j) − 1
    cover the rest. Above `800 J ln n`, (B) applies.
  * `j ≥ 3.1e4 J`: `e^{j/(800J)} ≥ 2^56`, so the C = 800 cells apply.
* (B25) makes the dense band `b ≥ 150` at `n ≥ 2^25` certified. There the NR = 2 sweeps sit at
  0.95 – 1.0 of the allowance, with fringe class A near its top `b ≈ 500`.

## Worst margins

* **Float sweeps** (esc / allowance, intervals with `j > J`):
  * k = 20: 0.953;
  * k = 24: 0.997, at `j ∈ [8818, 10140] J`;
  * k = 25: 0.999;
  * k = 21 – 23, NR = 2: FAIL at up to 1.096; resolved by the fine sweeps (worst 0.643).

  The binding case is always fringe class A near its ceiling (`b → 4023/8`) at `n ≈ 2^20 … 2^25`.
* **Interval covers**: every cell is CERT-OK.
  * (B) cells stop bisecting as soon as a leaf certifies, so their worst-leaf margins are small by
    construction: −0.15 % of the allowance at `b ≈ 0.0064` (floor 30) and −0.03 % at `b ≈ 220` (floor 25).
  * Pointwise (B) values are at most about 0.6 – 0.75 of the allowance.
  * (A): the largest certified worst/allowance is 0.671, at `j ∈ [2180, 2507] J` (floor 2^40).
  * (A) ladder: worst 0.516, at `j ∈ [5042, 5798] J` (floor 2^44).
* The previous (J = 5e5) point had about 3× more room, because the allowance `j/J` is 3.3× smaller here.

## Analytic (A) bound for `j ≥ 1e6 J`, re-derived

This repeats ROUND1-ENERGY.md "(A) for j ≥ 1e6·J", with `C = 800`, so `ln n₀ = j/(800J) ≥ 1250`, and with
`f = 3329`.
* Step 1's choice `s = ½ ln n₀ − ln(eRu/λ)` needs `ln n₀ > 2 ln(eRu/λ) ≈ 4 ln j + O(1)`, which is about
  115 at `j = 1e6 J`. It holds, and the gap grows with j.
* `δ ≤ (5 ln j + E₀/L_c)/(j/CJ) ≲ 0.2`.
* With `λ = 1`, `r = 2`, `D = 3000`:

      escapes ≤ s₂(1 + D) + 2.67 j/D² + 16(s₂+1)(1+δ)/D + (s₂+1) − f s₂
              ≤ −326 s₂ + 2.97e-7·j + 1.02  <  j/J = 6.06e-7·j.

Status: sketch, unchanged from the earlier one except for the constants.

## What is certified and what is not

* **Interval-certified** (mpmath.iv, outward rounding, at float-chosen parameters):
  * every (B) cell (`coverB/`, `coverB25/`);
  * every (A) cell (`coverA/` CERT-OK cells, `coverA_ladder/`).
* **Float only:** all per-n sweeps (`sweeps/`, `sweeps_fine/`, `sweeps_gap/`) and the `b → 0` numerics.
  * No interval version of `route_d_rigorous_nr.py` exists.
  * The n-range `[2^17, 2^30)` (all j), `[2^30, 2^40)` (j below the (B) boundary) and the ladder gap
    `[2^40, 2^56)` therefore rest on floats.
* **Not certified, as in IV-CERT.md:**
  * the cell-monotonicity conventions in b, σ and j;
  * the monotone-average closure;
  * the round-1 tail extension from `d₀` to every `d ≥ d₀`;
  * the constant `c_ln = 80`;
  * the sup-over-n reductions of rd_sparse;
  * the probabilistic lemmas themselves.
* **Sketch:**
  * (A) `j > 1e6 J` (analytic, above);
  * (B) `b < 1e-6` (limit argument of ROUND1-ENERGY.md; the numerics are rerun at this point).

## Remaining for a complete fringe certificate at this point

1. Finish the PENDING float runs listed in the table.
2. Write an interval version of the per-n evaluator, `route_d_rigorous_nr.py` (Kingman `A*`, `k_bool`,
   collision, multiplicity, `Kmax`). Then rerun the sweeps above in it. Margins near class A's ceiling
   are thin (0.95 – 1.0 at NR = 2), so a certified rerun will need the fine n-grid in the dense band:
   NR = 2^{1/4} and j-ratio 1.05.
3. Write and check the `b → 0` limit argument and the analytic (A) tail.
4. Get a review.
