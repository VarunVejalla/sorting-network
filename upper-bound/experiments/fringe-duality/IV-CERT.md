# Interval certification of the route (d) cell evaluators

New files: `rd_scaled_iv.py` (regime B, `escapes_cell`), `rd_sparse_iv.py` (regime A, `escapes_merged` /
`worst_merged`), drivers `rd_scaled_out/coverB_iv.py` and `rd_scaled_out/coverA_iv.py`, and sample outputs
in `rd_iv_cert/`. `rd_scaled.py` and `rd_sparse.py` are not modified. They are imported for the float plan.

## Method

This follows `../sub500-screen/cert_walk_n.py`. The float search picks every free parameter: λ, t, κ, s, c,
(D, ratio), and the α/κ sub-cells of each exclusion. The final inequality at that parameter is then
re-evaluated in `mpmath.iv` (dps 40, outward rounding), and its upper end is used.

* Inputs are exact. The float cell ends b, σ are exact rationals. ν = (hi−lo)σ, e_S, ε and n₀ are
  enclosed. n₀ and ln n₀ use certified **lower** ends, since ε is decreasing in n, and "for all
  n ≥ e^x" is stronger for a smaller x.
* For a min over alternatives, any certified alternative is a valid bound. The float argmin is certified
  first; the others are tried only if it fails or comes out worse than the next float value.

## What is certified (regime B, `escapes_cell_iv`)

* **A\*.** The claim "every α ∈ [A, amax] is excluded" is re-proved by a top-down geometric cover of
  [A_float, amax_up], with cells of ratio ≥ 1.02.
  * Each cell [a0, a1] is checked at a1 against a0. q, nlnG and the count entropy are nondecreasing in α,
    so this is the float code's monotone step.
  * The certified A is the bottom of the contiguous certified run below amax, so a failure partway up
    acts like the float restart.
  * If nothing is certified, A = amax (the mass bound).
* **k_bool.** The same cover for κ ∈ [k, ν_up], with cells of ratio ≥ 1.01. The top end is the exact ν,
  not the float-rounded ν.
* **Closed forms at the float argmin:**
  * `A_coll_s`, checking q < 1 and qe^s < 1;
  * `mult_excess_s`, with exact binomial pmf recurrences and the geometric tail past K;
  * the high-rows t-min. Its profile entropy is monotone in (N, w) for N ≤ 1, so it is evaluated at the
    certified upper ends.
* **Round-1 tail at d₀.** A cover of [ahat, R b], with cells of ratio ≥ 1.005, checking q ≤ 1/2.
* **`kmax_sources_s`.** Exact `Fraction` arithmetic at the certified A.
* **Level structure.** The caps R = ⌈hi − b_lo⌉, floors d = ⌊lo + 1 − b_hi⌋ and the high-rows offset are
  computed exactly.

**Regime B driver (`coverB_iv.py`).** Same cell logic as `coverB.py`: C = 100, floor 2^30 (or
`NMIN_LOG2=24`), a bottom cell, σ-cells of ratio 2 with depth ≤ 14, and closure by `count/σ_hi < f`. The
float value decides where to split. Every leaf, the bottom cell and the closing test are certified; a leaf
that fails certification is split further.

## What is certified (regime A, `escapes_merged_cert`)

* **`a_coll_sup_ln` and `mult_sup_ln`** are evaluated at the float argmin (λ, s) and (c, t):
  * exact binomials, and n₀ = e^x handled in iv (no overflow or underflow);
  * the checks q₀ e^s < 1 and the tail ratio < 1.
* **Exponent x.** A certified lower bound of max(40 ln 2, j_a/(100J)).
* **ln(1/η).** Taken as ln 10⁴.
* **Loads.** `worst_merged_iv` re-runs the set-size loop with certified loads. The exit test L/s < f is
  certified.

## Soundness issues found in the float code (all repaired in the iv versions)

1. **`ln_count_s`** uses ν·H(κ/ν) with κ up to ν. This is not monotone, and above ν/2 it **underestimates**
   #{supports of size ≤ κ}: at κ = ν it gives 0 instead of ν ln 2. The iv version uses H(min(x, 1/2)).
2. **`k_bool_s`** checks the cell [κ_lo, κ] with H at κ. Above ν/2 this is the cell's *minimum* entropy,
   and the top cell uses H(1) = 0. The iv version uses sup H over [κ_lo/ν_up, κ/ν_lo].
3. **`round1_level_tail`** uses x ln(e/x), x = α/d², which decreases for x > 1. Above x = 1 the binomial
   bound itself is invalid. The iv version uses x = min(α/d², 1) in that term.
4. **`rd_sparse.escapes_merged`.** For ln n₀ ≥ 700, b0 underflows to 0, so ⌈b0⌉ = 0 and the offset floor
   d − 0 is not a lower bound of d − b. The iv version uses d − b0_up. Also, the float ln n₀ and ln(1/ETA)
   can be off by an ulp in the wrong direction. Both are numerically negligible.
5. **Float level structure.** `math.ceil(hi - b_lo)` could round the wrong way near integers. The iv
   version computes it exactly. On the sample it never differed.

None of these changed any sample value: the A\*/k_bool covers succeeded from the float starting point, and
`A_fail = kb_fail = tail_fail = 0`.

## NOT certified (still float-level or analytic claims)

* The (b, σ) cell-monotonicity conventions. These are ROUND1-ENERGY.md "Cell covers". Each ingredient is
  nondecreasing in σ (LP for kmax, stochastic order for Bin, u·H(k/u) increasing in u), but this is not
  machine-checked.
* The **monotone average** closure (L(s)/s nonincreasing, L nondecreasing). This is used by both drivers
  and in the 1.05-cells of `worst_merged`.
* The extension of `round1_level_tail`'s exclusion from d₀ to every level d₀·ratio^i, which the docstring
  calls "relative monotonicity". Only d₀ is certified.
* The constant c_ln = 80 in `eps_level` (absorbing the ln n, ln(top), ln(1/η) and ln #grid terms).
* The sup-over-n reductions in rd_sparse (the Moebius map, t(n) = t* + x), the j-monotonicity of the
  j-interval convention, and the probabilistic lemmas themselves.
* `b < 1e-6` (B) and `j > 1e6 J` (A). These are outside both covers, as before.

## Commands

```
cd rd_scaled_out
python -I coverB_iv.py cell 10 13                 # one b-cell
python -I coverB_iv.py <part> <nparts>            # full B cover (b in [1e-6, 1.25e6], ratio 1.3, floor 2^30)
NMIN_LOG2=24 python -I coverB_iv.py <part> <nparts> 150 1.25e6     # the coverB24 variant
python -I coverA_iv.py near 1 100 1e4             # the A cells containing these j/J
python -I coverA_iv.py <part> <nparts>            # full A cover (j in [1, 1e6 J], ratio 1.15)
```

## Sample results (`rd_iv_cert/*.out`)

The float values are the current rd_scaled / rd_sparse code. The old `coverB_*.out` predate `A_coll` and the
adaptive dtop, so they differ.

| cell | float worst (esc − allowed) | certified | rel. to allowance | time |
|---|---|---|---|---|
| B b ∈ [1e-6, 1.3e-6] | −8.407648e-13 | −8.407648e-13 | −0.420 | 19 s |
| B b ∈ [10, 13] | −3.409477e-06 | −3.409477e-06 | −0.171 | 23 s |
| B b ∈ [1e3, 1.3e3] | −1.448216e-03 | −1.448216e-03 | −0.724 | 17 s |
| B b ∈ [1e5, 1.3e5] | −1.996590e-01 | −1.996590e-01 | −0.998 | 3 s |
| A j ∈ [0.8829, 1] J | −3455.893177 (allowed 1) | −3455.893177 | | 2 s |
| A j ∈ [87.57, 100.7] J | −2975.585559 (allowed 87.57) | −2975.585559 | | 11 s |
| A j ∈ [8818, 10140] J | 239.0525723 (allowed 8818) | 239.0525723 | | 22 s |

* All are CERT-OK.
* Certified and float totals agree to about 1e-11 relative. Sometimes the certified value is slightly
  lower, because the finer A\* cover goes below the float A\*.

## Runtime estimate

* **B.** About 3–25 s per b-cell, since high rows are cached per b-cell. With 107 cells, the full cover is
  about 0.5–1 h serial, or about 15 min on 4 parts. The coverB24 variant is about 15 min serial.
* **A.** The cost is the float plan, the same as `coverA.py`, which logged about 5 h serial with 1500 s
  cells near 1e6 J. The interval evaluation adds under 5 %. That is about 1.5 h on 4 parts.
