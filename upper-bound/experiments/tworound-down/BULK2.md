# Two-round bulk lemma B2: audited proof, certified numerics, Lean plan

Research note, 2026-10-10. This is a hand proof plus certified numerics. Nothing here has been
checked in Lean. Scripts: `bulk2_check.py` (certificates; output in `bulk2_check.out`) and
`bulk2_sanity.py` (exact small-case checks).

## VERDICT

* **The contraction works.** The two-round bulk lemma holds with ε_B2 = d := 1/59 000 000 for
  **every m ≥ 2^42 and every n ≥ 16**. That covers the window 2^42 < m ≤ 2^43. The decisive
  inequalities are certified with exact rationals, using only ln 2 < 0.6931471808
  (`Real.log_two_lt_d9`). The round-2 margin is large: at m = 2^42, m·K = 42.53 against
  ln(2(m+1)) ≤ 29.81.
* **Failure budget, per orientation:** round 1 < 1/100 (existing `lemma61_failFactor_lt_one_hundredth`);
  round 2 ≤ 1/1000 (actually ≤ e^{-200}). With the existing F share of 483/1000 the total is
  494/1000 < 1/2. That is exactly what the pair version of `exists_and_flip` needs.
* **Smallest m.**
  * Variant A (one tail; reuses almost everything) works for m ≥ 2^41.658 ≈ 3.47·10^12. Certified
    breakpoint: m ≥ 2^42.
  * Variant B (two-tailed in both rounds, which requires exact mass) works for
    m ≥ 2^40.624 ≈ 1.69·10^12. Certified breakpoint: m ≥ 2^41.
  * An ℓ1-ball count of the admissible states gains only about 0.35 in log₂ m, which changes no
    power-of-two window.
* **Three scrambles do not pay.** They lower the threshold to about 2^37.0 (A) or 2^36.0 (B), but each
  extra full column sort costs more than the saving. Doc cost model, coefficient =
  (sorts)·(k+1)(k+2)/4:

  | Scrambles | Variant A | Variant B |
  |---|---|---|
  | 1 (today, 2^58) | 1770 | — |
  | 2 | 1419 (k = 42) | **1354.5** (k = 41) |
  | 3 | 1482 (k = 37) | 1406 (k = 36) |

* **Corrections to `docs/chvatal-two-round-separator.md`.**
  * The union over thresholds is unnecessary, because exact mass fixes i.
  * The orientation union ln(200m)/16 is unnecessary, because the flip is handled by pigeonhole.
  * The doc's budget omitted the F share. It fits only if round-2 failure is ≤ 1/1000.
  * Its "explicit proof obligation" (the hypergeometric MGF comparison) is **already proved** in
    Lean: `avg_exp_hit_le` / `avg_exp_onesInRows_le`.
  * The Bernstein step needs only a 3-term `Real.exp_bound`. The doc's numbers (I ≈ 42.65) are
    essentially right.
* **This does not help the sorter on its own.** The F (fringe) existence at m ≈ 2^42 with the
  scheduler's fringe ratio is still open (doc §3, `chvatal-fringe-obstruction.md`). The physical
  pack, `packSpec_high`, and the claim that F is deterministically preserved by later rounds are
  outside this note and still need Lean proofs.

## 1. Exact statement

Notation follows Lean.
* c : `MonotoneColumnSums m n`, a column-height vector.
* a_r = |`monotoneRowOnes c r`| and p_r = a_r/n.
* `onesAboveBottom c σ i` = Σ_j (`scrambledColSum c σ j` − i)₊.
* exc(c,i) := Σ_j (c_j − i)₊, which equals `onesAboveBottom c 1 i`.

**Round-1 predicate (existing).** `HasCombinatorialPropertyBOnPipeline σ1 E1` holds iff for every c and
i with total(c) ≤ n·i and 1 ≤ i ≤ m, we have onesAboveBottom c σ1 i < (E1/2)mn.

**Round-2 predicate (new).** `HasCombinatorialPropertyB2 σ2 E1 d` holds iff for every c and i with
total(c) = n·i, 1 ≤ i ≤ m, and exc(c,i) < (E1/2)mn, we have onesAboveBottom c σ2 i < (d/2)mn.

**Semantic two-round B.**

`semanticExec2 hn σ1 σ2 x := semanticExec hn σ2 (semanticExec hn σ1 x)`

The inner re-sort of an already column-sorted Bool matrix is the identity on values, so physically
there are 3 sorts.

`HasPackSemanticPropertyB2 hn σ1 σ2 d` holds iff for every v : Perm(Fin (mn)) and every i with
1 ≤ i ≤ m:

`matrixOnesCountInRegion hn (semanticExec2 hn σ1 σ2 (fun w => largestKeyThresholdJ01 (i*n) (v w))) i < (d/2)·(m·n)`

This has the same quantifiers as `HasPackSemanticPropertyB`.

**Theorem B2.** Let m ≥ 2^42, n ≥ 16, E1 = 371/10^8, d = 1/59 000 000. Then:
1. Fewer than 1/100 of the σ1 fail round 1.
2. At most 1/1000 of the σ2 fail round 2.
3. If both predicates hold, then `HasPackSemanticPropertyB2 hn σ1 σ2 d` holds.
4. Hence there is a pair (σ1, σ2) such that both (σ1, σ2) and (flip σ1, flip σ2) satisfy B2.

## 2. Proof

**(a) Quantifiers.** σ1 must work for every first-sorted state c, which is the existing universal
statement. σ2 must work for every *admissible* intermediate state c′, meaning exact mass and
exc(c′, i) < (E1/2)mn. It is chosen by a union bound over all c′ ∈ {0..m}^n. So σ2 does not depend
on σ1 and no exchange of quantifiers occurs.

The good pairs form a product set, so the fraction of failing pairs is at most f1 + f2. Since
flip × flip is an involution of pairs that preserves the failure count, the pigeonhole of
`exists_and_flip` applies verbatim on `Scramble × Scramble`.

**(b) Decode.** Let c be the column sums after the first sort, so total(c) = i·n
(`sum_topJ_colSums_eq_j`). Write u = semanticExec σ1 x. `matrixOnesCountInRegion_semanticExec` gives:
* the column sums of u are c′_j = `scrambledColSum c σ1 j`;
* exc(c′, i) = onesAboveBottom c σ1 i < (E1/2)mn;
* total(c′) = i·n, since column-local networks and the row permutation preserve the count;
* the final count equals onesAboveBottom c′ σ2 i.

**(c) Variance identity (needs exact mass).** Write A_r for the ones of row r, so a_r = |A_r|. Then
a_r(n − a_r) counts the pairs (j, l) with j ∈ A_r and l ∉ A_r, that is c_l < m − r ≤ c_j. Summing
over r gives

  Σ_r a_r(n − a_r) = Σ_{j,l} (c_j − c_l)₊ ≤ Σ_{j,l} [(c_j − i)₊ + (i − c_l)₊] = n·exc + n·Σ_l (i − c_l)₊.

At exact mass, Σ_l (i − c_l)₊ = exc. Therefore

  **V := Σ_r p_r(1 − p_r) ≤ 2·exc(c′, i)/n < E1·m.**

With only total ≤ n·i this fails. Example: half the columns are 0 and the other half sit just below i.
Then exc = 0 but V is about m/8.

**(d) Per-row Bernoulli bound (new elementary lemma).** For 0 ≤ p ≤ 1 and 0 ≤ λ ≤ 1:

  1 − p + p·e^λ ≤ exp(pλ + c(λ)·p(1 − p)),  where c(λ) := λ²(1/2 + 2λ/9).

*Proof.* `Real.exp_bound` (n = 3): e^x ≤ 1 + x + x²/2 + (2/9)|x|³ for |x| ≤ 1. Apply it
at x = λ(1 − p) and at x = −λp. Since |y|³ ≤ y² for |y| ≤ 1:

  p·e^{λ(1−p)} + (1−p)·e^{−λp} ≤ 1 + 0 + (λ²/2 + 2λ³/9)·[p(1−p)² + (1−p)p²] = 1 + c(λ)·p(1−p).

This is at most exp(c(λ)·p(1−p)) by `Real.add_one_le_exp`. Multiplying by e^{λp} gives the claim. ∎

This loses only the factor 1 + 4λ/9 (≈ 1.001) against λ²/2.

**(e) Per-(c′, S) tail.** Take S = `excessColumnSet` with s = |S| ≤ n. If B2 fails, then
`lemma61_excess_columns` gives Y := onesInColumns c′ σ2 S ≥ s·i + T with T = (d/2)mn.

`avg_exp_onesInRows_le` with φ from (d) applies; it already contains the hypergeometric-to-binomial
comparison `avg_exp_hit_le`. Using Σ_r p_r = i (exact mass), it gives

  avg_σ e^{λY} ≤ exp(s·(λi + c(λ)·V)).

`scramble_markov` then gives

  fraction(bad) ≤ exp(−λT + s·c(λ)·V) ≤ exp(−n·m·K),  where K := λd/2 − c(λ)·E1.

Here s ≤ n and V < E1·m. The state index i is a function of c′, so there is no union over i.

**(f) Union.** Summing over (c′, S) ∈ (m+1)^n × 2^n gives

  f2 ≤ exp(−n·g(m)),  where g(m) := m·K − ln(2(m+1)).

g is increasing once K(m+1) ≥ 1. Proof for Lean: ln(2(m+1)) ≤ ln(2(M+1)) + m/M − 1, and
mK ≥ MK + (m − M)K. So for m ≥ M = 2^42 and n ≥ 16, f2 ≤ exp(−16·g(2^42)).

**(g) Constants.** Take E1 = 371/10^8, λ = 1/437, d = 1/59e6.
* Round 1: E1²·2^42 − 2(1 + 42·ln2_hi) = **0.3108 ≥ 0**. So
  √(2(1 + ln m)/m) ≤ E1 for all m ≥ 2^42 (`chernoff_mono`).
* Round 2: 2^42·K = **42.525** and ln(2(2^42 + 1)) ≤ 43·ln2_hi + 2^-42 = 29.805, so
  g(2^42) ≥ 12.72. Hence f2 ≤ e^{−203} < 1/1000.
* For Lean it is enough to show g(2^42) ≥ 1, since e^{−16} < 1/1000.

**(h) Variant B (two tails).** If s > n/2, the event Σ_S(c″ − i) ≥ T equals Σ_{S^c}(c″ − i) ≤ −T
(exact mass). In terms of zeros in S^c this is an upper-tail event with densities q_r = 1 − p_r,
where Σq_r = m − i and q(1 − q) = p(1 − p).

The zeros of c′ in row rev r are the ones of the state m − c′ in row r. So the existing ones-only
MGF lemma applies after the bijection σ ↦ σ ∘ rev. This gives s′ = min(s, n − s) ≤ n/2 and
K_B = λd/2 − c(λ)·E1/2.

Round 1 can be two-tailed the same way, with Hoeffding exponent ε²mn. That needs the exact-mass
interface in round 1 as well; the old ≤ interface breaks the lower tail. The requirement becomes

  E1²·m ≥ ln(2(m+1)) + ln(100)/16.

Certified at k = 41 with E1 = 366/10^8 and λ = 1/216: round-1 margin 0.057, round-2 margin 13.5.

## 3. Audit of the derivation in `docs/chvatal-two-round-separator.md`

| Doc item | Status |
|---|---|
| L = (2/n)·Σ(s_c − i)₊ needs exact mass | Correct; see (c). The exact-mass hypothesis is free in the semantic setting. |
| V = (1/2n²)·Σ\|s_c − s_d\| ≤ L ≤ e·m | Correct. |
| Hypergeometric vs Bernoulli MGF "obligation" | Already a Lean theorem: `avg_exp_hit_le` (λ ≥ 0, any A, S) and `avg_exp_onesInRows_le` (product over rows, arbitrary φ). Reuse as is. |
| Bernstein rate I = d²m/(8e + 4d/3) | Correct as Bernstein. The Lean route in (d)/(e) gives I = λd/2 − c(λ)·e, essentially the same (42.53 vs 42.65 at 2^42). |
| Union × m thresholds | Unnecessary (i = total/n). Harmless. |
| ln(200m)/16 for "both orientations" | Unnecessary. Orientation is handled by the flip pigeonhole on the per-orientation fraction. |
| "Failure < 1/100" | Wrong budget. With F at 483/1000 we need f1 + f2 < 0.017. Use f1 < 1/100 and f2 ≤ 1/1000. |
| Floating-point numerics | Replaced by rational certificates; the conclusions stand. |
| (3, 38, 1482), (4, 36, 1665) | The (3, ·) row is confirmed: k = 37 (A) is certified, k = 36 (B) is located but not rationally certified. Still not cheaper. |

## 4. Certified numbers

`bulk2_check.py` checks every pass/fail decision with exact rationals, with mpmath interval
arithmetic (`mpmath.iv`) as a cross-check. Each certificate is valid for **all m ≥ 2^k and all
n ≥ 16**.

| k | Variant | E1 | λ | Round 1 margin | Round 2: m·K − ln(2(m+1)) − ln(1000)/16 | Result |
|---|---|---|---|---|---|---|
| 42 | A | 3.71e-6 | 1/437 | +0.311 | **+12.29** | certified |
| 41 | A | 5.18e-6 | 1/611 | +0.167 | −14.31 | fails (no λ, E1 can fix it) |
| 41 | B | 3.66e-6 | 1/216 | +0.057 | **+13.52** | certified |
| 40 | B | 5.12e-6 | 1/302 | +0.116 | −13.45 | fails |
| 37 | A, 3 scrambles | 1.971e-5 → 1.77e-7 → d | 1/222, 1/21 | +0.100 | +0.48, +0.53 | certified |

Real thresholds, located by 200-bit bisection over the optimal λ and E1 (locating only, not a
certificate):

| Construction | Threshold (log₂ m) |
|---|---|
| 2 scrambles, A | 41.658 |
| 2 scrambles, B | 40.624 |
| 2 scrambles, A + ℓ1 count | 41.31 |
| 2 scrambles, B + ℓ1 count | 40.26 |
| 3 scrambles, A | 36.97 |
| 3 scrambles, B | 35.95 |

`bulk2_sanity.py` checks on exact small instances:
* the identity in (c);
* the bound in (d) on a grid;
* the exact MGF comparison and tail bound in (e), via exact convolution of hypergeometrics.

All pass. These checks are not part of the proof.

## 5. Lean plan (variant A, window k = 42)

Reused unchanged:
* `avg_exp_hit_le`, `avg_exp_onesInRows_le`, `scramble_markov`, `lemma61_excess_columns`
* `lemma61FailBound_onPipeline` (round 1, with epsB := E1), `lemma61_failFactor_lt_one_hundredth`
* `matrixOnesCountInRegion_semanticExec`, `matrixOnesCountInRegion_colSort_eq_sum_columnSub`
* `sum_topJ_colSums_eq_j`, `totalColumnOnes_eq_sum_rowOnes`
* `semanticExec_flip`, `card_filter_flip`
* `chernoff_mono` (make it public)

New lemmas:

| # | Statement (abridged) | Lines |
|---|---|---|
| 1 | `bernoulli_mgf_bernstein (h0 : 0 ≤ p) (h1 : p ≤ 1) (hl0 : 0 ≤ λ) (hl1 : λ ≤ 1) : 1 - p + p * exp λ ≤ exp (p*λ + λ^2*(1/2 + 2*λ/9) * (p*(1-p)))`, via `Real.exp_bound` (n = 3) and `Real.add_one_le_exp` | 45 |
| 2 | `sum_rowOnes_mul_compl_le (hc : totalColumnOnes c = n*i) : ∑ r, (a r : ℝ)*(n - a r) ≤ 2*n*(excessAbove c i)`, where `excessAbove c i := ∑ j, ((c j).val - i)` | 90 |
| 3 | `lemma63BernsteinBound`: if total = n·i, 0 ≤ λ ≤ 1, and every σ ∈ bad has i·\|S\| + T ≤ onesInColumns c σ S, then \|bad\| ≤ exp(−λT + \|S\|·c(λ)·V)·N | 50 |
| 4 | `HasCombinatorialPropertyB2` and `failBoundB2 : #fail ≤ (2(m+1))^n · exp(−n·m·(λd/2 − c(λ)·E1)) · N`, copying the structure of `lemma61FailBound_onPipeline` | 100 |
| 5 | `failFactorB2_le (hm : 2^42 ≤ m) (hn : 16 ≤ n) : … ≤ 1/1000` and `epsB1_le : √(2(1+log m)/m) ≤ 371/10^8`, via monotonicity (f), `Real.log_two_lt_d9`, `norm_num` | 70 |
| 6 | `semanticExec2`, `HasPackSemanticPropertyB2`, and `of_combinatorial_B2 : HasCombinatorialPropertyBOnPipeline σ1 E1 → HasCombinatorialPropertyB2 σ2 E1 d → HasPackSemanticPropertyB2 hn σ1 σ2 d`, using decode (b) | 90 |
| 7 | `exists_and_flip₂` on `Scramble × Scramble` with `(flip, flip)`, plus `semanticExec2_flip` (two applications of `semanticExec_flip`) | 50 |
| 8 | `ExistsScrambleSeparator_twoSided_B2 (hm : 2^42 ≤ m) (hn : 16 ≤ n)`, budget 1/100 + 1/1000 (+ 483/1000 with F) < 1/2 | 40 |

Total for variant A: **about 535 lines**. Variant B adds about 200 lines (complement-state
bijection, two-tailed round 1 at exact mass) and moves the window down to k = 41.

**Downstream constants.**
* `invEpsB = 1/59e6` is unchanged.
* `paperOrdinaryEpsB` should become the rational 1/59 000 000; `paperOrdinaryEpsB_le` then becomes
  `le_refl`. Alternatively keep the old definition for the root.
* `Theorem51Params.hepsB_lb` (√(2(1 + ln m)/m) ≤ epsB) is false at 2^42 for epsB = d. Replace it
  with a two-round field, or drop it, carrying E1 internally.
* `NodeGeom.hm1 : 2^58 < m` → `2^42 < m`. The 2^58 constants in `GeometryScale`/`RealNets` are
  coupled to F and the scaling, so they are not covered here.
* `paperRootEpsB` (2^79) is untouched unless the root also moves to two rounds.
* The physical pack (`physicalPackNet`, `packSpec_high/low`) must be redefined for three sorts with
  two row relabelings. This is not estimated here.

## 6. Caveats

* B2 only. The sorter does not improve until the F existence at m ≈ 2^42 is proved at the
  scheduler's fringe ratio.
* The deterministic F-preservation argument (doc §2) is plausible but not audited here.
* The real thresholds (2^41.66, 2^40.62, 2^36.97, 2^35.95) and the three-scramble k = 36 (B) row are
  located with 200-bit floats, not certified. The rows k = 42 (A), k = 41 (B), and k = 37
  (A, 3 scrambles) are rationally certified.
* Variant B's round-1 lemma (two-tailed Hoeffding at exact mass) is proved in (h) by hand only.
