# Two-round Property F at f = 131040

Research note, 2026-10-10. This is a paper proof with certified numerics. Nothing here is checked in Lean. No Lean files were edited. Scripts are in `f2round/`:

* `cert.py` is the certificate. It uses exact rational preconditions and `mpmath.iv` outward-rounded intervals.
* `test_det.py` brute-forces the deterministic lemmas on 20 000 random small instances.
* `explore*.py`, `closed.py` and `fsearch.py` are float exploration only.

## VERDICT

1. **The two-round F contract is provable at f = 131040.** It holds for every n ≥ 16, every m ≥ f (so for every m = 2f + 64b), every rank 0 < j ≤ Jmax = ⌊δfn⌋, and both orientations. The parameters are g1 = 52416 (2f/5), g2 = 104832 (4f/5), c = 1/3 and b = 17000.
   * Failure on the σ1 side (SR or R1 fails, either orientation): at most **e^{-2076}**.
   * Failure on the σ2 side (R2 fails, either orientation): at most **e^{-227746}**.
   * Both come from the Lean-friendly closed forms in §5. `python cert.py 131040 52416 104832 1 3 17000` prints ALL CHECKS PASS.
2. **Smallest f by this proof.**
   * f = **92160** with exact ψ* and per-E evaluation (g1 = 35020, g2 = 88474, c = 359/1000, b = 8360). This passes with failure ≤ e^{-127}.
   * f = 98304 (3·2^15) also passes.
   * Float search finds this proof route infeasible at 91136. The binding constraint is the R2 slope q0 − c·L_Y.
   * The Lean-friendly closed forms (§5) need f ≥ ~114688. For example 114688 / 45875 / 97485, c = 1/3, b = 19000 passes.
   * Every closed-form check gets better as f grows (checked at f = 131040·k for k up to 2^20; see §5).
3. **No property of σ1 alone can give the large-rank contract.** σ2 = identity is a legal scramble. With it the second round does nothing, so "PF(σ1) ⇒ F2 for every σ2" implies one-round F at f. That is impossible for f < 4.3e7 once n ≥ (2f+1)/δ (the `chvatal-fringe-obstruction.md` adversary).
   * So `ExistsScrambleSeparator_twoSided_B2` must also take a **σ2 predicate PF2**. Its failure budget is next to the bulk-2 share of 1/1000 (≈20 Lean lines).
   * Small ranks (j ≤ J) do need only σ1.
4. **The previous analyst's joint-witness route is not provable as stated.** That route takes a union over input tops and multiplies over demanded columns. If σ2 collides, all f+e demanded cells sit in one column, at probability n^{-(A-1)}. Round 1 then only has to make that one column tall, at cost n^{-(Δ+A)}. Meanwhile the input-top entropy is (j/g1)·ln n = (E/(εg1))·ln n. So the ln n exponent is K − 2A − Δ > 0 for E ≳ 100: the bound is vacuous at large n.
   * The two-stage route below replaces it. It needs **no negative association, no row-choice entropy and no collision analysis.**
   * Every probabilistic step is the existing `scramble_tail_fixed_set`.

## 1. Setup and target statements

Heights are counted from the F₂ end (Lean's bottom rows, `topRows m h` = rows above the bottom h).

* Input sorted heights h_c, with Σh = j.
* After round 1: heights z. After round 2: heights w.
* Escapes = Σ_v (w_v − f)₊. These are the j largest keys outside F₂, i.e. `matrixOnesCountInRegion … f`.
* Constants: J = 86·10^6, ε = 1/J, δ = 128/4095, D = δf (= 4096 exactly at f = 131040), Δ = g2 − g1, Φ = f − g2.

For a top t = (h − g1)₊, let H_c(t, σ1) be the number of rows ℓ > g1 whose σ1-preimage cell landing in column c is marked. H depends only on t. Set ŷ_c = (H_c − Δ)₊.

For E ≥ 2, let j_E = min(EJ, Jmax), κ_E = ⌈cE⌉ and B_E = ⌈bE⌉.

* **SR(σ1)** (small ranks): for all t ∈ tops(g1, n, min(J, Jmax)) and all columns c, H_c ≤ f − g1.
* **R1(σ1)**: for all E ≥ 2 and all t ∈ tops(g1, n, j_E):
  * (a) there is no S with |S| = κ_E + 1 and Σ_S H ≥ (Δ+1)(κ_E+1);
  * (b) there is no S with 1 ≤ |S| ≤ κ_E and Σ_S H ≥ Δ|S| + B_E.
* **R2(σ2)**: for all E ≥ 2, every y ∈ ℕ^n with |supp y| ≤ κ_E and Σy ≤ B_E − 1, and every S ≠ ∅: onesInRows(y, σ2, all rows, S) < Φ|S| + E.

Here tops(g, n, j) is Lean's `tops`. Each of these is a property of one scramble, and each is a union of `tailBadSet`-type events.

**Target theorem (F2 from SR, R1, R2).** For f, g1, g2, c, b satisfying the preconditions in `cert.py`, and any σ1, σ2:
SR σ1 ∧ R1 σ1 ∧ R2 σ2 → `HasPackSemanticPropertyF2 hn σ1 σ2 f hfm (128/4095) eps`.

For the flipped pair, apply the same theorem to `flipScramble σ1` and `flipScramble σ2`.

**Existence.** In both orientations:
* #{σ1 : ¬(SR ∧ R1)} ≤ e^{-2076}·|Scr| at f = 131040. This is PF1, which fits the existing 483/1000 slot.
* #{σ2 : ¬R2} ≤ e^{-227746}·|Scr|. This is PF2, a new slot.

**Small-rank-only, σ1-only form.** This has the shape of `HasPackSemanticPropertyF`:

∀ v j, 0 < j → j ≤ J → (j:ℝ) ≤ δ·(f·n) → `matrixOnesCountInRegion hn (semanticExec hn σ1 (thr j v)) f = 0`.

SR implies it. Combined with the `of_F` monotonicity it gives zero escapes after round 2 for any σ2. This is the "intermediate property" asked about. SR is stronger and simpler than E_g(z) < ηj with η = (f−g)/J, which only implies max z < f.

## 2. Deterministic lemmas (all checked by `test_det.py`)

* **D1, monotone rounds.** For a fixed scramble, the output heights are coordinatewise monotone in the input heights: w_v = Σ_r [z_{π_r(v)} ≥ r].
* **D2.** z_c ≤ g1 + H_c(t). The ≤ g1 marks come from rows ≤ g1, and rows ℓ > g1 are marked exactly where t ≥ ℓ − g1.
* **D3.** Let ẑ = g1 + H (≤ m). Then w_v ≤ g2 + D_v(ŷ), where D_v(ŷ) is the number of rows r ≥ 1 with ŷ_{π2_{g2+r}(v)} ≥ r. This uses D1 with z ≤ ẑ, and the fact that for r > g2, ẑ_c ≥ r ⇔ ŷ_c ≥ r − g2.
* **D4, small ranks.** If j ≤ min(J, Jmax), SR and D2 give z ≤ f. Rows above f are then empty. Every column after scramble 2 has ≤ f marks, so escapes = 0 < εj.
* **D5, large ranks.** Take j ∈ ((E−1)J, EJ] with j ≤ Jmax, so the top t lies in tops(g1, n, j_E).
  * R1(a) applied to S = {c : H_c ≥ Δ+1} gives |supp ŷ| ≤ κ_E.
  * R1(b) applied to the same S gives Σŷ ≤ B_E − 1.
  * If escapes ≥ εj > E − 1, then escapes ≥ E (integers). With S = {v : w_v > f}, D3 gives Σ_S D_v ≥ Φ|S| + E. This contradicts R2.

This E-grouping is the only "rounding" in the proof. Ranks are never inflated: the mass bound j_E ≤ Jmax keeps the support condition. This replaces `round_event`'s rounding up to 86e6·E and its f ≥ 8.5e9 requirement.

## 3. Probability and counting (existing lemmas)

**Chernoff (`scramble_tail_fixed_set`).** Let the rows R carry ≤ M ones and let T ≥ Ms/n. Then P(onesInRows(R, S) ≥ T) ≤ (eMs/(nT))^T. A union over |S| = s multiplies by C(n,s) ≤ (en/s)^s.

**Tops count (`tops_card_le`).** Let K = j/(g+1). If j ≤ (g+1)²n, then

|tops(g, n, j)| ≤ Σ_{k ≤ K} C(n,k)·C(j,k) ≤ (K+1)·(e²n(g+1)²/j)^K.

The k-th term is increasing for k ≤ √(nj).

**Y count (new; same induction as `tops_card_le`, but tracking the support size).** The number of y with support ≤ κ and Σy ≤ B−1 is at most

Σ_{k ≤ κ} C(n,k)·C(B−1,k) ≤ (κ+1)·(e²n(B−1)/κ²)^κ, valid for κ² ≤ n(B−1).

**The resulting log-bounds** (L(g,n,j) denotes the tops bound):

* SR: L(g1, n, j0) + ln(en) + T0·ln(e·j0/(n·T0)), with j0 = min(J, Dn) and T0 = f − g1 + 1.
* R1a_E: L(g1, n, j) + (κ+1)·ln(en/(κ+1)) + (Δ+1)(κ+1)·ln(e·j/(n(Δ+1))).
* R1b_E: L(g1, n, j) + ln κ + max_{1≤s≤κ} [s·ln(en/s) + (Δs+B)·ln(e·j·s/(n(Δs+B)))].
* R2_E: lnY + ln n + max_s [s·ln(en/s) + T_s·ln(e(B−1)s/(nT_s))], with T_s = Φs + E.

**Chernoff validity** needs three things: Δ+1 ≥ D, f − g1 + 1 ≥ D, and Φ ≥ 2bD/J. All are checked exactly.

## 4. Worst cases over n and j (closed-form monotonicity)

Each bound is (terms increasing in j) + a·ln n with a < 0, as long as j ≤ Dn.

* For R1a, a = K − Δ(κ+1) < 0 follows from cΔ ≥ J/(g1+1).
* For R1b, a = K + s − Δs − B < 0 follows from b ≥ J/(g1+1).
* For R2, a ≤ κ + 1 − E ≤ 0 follows from c ≤ 1/2. Inside R2, the A-term below is also decreasing in n.
* With j = Dn the bounds increase in n.

So the supremum over the admissible set {16 ≤ n, j ≤ min(EJ, Dn)} is attained at specific points:
* R1: at n = EJ/D, j = EJ;
* R2: at n = (E−1)J/D;
* SR: at n = J/D.

**R1 at its worst point is linear in E.** Write α = J/(g1+1) and ts = α·ln(e²(g1+1)²/D). Then:

* R1a ≤ ln(αE+1) + E·ts + (cE+1)·β, where β = ln(eJ/(cD)) + (Δ+1)·ln(eD/(Δ+1)) < 0. This uses κ+1 ≥ cE+1.
* R1b terms equal E·ψ(s/E) + L, where ψ(σ) = σ·ln(eJ/(σD)) + (Δσ+b)·ln(eDσ/(Δσ+b)).
  * ψ is concave: ψ'' = −1/σ − b²/(σ²(Δσ+b)).
  * The exact route bisects ψ' and uses the concavity bound.
  * The Lean route uses ψ(σ) ≤ σ·[ln(eJ/D) + Δ·ln(eD/Δ)] + b·ln(eD/Δ) + 1/e, which needs the bracket ≤ 0.

**R2** has e·(B−1)s/(nT_s) ≤ ebE/(nΦ). Put q = ln(nΦ/(ebE)) ≥ q0 = ln(JΦ/(2Deb)) and A = 1 + ln n − Φq.

* The s-term is ≤ s(A − ln s) − Eq.
* The maximum over s ≥ 1 is A when A ≤ 1, and e^{A−1} otherwise.
* n·e^{−Φq} ≤ (EJ/D)·e^{−Φq0}, which is negligible.

With L_Y = ln(e²Jb/(Dc²)):

* Regime I (A ≤ 1, true for E ≤ 10^6): R2 ≤ ln(cE+2) + (cE+1)·L_Y + 2·ln(EJ/D) + 1 − (Φ+E)·q0.
* Regime II (E > 10^6): R2 ≤ ln(cE+2) + (cE+1)·L_Y + ln(EJ/D) + 1 + E·τ − E·q_N.

Both are exp(poly-log) · e^{−ΛE}. The sums over E have closed forms Σ E^k r^E.

## 5. Certified numbers (`cert.py`, interval arithmetic)

| f | g1 / g2 | c, b | SR (ln) | slopes λ_a / λ_b / Λ_I / Λ_II | ln(2P1) | ln(2P2) |
|---|---|---|---|---|---|---|
| 131040 (closed forms) | 52416 / 104832 | 1/3, 17000 | −128375 | 1771 / 1043 / 0.728 / 1.42 | **−2076** | **−227746** |
| 131040 (exact ψ*, b = 7000) | same | 1/3, 7000 | −128375 | 1771 / 2102 / Λ = 1.91 | −4194 | −3775 |
| 114688 (closed) | 45875 / 97485 | 1/3, 19000 | | all > 0 | passes | passes |
| 98304 (exact) | 36864 / 92160 | 17/50, 8200 | −87595 | 541 / 787 / 0.99 | −1565 | −1934 |
| 92160 (exact) | 35020 / 88474 | 359/1000, 8360 | −76807 | 116 / 68 / 0.090 | −127 | −128 |

* For f = 131040·k with g's at 2f/5 and 4f/5, every closed-form slope improves with k (1.42 → 6.0 at k = 2^20). In the formulas, q0 does not depend on f, while ts, β and L_Y decrease as f grows.
* A Lean proof uniform in f ≥ 131040 needs this monotonicity proved once with f as a real variable. That is still open: it is not written down.
* The exact rows evaluate E ≤ 2000 one at a time and use the regime-II tail beyond that.

**Failure budget per orientation pair:**
* σ1: 1/100 (bulk round 1, existing) + e^{-2076} (SR ∧ R1, both orientations) ≤ 483/1000. This is PF1 in `ExistsScrambleSeparator_twoSided_B2`.
* σ2: 1/1000 (bulk-2, BULK2.md) + e^{-227746} (R2, both orientations).
* Pigeonhole on pairs (flip × flip) needs 2(f1 + f2) < 1. Each side is generated independently.

## 6. What is proved and what is not

**Proved here (paper-level):**
* D1–D5;
* every inequality, for all n ≥ 16 and all j by the monotonicity in §4, and for all E by the closed-form sums;
* both orientations, by flip symmetry and equal failure counts (`card_filter_flip`).

**Not done:**
* the Lean formalisation;
* the f-uniformity proof (numerically monotone, see §5);
* a cross-check of the semantic ↔ combinatorial bridge for two rounds. The column sums of the intermediate state are `scrambledColSum c σ1` (BULK2's decode), and the bridge should be the same as for bulk.

The analysis is tied to the template value f = 131040. Anything with f < 92160 needs a different idea, for example a three-level R1 profile or an R2 entropy that is not paid per column.

## 7. Lean plan

Reused unchanged:
* `scramble_tail_fixed_set`, `avg_exp_onesInRows_le` (Tail);
* `tops`, `tops_card_le` (TopsCount);
* `choose_le_exp_pow`, `choose_mul_choose_le_of_le` (Ratio);
* `exists_and_flip`, `card_filter_flip`, the flip equivariance (FlipSpec);
* `HasPackSemanticPropertyF2`, `packNodeSpec2`, the B2 decode.

**Not used:**
* `Lemma62Round.round_event` (replaced by D5);
* `xval`, `Lemma62Numerics` and the 8/25 closure;
* `Lemma62Params` (replaced by new parameter records).

| # | New lemma (exact shape) | Reuses / generalises | Lines |
|---|---|---|---|
| 1 | `hits_top (g1) (t) σ c : ℕ`, `colSum_le_add_hits : scrambledColSum c σ1 col ≤ g1 + hits_top g1 (topOf g1 c) σ1 col`, `hits_depends_only_on_top` | `event_depends_only_on_top` (generalised from f/2 to g) | 80 |
| 2 | `round2_le : (scrambledColSum ẑ σ2 v) ≤ g2 + onesInRows (ŷ) σ2' univ {v}`, with monotonicity in heights | `ones_mono` | 90 |
| 3 | `F2_of_SR_R1_R2 : SR σ1 → R1 σ1 → R2 σ2 → HasPackSemanticPropertyF2 hn σ1 σ2 f hfm (128/4095) eps` (D4, D5, E-grouping with ⌈·⌉) | PackSpec2 decode, `matrixOnesCountInRegion_semanticExec` | 200 |
| 4 | `tops_card_le_gen (g n j) (hj : j ≤ (g+1)^2*n) : (tops g n j).card ≤ (K+1)*(e²n(g+1)²/j)^K` | `tops_card_le`; replaces TopsClosed's f/2 + 90/89 version | 100 |
| 5 | `ycap_card_le (κ B) : #{y : |supp| ≤ κ ∧ Σy ≤ B} ≤ (κ+1)(e²nB/κ²)^κ` | induction of `tops_card_le` plus a support counter | 140 |
| 6 | `SR_fail`, `R1a_fail E`, `R1b_fail E`, `R2_fail E`: card ≤ exp(closed form)·|Scr| | `badSetF_card_le` pattern, parameterised by (h, T(s), s-range) | 250 |
| 7 | Worst-point lemmas: each closed form is n^a·G(j) with a ≤ 0 and G increasing (power/rpow algebra, no calculus) | — | 200 |
| 8 | Numerics at (131040, 52416, 104832, 1/3, 17000): λ_a, crude λ_b, Λ_I, Λ_II > 0; Σ_E bounds ≤ e^{-2000}. Margins are ≥ 0.7 per unit and thousands overall, so `Real.log_le_sub_one_of_pos`, `log_two` bounds and `norm_num` suffice | `Lemma62Numerics` style | 350 |
| 9 | `ExistsScrambleSeparator_twoSided_B2'` with `PF2 : Scramble → Prop` and `hPF2 : fail ≤ 1/1000`; σ2 predicate becomes `B2comb ∧ PF2` with c := 2/1000 | `ExistsScrambleSeparator_twoSided_B2` | 30 |
| 10 | f-uniformity (all even f ≥ 131040, g's = ⌊2f/5⌋, ⌊4f/5⌋), or fix f per template | GeometryScale/NodeGeom: replace `85e8 ≤ f` | 80–200 |

Total is about 1500–1650 lines, most of it (rows 6–8) mechanical.
