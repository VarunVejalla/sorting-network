# Review of INDUCTION-v6 §11–15, PROOFS-L3-L4 (L3 full, L4 full), ROUND1-ENERGY route (d) n → ∞, and the L3 Lean statements (2026-10-23)

Independent review (Claude Opus 5.5, fresh context). I modified no tracked file. Scratch runs used a copy of
`transbox_analytic.py` with `EPSB` read from the environment. I did not touch any running sweep.

## Verdict

**The 477 package is not supported as written. Two accounting errors each break it. A ~490 variant looks
plausible.**

* **Band budget.** L3b as proved gives a band-escape bound of `d/2 + 2T(W)` **per cut and direction**. That
  is `d + 4T(W)` per block. The package budgets `d + 2T(W)` (finding 1). At `2W = 2^18` the band needs
  `ε_B ≥ 2.93e-5`, and at that ε_B the formula box is 1.124.
* **Property F under band repair.** Route (d) certifies Property F for a *fully sorted* third stage. With
  band repair, fringe keys sitting above the F-cut's segment after σ2 are never moved. Their count can be
  about 0.95 × the whole allowance `j/J` (finding 2). This is not in any evaluator.

Moving to `2W = 2^19` (depth 190, cost 490) appears to repair finding 1: box ≈ 0.990 with an estimated
far tail. Finding 2 must then be added to route (d) at the 2^19 band, where it is about half the allowance.

**Correct as far as I checked:**
* the transition-box algebra and its code;
* S1, S2 and S2e up to small stale constants;
* L3a/L3b as deterministic lemmas, and their Lean statements;
* the n-interval and cell monotonicity conventions in route (d), and its coverage table, apart from the
  open items listed.

## Findings

**1. HIGH: band-repair Property-B budget off by a factor 2 on T.**
*Where:* PROOFS-L3-L4.md "Bounds" (lines 151–152); INDUCTION-v6 §8 item 2 and §10 (`2·tail(2^17) = 7.22e-6 ≤
ε_B − d = 7.59e-6`); `screen.py: band()` (`d + 2·tail ≤ ε_B`).

*What is wrong.* L3b bounds the X-keys above cut i by `Σ(c″−i)₊ + E⁺(i+W) + E⁻(i−W) ≤ (d/2 + 2T)·a`. That
is one cut and one direction. A block's intruders come from two cuts (lower cut upward, upper cut downward),
and these involve different threshold sets X. L2 and R1 Lemma 4.2′ charge `ε_B·a` per block, i.e. `ε_B/2`
per cut and direction. Band repair is therefore within Property B only if `d + 4T(W) ≤ ε_B`. The doc's line
"two-sided: d + 2T(W)" doubles d/2 but not 2T. A joint bound on `Σ_k(|c′_k − i| − W)₊` is genuinely
two-sided: the walk bound gives `2T` for it, not `T`.

*Numbers.*
* `d + 4T(2^17) = 1.491e-5 + 1.444e-5 = 2.934e-5 > ε_B = 2.25e-5`.
* At ε_B = 2.5e-5 / 2.94e-5 the formula box gives **1.036 / 1.124** (scratch copy of `transbox_analytic.py`).

*Fix.* Use W = 2^18 (2W = 2^19, S(19) = 190, cost 490):
* `d + 4T(2^18)` ≈ `1.491e-5 + 4·1.63e-6 = 2.14e-5 ≤ 2.25e-5`, using the float NA-table value; this needs
  certifying.
* The far margins drop to `d₀ − 2^18 ≈ 0.02718·16547000 − 262144 ≈ 187,600` rows. With an assumed
  `T(187,600) ≈ 2.5e-6` (to be certified) the box gives **0.98993**.
* The near threshold 0.02734 still leaves a margin of at least 190k rows, so S2 is unchanged.
* `screen.band`, §7–§10 and PROOFS line 152 must all be restated with 4T.

**2. HIGH: route (d) does not model the band stage, so Property F is unproved for the separator actually used.**
*Where:* ROUND1-ENERGY.md route (d) (`escapes(S) = Σ_levels count − f s₂`); PROOFS-L3-L4 L3 (band
segments at every output cut, including F₁|B₁); `SegmentSort.lean` header ("clipped segments shifted to
[0, 2W)"). "Band" appears nowhere in ROUND1-ENERGY or the `rd_*` code.

*What is wrong.* The F₁|B₁ cut is at about row f+1 (≈ 3968 rows), so its segment is `[0, 2^18)`. A fringe
key at row ≥ 2^18 after σ2 is never sorted down and lands outside F₁. The row identity makes the count of such
keys exactly `Σ_T (z_T − 2^18)₊`, a round-1 quantity. Route (d)'s escapes only count `load_v − f` on sets S,
so this term is missing.

*Size.* Fact 3's attack (|A| targets of height k at cost |A|k²/2) gives, at k = 2^19, `Σ(z − 2^18)₊ = j/2^19 =
1.91e-6·j`. The allowance is `j/J = 2.0e-6·j`. This needs `j ≥ k²/2`, i.e. `n ≳ 2^28` at f = 3967, which is
inside the certified range.
* With the 2^19 band of finding 1, it is about `j/2^20` (≈ 0.48 of the allowance).
* For large classes (centred segments at row f+1), it is about `C₁ j/(4(f+W))`.

*Fix.* Add the term `E⁺_fringe(top of the F-cut segment)` to every route-(d) evaluator. The high-rows / A*
energies (`Σ(z−c)₊ ≤ E_{≥}/(4c)`) can bound it. The fixes for findings 1 and 2 then have to be re-run
together. If the slack is too thin, make the F-cut segments taller.

**3. MEDIUM: the 321,400-row margin is not achieved at the bottom of the row window.**
*Where:* INDUCTION-v6 §15 ("`≥ 0.027237·a` … `cH ≤ T(321400 rows)·a`", near threshold 0.02734);
`transbox_analytic.py` line 44.

*What is wrong.* The margin is `dL·m − W` with `m ≥ 16547000`:
* `0.027237·16547000 − 2^17 = 319,619`;
* with S1 updated to 1.01693 (§14), S3's bound is 0.027183, giving **318,725**;
* the near threshold 0.02734 gives 321,323.

321,400 matches `(0.027237 − 2^17/2^24)·16547000`, i.e. W/m was taken at m = 2^24 and m at m_min.
`cert_tail_W321400.out` fixes W = 321,400 in every m-cell, so it does not cover margins that shrink with m.

*Fix.* Certify T at ≤ 318,700 rows. Restate S3 as 0.027183 and the near threshold as 0.027345 (or define it
by the certified row count). Numerically harmless: `TAIL_X = 1.4395e-6` gives 0.985863.

**4. MEDIUM: the Lean band segments cannot represent the clipped segment the paper uses at F cuts.**
*Where:* `SegmentSort.lean` (`segNet`: length exactly 2^b, `o + 2^b ≤ m`; "clipped segments shifted to
[0, 2W)"); PROOFS L3 "What changed" item 3.

*What is wrong.* The paper's `Seg(i) = [i−W, i+W) ∩ [0, m) = [0, i+W)` at F₁|B₁ keeps the margin `d₀ − W`.
The Lean/implemented segment `[0, 2W)` reaches `2W − i ≈ 258k` rows above the cut. The cB mirror bound
(non-X keys below i ≤ `E⁻(top of segment)`) then has margin `d₀ − 2W + i ≈ 194k` rows at dB = 0.02734, not
321k. The box charges cB at `TAIL_X`, so it is unjustified at F cuts; the B₂|… cuts are fine. The same
applies at the top F₂ cut.

*Fix.* Either allow per-offset lengths ≤ 2^b in `segmentSort` (same depth bound), or recharge cB at the F cut
with T at about 194k rows. In both cases finding 2's term must use the actual segment top.

**5. MEDIUM: "cuts ≥ 2W apart" is unproved at spill senders and small blocks.**
*Where:* PROOFS L3 "Separator" ("interior blocks are about m/k"); `SegDisjoint` is a *hypothesis* of both Lean
theorems.

*What is wrong.* At spill senders, prefix children have b = 0 (coincident cuts), and the partially consumed
child's block can be anywhere in `(0, 2W)` rows. Segments of adjacent cuts then overlap. That breaks
disjointness and the centring L3a/L3b need.

*Fix.* Give a lemma on the minimum nonzero block size, or a rule that merges nearby cuts into one segment and
re-prices its depth and margins. Then discharge `SegDisjoint` in the node wiring.

**6. MEDIUM: route (d) coverage still has open cells (all floats).**
*Where:* ROUND1-ENERGY "Route (d) float coverage … complete except s29".
* `rd_nr2/s29.out` stops at `2.903e5 J`, but needs `3.2e5 J`. So `n ∈ [2^29, 2^30)`, `b ∈ [≈135, 150)` is
  currently uncovered (`coverB24` starts at b = 150).
* `b < 1e-6` in (B) rests on numerics plus the sketch.
* The f-ladder top `f_max = 1e7` needs a for-all-d lemma that every non-Batcher sender has
  `a/c ≥ 3968/1e7 ≈ 4e-4`. Currently it is checked only at d = 16 and 20 (`designP_sim`).

Otherwise the table has no hole:
* the A/B boundary uses C = 100 consistently in `coverA/coverB/coverB24/fullB/floor30`, overriding
  `rd_scaled.CJ = 800`;
* the sweeps' `100·J·ln(2n)` covers each NR = 2 interval;
* `coverB24` holds for every n ≥ 2^24 because ε uses `n_eff ≥ 2^24`.

**7. LOW: S2e/S3 case split omits "w₁ topRise at t−1"** (u newly at the top).
That case is generic-like: `G(w₁) = π_top(w₁)`, `G(w₁′) = π(w₁)/2`, so `dL ≈ π(w₁)/(2a) ≈ 0.031`. Add it
explicitly. §S2e should also note why a mid w₁ cannot be capped: by (I2), `G ≥ π(w₁′, t−2) ≫ θ`.

**8. LOW: §14 S1, "senders new at the top: `a ≤ Σπ_kid ≤ 0.96875c`" is wrong.**
The kids are topRise at t−1, so `Σπ = k·(ν/(Ak))·128c = c` exactly. That is still ≤ 1.01693. The botDesc
claim `R(u) = alloc + c/Q ≤ c` needs the (4,4,3) bottom-ratio table written out, as R1 does for (4,5,3).

**9. LOW: reserve audit (§15 end).**
"n per cut ≤ 1e-5 μc′" is off by about 100×: `n ≈ c/2^24 ≈ 1.0e-3·μc′` per cut, about 2e-3 per block.
* If this is the same n already inside γ (`paddedPack2Net_all_cut_bounds` has "+n" per cut), say so. γ must
  be re-derived for the band stage anyway.
* If it is separate, and outs_sub is separate, the total is about 0.011 > ROUND = 0.01. That is harmless:
  ROUND = 0.012 costs +0.002 on the ratio.
* L5 (far terms, about 1e-7 c) has silently left the reserve table. State that cH or Property B subsumes it,
  or keep it in.

**10. LOW: stale text.**
* The `transbox_analytic.py` docstring has S1 1.01595 / S2 0.1735 and a garbled T line; the code uses
  1.01693 / 0.2265 / `μ/2 + ε_B s_max/4`.
* §13's "0.027237" uses the old S1.
* ROUND1-ENERGY's "(B) as b → 0" table says C = 800.
* PROOFS line 268 says "both L3a and L3b are deterministic theorems in Lean". Only the upward (`false` at
  rows ≥ i) forms are. The mirrors (`true` at rows < i), used for cB and for downward escapes, are not
  stated.

## Checked and found correct

* **`transbox_analytic.py` vs §14/§15 formulas.** End `(μc′ + 2h + cB + cL)/2`, interior, spilled and T
  rules → `μ/2 + hw_p/2 + …`, `/4`, `kΔ₁/(8c)`, with c′ = 2c. The ratio is `hw/(2μ) + D + ε_B s/(2μ) +
  ROUND`, and D matches `δA²k(k/(2(1−(δkA)²)) + 1)/2 = 0.018432`. The complete-box max over senders is
  sound because inherit is monotone in (hw, s). Rerun: 0.985815, post-fixed point verified.
* **S1 telescoping.** `π_u(t−2) + G_u(t−2) + Σπ_kid(t−1)` with 0.03125 + 0.96875 + 64·2.6453e-4 = 1.016930.
  The g* fixed point is `16/65536 + μ/2 + ε_B/4 = 2.645e-4`. The design is `θ_first = π/2 + G_L + o`,
  `θ_last = π/2 + G_H − o`, interior 0.
* **S2.** The bound `8·(0.02734·1.01693 + g* + 16/65536) = 0.2265` holds. S2e's emptiness via invariant E and
  the capping lemma holds. The S3 generic algebra `dL·a ≥ π(w₁)/2 − o(w₁) − o(u)` holds.
* **cH margin.** `G(w_k′) = θ_last ≥ π(w₁)/2 − o(w₁)` is the same as S3. The joint bound `cL + cH ≤
  min(2T, ε_B/2)` is valid. It is even conservative, since `X_L ⊂ X_H` gives a single `T(margin_H − W)`.
  The top-grandchild crossings are self-cancelling: the matching downward crossers are w₁'s high outsiders
  and leave via F₂.
* **L3a/L3b proofs.** Row identity under σ2, segment locality, `B_j − W ≤ (c″_j − i)₊ + (i−W−L_j)`, and the
  sums equal to `E⁺(i+W)` and `E⁻(i−W)`.
* **Lean statements.**
  * `mergeBandPack2Net_low_crossings_le`: `false` = low set, rows from the bottom (columns Monotone). `F_j` =
    `false` count of column j of `semanticExec σ1 v`, the post-second-sort columns, i.e. c′. The hypotheses
    (`SegDisjoint`, fit, `h ≤ o` for segments reaching ≥ i) are satisfiable, so it is not vacuous.
  * `mergeBandPack2Net_escapes_le`: the bound is `Σ(F_j − (o+2^b))₊ + Σ(C_j − i)₊ + Σ(o − F_j)₊`, with
    `C_j` = band-stage-input column counts (c″). This matches L3b with `o = i − W`.
* **Route (d) n-interval conventions** (`route_d_rigorous_nr.py`): every direction is correct.
  * n_lo in `nlnG`, `A_coll` q and `n·ln(1+…)`, `k_bool`;
  * NR·n in `lbinom`, `ln n`, `u`, and the multiplicity n-factor, with the pmf shift
    `((1−p_lo)/(1−p_hi))^H`;
  * b at n_lo for top / L0 / d, and `b_lo = j_lo/(NR n)` for R;
  * `f_eff = max(3967, 8 j_a/(NR n))` and `jmax = f_max·NR·n/8`.
* **(B) cells** (`escapes_cell`): b_hi for λb, n₀ (decreasing in b), ε, d, L0 and the high-rows offset; b_lo
  for R; σ_hi for counts and σ_lo for credit. Centring at b_hi > j/n is valid, since `Σa(z − b_hi) ≤ Σa(z −
  b′)`. The mass cap `Σa² ≤ RΣa ≤ Rj` holds.
* **(A) Möbius sups** (`rd_sparse`): with `s(n) = s* + x/2`, `n(qe^s)²` is constant; with `t = t* + x`, the
  n-term is ≤ the n₀ value·`e^{x(1−c)}`. The sups are `max(v₀, 2RL_c)` and `max(v₀, L_c)`. `top =
  b₀ + √(2j) + 2` holds. Using `j_a` in `n₀ = e^{j_a/(100J)}` is conservative.
