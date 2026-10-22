# Review of INDUCTION-v6, PROOFS-L3-L4 and width_sim.py (2026-10-22)

Independent review (Claude Opus 5.5, fresh context). No repo file was modified. My checks used patched
**copies** of `width_sim.py` in scratch space (runs at d = 14 and 18 only, one process at a time):
* `wsim_inst.py` records topDesc ratios, a/c_child, h/(μc′), and the "true" crossing distance;
* `wsim_y.py` adds `YMODE` = `code` | `true` | `pre`, which selects how Y is computed;
* `wsim_side.py` records which side the spilled children's ancestral keys are on.

Unless stated otherwise, every run uses ROUNDF = 0.01, δ = 1e-6 and (4,4,3).

## Verdict

**The architecture is sound in outline. The two headline numbers are not supported as written.**
* The per-node certificate is the right replacement for the global (4.2), and the type rules match
  REVIEW-v5's derivations.
* **477 is refuted at the model level.** `width_sim.py` computes the end-child count Y off by the child's
  design offset o_w (issue 1). With Y corrected, the 477 point fails: ratio **1.0019 / 1.0037** at
  d = 14 / 18. It also has zero band-room slack (issue 3).
* **490 "with 1.9% slack" was priced with the wrong band** (issue 2). With the band that depth 190
  actually buys under `screen.band` (2W = 2^19), the ratio is **1.08**.
* A corrected 490 variant survives at the model level with about **1% slack** at d = 18. Its band is
  2W ≈ 2^18.2 rows, which is not a power of two but still has depth S(19) = 190. It also needs
  per-type midpoints and an m-window at least 2^23.95 (issues 3 and 4). That 1% must still absorb
  d-growth, φ̄ in the widths, and γ.

## Issues

**1. (MAJOR) Wrong Y in the certificate's crossing distances.**
* `width_sim.py` uses `Y = first.GL − G_L(u)`, i.e. G_L(w). But the count of range(w_1′) keys in u's
  bag is `G(w_1′) − G_L(u)`, as REVIEW-v5 defines it. Since `G(w_1′) = θ_first(w) = G_L(w) + o_w`, the
  code's Y is too small by o_w.
* With o_w = μc_w, this is negligible at dense end children. It is not negligible when the end child is
  a sparse botDesc node, whose capacity far exceeds its content:
  * debug node t = 9, i = 3: o_w/a_u = 0.0037;
  * so dL_min = **0.02605**, REVIEW-v5's binding number, and not the 0.029774 printed in v6's outputs;
  * mid dB also drops to 0.0072 (REVIEW-v5 issue B reappears).
* The error is non-conservative on the λ side, and it is decisive at 477:

| run (EPSB, 2W/m) | code Y, d = 14 / 18 | true Y, d = 14 / 18 |
|---|---:|---:|
| 2.6e-5, 0.015625 | 0.9953 / 0.9970 | **1.0019 / 1.0037** |
| 2.6e-5, no band | 0.9851 / 0.9868 | 0.9859 / 0.9880 |

* A prefix-aware Y (the top of w's whole low prefix, `YMODE=pre`) gives the same binding values.
* With OFRAC = 0 the code Y and the true Y coincide (dist 0.0298), which confirms the diagnosis. **Y
  therefore depends on the midpoint convention** (issue 4).

**2. (MAJOR) The 490 row of §7 used a band that does not match its depth.**
* `screen.band(24, ·, 2.5e-5)` returns 190 = S(19). That means W = 2^18 and 2W = 2^19 = 0.03125 m, which
  is wider than every end-child distance. Yet §7 ran it with `BAND2W_FRAC = 0.015625`, the 2^18 band of
  the 477 row.
* With the matching band I get 1.0678 / 1.0797 (code Y, d = 14 / 18): **infeasible**.
* **Rescue.** A non-power-of-two band 2W = 2^18.2 rows (0.0179 m) has the same Batcher depth S(19) = 190.
  It needs `bulk + 2·tail(2^17.2) = 2.486e-5 ≤ ε_B`. At ε_B = 2.5e-5, d = 18, true Y:
  * 0.9934 with the code's o = μc;
  * 0.9870 with o = μc/2.
* The band-repair primitive must allow arbitrary band heights (check the UB-32 Lean `blockSort b`).

**3. (MAJOR, unaddressed) The row window.**
* Bulk and tail are evaluated at m = 2^24 exactly (1.897e-5). §17's geometry admits m ∈ [2^23.506, 2^24).
  At 2^23.5 the bulk is 2.456e-5, so the band room at ε_B = 2.5e-5 is 4.4e-7 (2W/m ≈ 0.31). The package
  is then **infeasible**.
* R1 certified d ≤ ε_B over its whole window. v6 must do the same. Required lower ends:

| ε_B | band | required lower end of the window |
|---|---|---|
| 2.6e-5 | 171 (2W = 2^18) | m = 2^24 exactly. The room `2.6e-5 − 1.897e-5 − 6.88e-6 = 1.5e-7` is gone by m = 2^23.98 (bulk 1.916e-5). **477 is infeasible for any realistic window.** |
| 2.5e-5 | 2W ≈ 2^18.3 (0.0185 m) | m_min ≥ 2^23.98. Corrected ratio 0.9934 (o = μc) / 0.9895 (o = μc/2) at d = 18. |
| 2.5e-5 | 2W ≈ 2^18.3 (0.0196 m) | m_min = 2^23.95. Ratio 1.0034 / 0.9938. |

* Pinning every block-sending sender within 2^-0.05 of 2^24 needs either:
  * many fringe classes, each certified at J = 5e5;
  * or a free choice of n with a fringe certificate for every f in a range.
* The tail must also be evaluated at m_min, where it is larger (×1.4 at 2^23.5).

**4. (MEDIUM) Midpoints are not implemented.**
* The certificate assumes `|N_L − o_T| ≤ h` with o_T the midpoint of the class's interval. The code
  instead uses one constant, o = OFRAC·c = μAν/(2(Aν−1))·c = **μc**, for every role. That value is the v4
  *half-width*, not a midpoint. The derived midpoints are:
  * end child: (μc′ + c_B − c_L)/2 ≈ μc′/2;
  * interior child: (μc′ − λ_int)/2;
  * children of topDesc, and top nodes: ≈ 0.
* Taken literally, a top node with h ≈ 0 but o = μc would shift every interior boundary by μc. That
  would add about 0.5 to its ratio.
* "A midpoint is input-independent because each width is" is true, but the certificate must track
  interval **endpoints** per class and feed o = midpoint into the flow.
* Numerically the flow is insensitive: OFRAC = 0 moves the ratios by ≤ 0.1%. Y is not insensitive
  (issue 1). Use the true-Y and o = midpoint combination when re-running.

**5. (MEDIUM) L4 as stated ("Anc_L(u) is a lowest segment") is false at spill senders.**
* PROOFS step 1 needs the low range(u) keys in u's bag to supply F₁, i.e. `Y ≥ π/2 − O_L` (dB ≥ 0). At
  spill senders dB goes down to −0.70.
* There, a fully consumed child w_h (θ_h = G_h) sends up **both** its F₁ keys (lowest) and its F₂ keys
  (highest). Its middle keys stay in subtree(w_h), so Anc_L(u) has holes.
* The code's split (`thL = th if j < len//2`) then assigns the whole θ to one side. The physical
  wrong-side mass is up to **2.07 μc′** (consumed children) and **4.13 μc′** (partial children)
  (`wsim_side.py`).
* At such a child's next send this would be a design error of order π_w, far beyond h. It is harmless
  only because **every spilled interior child is botRise at t+1** (no blocks; verified at d ≤ 18).
* **Required:**
  * a schedule lemma, for all d, that spills occur only where children are next botRise;
  * restate L4 per child range: "for each child h, the count of range(w_h) keys above u is θ_h ± X",
    which is all the shift identity uses.
* Step 2 (the parent's block) is correct for end-low u. With separators, p's swaps inside range(u)'s
  low segment create holes, at most ε_B a_p/2 per send. These are net 0 for every count that the per-child
  form uses, so the per-child form avoids an accumulation question that the "lowest segment" form raises.
* Steps 3 (lateral keys) and the top oscillation (G = 0, topDesc returns everything) are fine.
* Meeting prefixes are never observed (low 9 + high 7 of 16). The code should assert this rather than
  rely on "charged as spill", which is not implemented.

**6. (MEDIUM) The ROUND = 0.01 μc′ reserve is under-justified.**
* γ at a mid sender: n = π/(2(f+1)) = p·c/7936, so `γ ≤ 3n = 8.9e-8 c′ = 0.0030 μc′`. That is not
  "about 0.0004μ".
* `2φ̄ = 2e-7 c_u = 0.0034 μc′`, and the far term L5 is an uncertified energy-method model.
* Also missing:
  * φ̄ in the width recursion (INDUCTION Q(a) has it in λ);
  * outs_sub ≤ Δ₁ on the end-child upper side;
  * the topDesc children's deep term (≈ 0.004 μ c_u).
* The total (≈ 0.007–0.009) fits under 0.01, but with almost no room. The former reserve was
  0.1μ c_u = 0.05 μc′.

**7. (MEDIUM) Coverage of the certificate.**
* topDesc sends (t ≥ 1) are **not checked** in `send()`. I measured max ε_B a/(μc′) = 0.447 there
  (a/c′ ≤ 0.508); add the check.
* t = 0 is not checked either. Its ratio is exactly 1.0000 with ε_* = μ/k, leaving no room for γ or
  rounding. Take ε_* strictly smaller, which costs O(1) depth.
* The ratio rises with d at every setting I ran (d = 14 → 18: +0.0017 to +0.0034). "Converging just
  above 1" at 2.68e-5 is consistent with that, but no bound for all d exists.
* Hash-consing and the upward quantisation (1e-7 relative to h ≈ 3e-5) are sound.

**Minor.**
* The doc says the tail is used for d ≥ 0.02; the code uses `dist − 2W/m ≥ 0.005`. This is valid only
  because tail(0.005 m) = 5.8e-6 < ε_B/2. Write `min(tail, ε_B/2)`.
* The `.out` files do not record EPSB, BAND2W_FRAC, ROUNDF, DELTA or OFRAC. The script default is
  ROUNDF = 0.1, not 0.01.
* At spill senders the end children get hw_end with a tail on one side, not the table's spill width.
  This is moot, since they are botRise next.
* REVIEW-v5's one-line G_L split bug was copied into `width_sim.py`.
* PROOFS L3 step 4 is internally inconsistent: "2W ≈ 2^18.4", a margin of 1.0e5 rows, "W ≤ dB·m/4 costs
  a factor 2", and dL ≥ 0.026 (true) used together with §7's 2W/m = 0.0156 subtraction (see Q4).

## Answers to the tasks

**Q1 (type rules vs REVIEW-v5 A–E).**
* All four formulas reproduce REVIEW-v5 §2/§6 and hprop: end, interior, spill, and h_w = μ/2 + (…)/(2Aν)
  in child units.
* Item A (dB/dL at the right cuts, one tail per side), item B (per node), item D (disjoint full band
  sorts) and item E (types listed) are implemented.
* Item C (count form) is stated in INDUCTION but not proved, and the PROOFS sketch argues the false
  segment form (issue 5).
* The implementation of A has the Y offset error (issue 1). Midpoints are missing (issue 4).
* **topDesc.**
  * R1 (4.1) is the t = 0 root separator only. R1's large topDesc senders at t ≥ 1 use ordinary
    Property B with ε_B.
  * In the run, "a > c_child" holds **only at t = 0** (a/c′ = 16 = k). At t ≥ 1 the maximum is 0.508,
    so ε_B is used there and gives ratio ≤ 0.447.
  * The criterion is therefore harmless, but the wrong one. It should read "t = 0 (root separator,
    ε_* < μ/k)". If a > c′ ever occurred at t ≥ 1, (4.1) would not apply, and that separator (m = 2^79)
    is affordable only for O(1) stages.

**Q2 (soundness of the per-node certificate).**
* Sound, provided all of the following hold:
  * (i) the type rules are proven input-independent bounds on |N_L − o_class|;
  * (ii) the flow uses those o_class;
  * (iii) every send is checked, including topDesc and t = 0;
  * (iv) for every d;
  * (v) in exact arithmetic;
  * (vi) with crossing distances computed from the correct Y and at the node's actual m.
* `intr = h + kΔ₁/2 + μδA²k c + ε_B a + ROUND·μc′ ≤ μc′` is the right order-0 condition at the child:
  * it is R1 (4.2′) with μ + r* replaced by h, and (k−1)μ sib replaced by the centred kΔ₁/2;
  * the end-child own-key crossings (c_B, c_L) correctly enter only the next generation's widths, not
    P;
  * h is per class, and c′ = cap(i+1, t+1) is the child's capacity at its next send. Both are correct.
* Of (i)–(vi), only the per-class h and the condition itself are currently right. (ii), (iii) and (vi)
  fail as coded, and (iv) and (v) are open.

**Q3 (L4).** See issue 5.
* **Counterexample** to the segment claim: any spill sender with a fully consumed interior child that
  had G = π_w, i.e. halves from its F₁ and F₂. All such children are botRise next.
* Step 2 is fine for end children.
* Separator holes are counted, but under the segment form they need an argument that they do not
  accumulate. The per-child count form needs none.

**Q4 (L3).**
* **Three-sort reduction: correct.**
  * Crossers at F₁|B₁ are the ones (rank ≥ Y) below row i, where the ones' level is dB·m rows above.
  * The last-scramble argument of REVIEW-v5 §4 reduces this to the round-1 excess beyond the margin dB·m.
    PROOFS step 3's band-adversary detour is unnecessary.
  * Ignoring O_L in the threshold is conservative.
* **Band repair (tiling, disjoint, fully sorted bands of 2W rows).**
  * A crosser must sit, before the repair, in the cut's band, i.e. at a row < i + 2W.
  * Rows are preserved by the scramble, so the count is at most the round-2 excess beyond (dm − 2W).
    That is at most the round-1 tail at dm − 2W.
  * **The margin dm − 2W is right and conservative.** REVIEW-v5's sharper "margin dm" needs bands centred
    on the cut, which a tiling does not give.
  * Use the correct dL = 0.02605, not 0.0298.
* **Status of the tail.**
  * The margin version is a direct corollary of WALK-BOUND §3: subtract W·s deterministically. It is the
    same failure event, so it needs no new union.
  * It rests on a hand proof with one review (Freedman, slice McDiarmid), and the corollary is not
    written down.
  * `screen.tail_frac` is a float grid evaluation with the pre-review constants:
    * Lipschitz 2, conservative ×2 in the concentration term;
    * it omits the rigorous +2/3-per-column mean term (2/(3m) ≈ 4e-8, about 5% of the tail at the
      binding margin), which the Lipschitz factor likely absorbs;
    * it omits ln(2n/η)/n (negligible at n ≥ 2^19);
    * it is evaluated at m = 2^24 rather than at the node's m.
  * Verdict: **an established bound modulo a short written corollary and a rigorous evaluation**, not a
    mere model.

**Q5 (package).**
* **477: not supported** (issues 1 and 3).
* **490 "1.9% slack": not supported as stated** (issue 2).
* A corrected 490 is plausible at the model level, with the following inputs and margin:
  * ε_B = 2.5e-5;
  * 2W ≈ 2^18.2–2^18.3 (depth 190);
  * m ≥ 2^23.98 at every block sender;
  * o = midpoint, true Y;
  * ratio ≈ 0.990 at d = 18, i.e. ~1% slack;
  * to be absorbed from that ~1%: about +0.2% of d-growth, φ̄ in the widths, γ = 0.003, rounding, and
    whatever the true per-class midpoints change in Y.
* **Remaining unproved:**
  1. L4 in per-child count form, plus the botRise-after-spill schedule lemma for all d.
  2. L3: the written margin corollary of WALK-BOUND §3; a rigorous tail evaluation at each node's m; the
     band-repair displacement lemma for tiling bands of non-power-of-two height.
  3. L5 / φ̄ (energy method) at the actual margins, and its inclusion in the widths.
  4. The certificate:
     * per-class endpoints and midpoints;
     * corrected Y;
     * topDesc and t = 0 checks;
     * the actual per-node m;
     * exact or interval arithmetic;
     * a proof that it holds for all d (periodicity in t mod 16; the ratios currently increase with d).
  5. Geometry: a fringe-class assignment with m ∈ [2^23.98, 2^24) at every block sender, with a fringe
     certificate (route (d), J = 5e5) for every class used.
  6. Band repair in Lean with arbitrary b (UB-32), merge-first in the node spec, and the fringe n → ∞
     argument.
  7. Higher-order P, (4.3)–(4.5) at δ = 1e-6, and the sidedness conditions at the topRise/topDesc
     transitions (fine by inspection; not written).
