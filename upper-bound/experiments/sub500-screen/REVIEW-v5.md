# Review of INDUCTION-v5 (centred sided invariant, spill rule, far-crossing lemma), 2026-10-22

Independent review (Claude Opus 5.5, fresh context). It covers what `REVIEW-centring.md` did not: the spill
rule, prefix sidedness (L4), the type-specific widths, the far-crossing lemma (L3), the sparse-node
accounting, and the §5 numbers.

My checks used instrumented **copies** of `centred_sim.py`, kept in scratch space and not in the repo:
* `csim_inst.py` records per-node crossing distances, prefix lengths and partial blocks;
* `hprop.py` propagates type-specific half-widths node by node through the exact SPILL=1 flow and tests
  (4.2-v5) at every sender, using that node's own η = a/c.

No repo file was modified.

## Verdict

**Confirmed with corrections.**
* **The bulk-margin claim survives.** In the doc's own form: 1.22 / 1.16 / 1.10. Node by node, with the
  true crossing distances: 1.29 at δ = 1e-6 and 1.18 at δ = 3e-6.
* **Three statements are wrong as written and must be repaired before this can back a proof:**
  * the crossing-distance quantity behind L3 (issue A);
  * the claim that the distance fails "only at spilling nodes" (issue B);
  * L4 / L1-exactness in the spill regime (issue C).
* **The band-repair variant of L3 is not automatic.** It holds only if the repair is a full sort of each
  band (issue D). Under the naive reduction, the band-repair package is infeasible for every W.

## 1. Spill rule (task 1): well defined, consistent; "no negative blocks" is vacuous (minor)

* **Run.** `SPILL=1 python -I centred_sim.py 4 4 3 10 14 18` reproduces `centred_sim_443_spill.out` exactly:
  * no `neg_block_min` entries;
  * spills only at botDesc, at t ≡ 3, 6, 9, 12 (mod 16);
  * `spill_a_over_c_max = 0.00758`;
  * up to 11 interior children spilled;
  * η ≤ 1.015792, and G/c ≤ 2.66e-4.
* **Bookkeeping is consistent.** Σθ = π + G (asserted), b = G_child − θ ≥ 0, and child G ← θ, as in
  Chvátal's flow table.
* **"No negative blocks" is guaranteed by construction, so it carries no evidence.** The cap θ_h ≤ G_{w_h}
  forces b ≥ 0. Feasibility is just π + G ≤ Σ G_child = a + G, which always holds. The real content of the
  rule is sidedness and the shift structure (§3 below).
* **The two prefixes never meet** at d ≤ 22: the longest are a low prefix of 9 and a high prefix of 7, out of 16.
* **Minor bug in `centred_sim.py`.** The child's sided split uses `thL = th[j] if j < len(seq)//2`. A low
  prefix of 9 crosses index 8, so one child per such node gets G_L = 0 instead of its low part. Replacing
  it with the low part only (my `FIXGL=1`) leaves every statistic and class count unchanged
  (1362 / 5408). So it has no effect, but the fix is one line.
* **The doc's design spec omits two cases:**
  * what happens if the prefixes meet (a child with both a low and a high part);
  * what type a **fully consumed** child (b = 0) has. It receives no block, so its next bag is only its
    children's F blocks, which makes it top-like. It is not in §3's type list.

## 2. Far-crossing distance (tasks 3, 4): the wrong quantity is measured (MAJOR, repairable)

**Issue A. `cross_margin_min` is not the L3 distance.**
* The simulation computes `(X1 − π/2)/a` with X1 = G(w_1) − G_L(u). Since b_1 = G(w_1) − θ_1, this equals
  `(b_1 + o)/a`, essentially the end child's **whole block**.
* The two end-child crossing terms involve range(w_1′), the grandchild range. Let
  `Y = G(w_1′) − G_L(u)` be the design count of range(w_1′) keys in u's bag. The two distances are:
  * **β side, F₁|B₁ cut, a non-range(w_1′) key goes up:** `dB = (Y − π/2)/a`;
  * **λ side, B₁|B₂ cut, a range(w_1′) key leaves upward:** `dL = (b_1 + π/2 − Y)/a`.
* Note `dB + dL ≈ χ_sim`.
* The doc's L3 and §3 also misplace the λ term. It is at the **B₁|B₂ cut**, not at F₁|B₁. At F₁|B₁, a
  range(w_1′) key going up is net 0, as `REVIEW-centring` §2 already says.

Measured (d = 18 and 22, steady state):

| sender | dB | dL | χ_sim |
|---|---:|---:|---:|
| mid | 0.0502 | **0.02605** | 0.0764 |
| topRise (t ≥ 3) | 0.0503–0.0513 | **0.02605–0.0265** | 0.077 |

* The binding distance is **0.02605, not 0.062.** `tail(0.026 m)` is therefore just adequate, by about 0.2%
  in distance. It is not "conservative": tail(0.02605 m) = 0.9402e-6 against 0.9420e-6.
* L3 must be restated with dB and dL, and the λ side must be covered at the B₁|B₂ cut.

**Issue B. Short distances occur at dense, non-spilling senders (MAJOR as a statement, numerically absorbed).**

`csim_inst.py` at d = 22 finds non-spilling senders with min(dB, dL) < 0.026. They recur with period 16:

| sender | t (mod 16) | a/c | dB | tail(dB·m) |
|---|---|---:|---:|---:|
| mid | 4 | 1.016 | **0.0072** | 3.77e-6 |
| mid | 7 | 1.016 | 0.0149 | 1.69e-6 |
| botDesc | 1 | 1.00 | **0.0034** | 9.3e-6 |
| botDesc | 14 | 0.50 | 0.0029 | |
| botDesc | 2, 5, 8, 12, 15 | 0.0076–0.12 | ≤ 0, down to −0.053 | case (a) |

Notes on these rows:
* The mid rows at t ≡ 4 are, for example, (t, i) = (20, 8) and (36, 14). In every row the end child
  becomes a botDesc sender next step.
* topRise also reaches 0.0037, but only at t = 1.
* dB ≤ 0 means u's F₁ already exhausts range(w_1′), so every F₁|B₁ crossing is short. The far-crossing
  lemma gives nothing there.

So §16's "the crossing distance fails only at the spilling nodes" is **false**.

**Pricing issue B.** The end children of these senders are sparse botDesc nodes (a/c ≈ 0.03–0.06), whose
(4.2) has room because their own ε_B η is small. `hprop.py` (d = 14) uses:
* per-node η;
* end child: `h_w = μ/2 + (2h_u + X_B + X_L)/(2Aν)`, with `X = min(tail(dist·m), ε_B/2)·η_u`, and case (a)
  `ε_B η_u/2` when dist ≤ 0 or at spill nodes;
* interior child: `h_w = μ/2 + λ_int/2`;
* top nodes and consumed children: h = μ/2.

Results (max ε_B; bulk d = 1.8966e-5):

| mode | δ = 1e-6 | δ = 3e-6 |
|---|---:|---:|
| doc's literal form (Aνφ′ per side, χ = 0.026 everywhere) | 2.327e-5 (**1.227**) | — |
| true per-node distances, physical units φ·η | 2.447e-5 (**1.290**) | 2.233e-5 (**1.177**) |
| sanity check: case (a) everywhere | 1.679e-5 (0.885; reproduces REVIEW-centring's 0.881) | — |

* The binding node is the mid sender at (t, i) = (20, 8) itself, with h = 3.01e-5. Its short-distance
  child does not bind.
* So issue B costs nothing **if** the proof is per node, with η_u, rather than one global
  `w̄/2 + ε_B η_max` inequality.
* The doc's global form needs an explicit bottom-boundary lemma: "end children of senders with
  dist < χ are sparse, and their (4.2) holds with their own η". It is not stated.
* Caveat: this propagation is my model at d = 14. Top width μ/2 and consumed-child width μ/2 are assumed,
  not derived (see issue E).

**Units in the end-child formula (minor, conservative).**
* Crossings φ·a_u give φη_u/(Aν) in child units. `(w/2 + Aνφ′)/(Aν)` overcounts by Aν/η ≈ 1.97.
* The algebra `w_end/2 = (μAν + 2Aνφ′)/(2(Aν − 1))` is correct for the doc's β and λ.
* The physical fixed point is `(μAν/2 + ηφ′)/(Aν − 1) = μ + ηφ′ = 3.049e-5`, against 3.142e-5.

## 3. Prefix sidedness L4 and "top boundary exact" (task 2): false in the spill regime (MEDIUM)

**Counterexample (d = 14; botDesc, t = 3, i = 3).** Values in units of c:
* a = 8.2e-4, π = 4.73e-4, G_L = 0, G_H = 1.571e-4, o = 2.95e-5;
* every child has G = 6.10e-5;
* low θ: children 1–4 full, child 5 gets 2.19e-5 (its b = 3.91e-5);
* high θ: children 12–16 full, **child 11 gets 5.89e-5, so b_11 = 2.1e-6**.

What goes wrong:
* The design shift at the interior boundaries is `s = N_L − o − ΣD`, with |s| up to h·c ≈ 3.1e-5 (≈ μc).
* If s > b_11, then F₂ takes up to s − b_11 ≈ 2.9e-5 keys of **range(w_10)**. Child 10 is interior, not in
  Pre_H, and has design G_H = 0.
* Symmetrically, at t = 19, i = 9 the low partial child has b = 1.8e-5 < 3.1e-5, so F₁ can overshoot into
  an interior child.

Where it happens:
* Partial blocks below 3.1e-5·c occur at spill nodes with a/c up to 0.0037. For example, at t = 22 and 25
  there is b_low = 2.3e-5 and b_high = 4e-6.
* At these nodes μc ≈ half of one child's deficit, so the "uniform shift" is not small against the
  prefix geometry.

Consequences:
* L4 ("every non-far ancestral key lies in Pre_L ∪ Pre_H") is false.
* L1's "top boundary B_k|F₂ is exact" is false whenever a high prefix exists. The top cut then sits at
  the partial child, where `up_{j′} = θ_{j′} − anc_{j′}` can be smaller than the N_H swing.

Why this is probably harmless, though it must be proved:
* Overshoot keys are own keys **pushed out** of a non-prefix child. Their number is at most |s|, which is
  exactly the term λ_int already charges (`w_par/2` over Aν), whether they go to a lateral block or to F.
* For the partial child, overshoot makes the inheritance identity over-count its own keys sent up. Its
  actual N_L then lies between the formula's value and 0, which is inside the interval.
* The misplaced ancestral keys are middle-of-range(u) keys, so the parent returns them inside B_u at
  t + 2, where the design counts them in u's bag (D = 0).

**Required:** restate L4 in **count form**: ancestral own keys of a non-prefix child are at most the keys
the shift pushes out of it. Drop "exact top boundary" for spill nodes. Add both to the Q step.

## 4. Far-crossing lemma reduction (task 4)

**Three-sort separator (sort, scramble, sort, scramble, sort): correct.** Proof sketch:
* Take ones = keys of rank > P + χa, so the total is ≤ n(i − χm) with i = P/n.
* After the last scramble and sort, `count(T) ≤ i + #{rows r ≥ i : the scrambled row-r entry in T is 1}`,
  because rows below i contribute at most i.
* Hence `Σ_T (count(T) − i)₊ ≤ Σ_j (c′_j − i)₊`, the round-1 ones above row i.
* By WALK-BOUND §2, that is ≤ `B − χm·s`, i.e. `tail(χm)·mn`, simultaneously for all c and i.
* So φ′ = one-round, one-direction tail. **No factor 2 is needed per side.**
* L3's "2·tail ≈ 1.9e-6 is conservative" contradicts §5's φ′ = 0.94e-6. With 1.9e-6 the margins would be
  1.12 / 1.06 / 1.01. Pick one; 0.94e-6 is justified.
* γ (partial rows) is separate, and RES_γ is listed but **priced at 0** in §5.

**Issue D. Band-repair variant (scramble, then band repair): MEDIUM.**
* The naive argument says a far key below the cut sat in round-1 row < i + W, so the margin is χm − W.
* At the band W the package needs (`d + 2 tail(W) ≤ ε_B` gives W ≈ 2^17.75–2^18), that margin gives
  φ′ = tail(0.026m − 2^18) = 2.5e-6 and ε_B ≈ 2.0e-5 < 2.22e-5 needed.
* **No W is feasible** under the naive argument (scanned 2^15 … 2^18.5).
* It **is** feasible (W ≥ 2^17.75) if the band repair fully sorts each band and the bands are disjoint.
  * A far key inside the band falls below the cut only if the band holds > Wn far keys, which is
    impossible given the round-1 tail.
  * Far keys outside the band have displacement ≥ χm + W.
  * The margin is then χm.
  * Bands of ±2^18 rows (±0.0156 m) are disjoint at the end child's two cuts, which are 0.076 m apart.
    They are **not** disjoint at sparse spill nodes, where blocks are ≈ 0, but there L3 is not used.
* **Required:** state L3 for the actual band-repair primitive and include the band-sort property.

## 5. Sparse-node accounting (task 5): legitimate, even free, but not the real issue

* The partial child of a spill node with case-(a) crossings gets `h = μ/2 + (2h_u + ε_B η_u)/(2Aν)`. With
  η_u ≤ 0.0076 this is `≤ μ + φ′ + 0.0019 ε_B`, below w_end/2 = μ + 2φ′, since 0.0019ε_B = 4e-8 < φ′.
* So it is dominated by the end type. RES_φ ≤ 0.004 ε_B is a harmless over-reservation.
* What Property B scaling does **not** cover is the shift overshoot (§3), which scales with μc and not with
  ε_B·a.

## 6. Widths and missing types (task 3)

* **Interior width: confirmed.**
  * N_L ∈ [−λ_int, μ], with `λ_int = (h_par + ε_Bη/2)/(Aν) + (k/2)μ sib/(Aν)`.
  * The upper side is P's cap; the review's minor term `+outs_sub ≤ Δ₁` is still omitted.
  * Hence `w_int/2 = μ/2 + λ_int/2`. My recomputation gives 2.580e-5, 2.590e-5 and 2.600e-5 at the three δ.
* **Chains: no problem.** An end child whose parent is interior, or chains of end children, are covered
  by `h_par ≤ w_end/2`.
* **Missing or under-specified types (issue E, minor or medium):**
  1. **top** (topRise/topDesc senders): §2 mentions o_top, but §3 gives no width. I assumed μ/2. The review
     said |s| ≤ μ with o = 0.
  2. **fully consumed prefix children** (b = 0, top-like).
  3. **the partial prefix child**: an interior-indexed end type with case-(a) crossings and possibly
     b ≪ |s| (§3).
  4. **end children of short-distance dense senders** (issue B).
  5. **children of topDesc**: B₁ takes O_L(u) uncentred. This is order-1 tiny but should be listed.

## 7. Numbers (task 6), exact rationals, (k, A, ν) = (16, 16, 1/8), q = 24

Inputs:
* μ = (1023/1024)·31/1048576 = 2.95350e-5;
* φ′ = tail(0.026·2^24) = 0.94204e-6;
* w_end/2 = μ + 2φ′ = 3.14191e-5;
* η = 1.0158;
* ROUND = μ/10, φ̄ = 1e-7, RES_φ = 0.004 ε_B, RES_γ = 0;
* d = 1.89659e-5.

| δ | max ε_B | margin | doc |
|---|---:|---:|---|
| 1e-6 | 2.3052e-5 | 1.2155 | 2.31e-5, 1.22 ✓ |
| 2e-6 | 2.1985e-5 | 1.1592 | 2.20e-5, 1.16 ✓ |
| 3e-6 | 2.0917e-5 | 1.1029 | 2.10e-5, 1.11 (rounding; 1.10) |

* Without φ̄ and RES_φ the margins are 1.225 / 1.169 / 1.112.
* The doc does not price RES_γ. Any γ reserve comes straight off ε_B: the margin falls by 0.053 per 1e-6.
* **The bulk margin claim follows** in the doc's form, and survives issues A and B in the per-node form
  (1.29 / 1.18).

## 8. Required before this can back a proof

1. **L3:** restate it with dB and dL (λ side at B₁|B₂), with the binding χ = 0.02605 (not 0.062). Fix
   `centred_sim.py` to report dB and dL. Fix φ′ = one tail per side.
2. **Bottom boundary:** add a lemma for dense senders with dist < χ (case (a) or a local tail). Either make
   (4.2) per node with η_u, or prove the short-distance children are sparse.
3. **L4 and L1:** use count form in the spill regime. Drop "exact top boundary" when a high prefix exists.
   Add types for consumed children, partial children and top nodes, with derived widths.
4. **Band repair:** state the band-sort property used, or price margin χm − W, which is infeasible.
5. Price RES_γ. Fix the one-line G_L split in `centred_sim.py`. Specify how the design treats prefixes that
   meet.
