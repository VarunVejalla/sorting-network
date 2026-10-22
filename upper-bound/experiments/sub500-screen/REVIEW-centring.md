# Review: centred shift identity and the joint induction for P and Q (2026-10-22)

Independent review (Claude Opus 5.5, fresh context). Scope: `CENTRED-SHIFT.md`,
`SIDED-CENTRED-INVARIANT.md`, `INDUCTION.md` (v4), `centred_shift_check.py`, `package_point.py`/`.out`.
Notation is INDUCTION's. "Mid" means a mid sender u with c = c_u. "End child" means w = w_1.
Range(w_1') is w's lowest grandchild range. Scratch numerics were done outside the repo.

## Verdict

**Confirmed with corrections. As a statement about the package at (16,16,1/8), it is refuted unless a
new crossing lemma is added.**
* The shift identity, the legitimacy of the centring, and the v4 end-child inheritance are correct.
* The width w̄ is **too optimistic when only Property B is available.** The end child's upper side
  omits a crossing term (issue 1). The corrected term is
  `w̄/2 = (μAν + ε_B η)/(2(Aν − 1))`, not `(μAν + ε_B η/2)/(2(Aν − 1))`.
* With that correction the package point is **infeasible for every δ**: the bulk margin is 0.881 at
  δ = 1e-6, 0.845 at 2e-6, and still about 0.92 at δ → 0.
* If a mid-range crossing lemma is proved (issue 1(b)), the documented term is conservative.

## 1. The shift identity (task 1): correct, with scope conditions

I re-derived it. Take an exact sort, with P_j = π/2 + Σ_{h<j} b_h and Q_j = O_L + Σ_{h<j} X_h. Then
`intruders(B_j) = min(b_j, s_j⁺) + (−s_{j+1})⁺`, with `s_j = Q_j − P_j`.

**Ends.**
* `s_1 = O_L − π/2 ≤ 0`, so B_1 has no lower intruders.
* `s_{k+1} = π/2 − O_R ≥ 0`, because b_k is "the rest" (a = O_L + ΣX + O_R). So B_k has no upper intruders.
* **The top boundary is exact** in this sense. O_R and D_k never reach any block; they only change
  how many of w_k's top keys go up.

**Interior boundaries.** `s_{j+1} = N_L − o − Σ_{1<h≤j} D_h` (minus the Δ offsets), as claimed.

**Both-sided outsiders are fine.** O_R cancels exactly. A useful consequence the notes do not state is
**conservation**:

    N_L + N_H = (a − Σ X̂) + Σ_{1<h<k} D_h.

So N_H is not an independent quantity. Only the N_L interval matters, and asymmetric centring (o on the
low side, b_k = rest) is sound.

**Scope conditions.**
* **O_L > π/2** is excluded at every sender with π > 0, by (4.4) (μc ≤ δ_F π/2) and by (4.3) for topRise.
* **topDesc (π = 0)** breaks the identity: B_1 gets O_L and B_k gets O_R directly, which is Chvátal's
  O_L + O_R. This is harmless only because a top node's bag is its children's F blocks. Its outsiders
  are therefore order ≥ 1 at the children, at most `kμδ(A/ν)c ≈ 0.004μc`.

**Separators.** Property B at arbitrary cut positions gives `≤ s_j⁺ + (−s_{j+1})⁺ + ε_B a`. This is
right. F-escapes of u's outsiders are B-crossings at the π/2 cut.

**Deficit/θ bookkeeping.** The flows are consistent:
* `θ_1 = Ĝ_L(u) + π/2 − o`;
* `θ_k = π/2 + Ĝ_H(u) + o + (k−2)Δ₁/2`;
* Σθ = π + G.

But sib centring makes the interior `θ_h = G_h − b_h = −Δ₁/2 < 0`. That violates R1's table convention
(θ ≥ 0). It is numerically harmless (W_h > R_h just matches the subtree's deep outsiders), but
(I1)–(I3) and Lemma 3.1′ must be re-stated for negative θ. **Minor.**

`centred_shift_check.py` verifies only the arithmetic identity with exact X and no crossings, no D_1 and
no deep keys. That is the trivial part, and it does not test the induction.

## 2. Step lemma for Q (task 2)

**Cancellation (§4): the conclusion is right, but the argument is wrong as stated (minor).**

The text says each child's F block is "outsiders first, then own extremes", so outsiders and own keys
trade one for one. That fails for order-0 strangers *between w's children*:
* F2(w_1′) carries O_R(w_1′) keys of range(w_2′);
* O_R(w_1′) can be up to `μ c(i+2,t) = 128 μ c_w`, which is far above w's scale;
* the compensating keys arrive through F1(w_2′) (as O_L(w_2′)), so the cancellation is not slot by slot.

The correct argument is wire conservation at t+1:

    X_1(w) = G_{w_1'}(t+1) + outs_sub(w_1') − Out_{w_1'}(t+1).

Here Out counts the range(w_1′) keys outside w ∪ subtree(w_1′). w's children are empty at t+1, so
these keys are above w, outside subtree(w), or **deep** (order ≥ 1 at level i+3). The large
inter-child terms then cancel identically. The doc should replace §4's cancellation paragraph with this.

**End child (v4): confirmed.** Tracking Out from t to t+1:

    Out_{w_1'}(t+1) = Out_w(t) + (π/2 − O_L(u)) + (crossings),
    Out_w(t) = G_w(t) + outs_sub(w)(t) − X̂_1(u) + D_1(u).

With the design `X̂_1(w) := G_{w_1'}(t+1) − Ĝ_L(w)` and `Ĝ_L(w) := Ĝ_L(u) + π_u/2 − o_u` (= θ_1), this gives

    N_L(w_1) = O_L(w_1) + (N_L(u) − o) + [crossings] + [deep terms],

which is exactly v4. **X̂ is never defined in the notes.** The recursion for Ĝ_L above must be written
into §2 (medium: without it, "midpoint" and "design count" have no referent).

**Grandparents, topRise/topDesc oscillation, lateral cousins, and the parent's split: no missed terms.**
* Everything that happened before t is inside N_L(u) by induction, because Out_w(t) enters only through
  D_1(u).
* Keys moved by gp at t (down to p, up, or laterally to p's siblings) stay inside Out, and the count is
  unchanged.
* The deficit split is pure for every role: end children are all low or all high, and top nodes have G = 0.
  Deviations show up only in N_H, which never reaches a block.

**Issue 1 (MAJOR, conditional): crossings on the end child's upper side are omitted.**

Content of B_1 in u (mid sender):
* first, about Y − π/2 range(w_1′) keys, where Y ≈ π_w(t−1)/2 ≈ 64pc ≈ 0.026c, from w's F1 plus
  ancestral keys;
* then about 0.03c range(w_k′) keys from w's F2. Interior range(w_h′) keys are essentially absent.

Crossings at each cut:
* **F1|B_1 cut, a range(w_1′) key goes up.** The key that comes down has rank ≤ π/2 (a low outsider or a
  range(w_1′) key). This is net 0 for N_L(w), so §4's "crossings at w's lower cut" term is not where
  the ε goes.
* **F1|B_1 cut, a non-range(w_1′) key goes up.** Example: B_1 = {a5..a10, z1..z10} by design, with
  π/2 = 4. The separator outputs F1 = {a1, a2, a3, z10} and B_1 = {a4..a10, z1..z9}: one crossing,
  allowed by B at threshold 4. w keeps one extra range(w_1′) key, so D_1(w) = −1 and
  `N_L(w) = O_L(w) + s_u + 1`. The extra key is own, not an outsider, so P's cap on O_L(w) does not
  contain it. Up to `ε_B a/2` such exchanges are allowed, with O_L(w) independently at its cap.
* **B_1|B_2 cut.** Range(w_1′) keys leaving upward give the lower-side term (−ε_B a/2). The notes list
  this term, but under the wrong name.

Both events are rank displacements of about 0.026–0.03c, roughly half a child range. So neither is
covered by φ̄ as defined ("more than one child-range away", interior ranges only). Two cases follow.

**(a) Property B only.**

    β_end = (w̄/2 + ε_Bη/2)/(Aν),   λ_end = (w̄/2 + ε_Bη/2)/(Aν),
    w̄/2 = (μAν + ε_B η)/(2(Aν − 1))     (Aν = 2: μ + ε_Bη/2, not μ + ε_Bη/4).

**(b) With a proved mid-range crossing bound** (keys displaced ≥ Y − π/2 are at most φ̄′ a): both
end-child ε terms drop out, and

    w̄/2 = (μAν + 2Aν φ̄′)/(2(Aν − 1)).

This is better than the documented term.

* At mid senders the distance is Y − π/2 ≈ 56·(π/2).
* Near the bottom (small R/c), Y can be small, so φ̄′ would have to be certified role by role.
* Interior children are unaffected: their own low keys leave B_h downward near the cut (ε_B a/2, already
  counted) or upward about b_h away (far).

**Issue 2 (MEDIUM): Δ terms are two-sided, and the stated sib offsets centre the wrong interval.**
* Under P, deep outsiders in subtree(w_h) can be keys of another child's range, which makes D_{h′} > 0
  ("deep-lateral").
* Counted per key, `−Σ_{1<h<j} D_h ∈ [−(k−j+2)Δ₁, (j−2)Δ₁]`, which is not `[0, (j−1)Δ₁]`.
* With the stated offset (j−1)Δ₁/2, the worst case at j = 2 is about `(k + ½)Δ₁`, about twice the
  claimed `(k−1)Δ₁/2`.
* The optimal per-boundary midpoint `((j−2) − (k−j+2))Δ₁/2` gives `kΔ₁/2`, which is negligible
  (0.881 → 0.879 below).
* D_1's deep-lateral part must also move out of N_L into this Δ part. It cancels in the end-child
  inheritance (the `Lat_w(t)` term), so it does not propagate.
* The interior children's λ should include `+(k/2)μ sib/(Aν)`. The end-child width still dominates
  (w̄/2 ≈ μ ≫ that term), so w̄ is unaffected **provided o is the midpoint for each node type.** One
  uniform λ, as written in Q(a), is wrong for interior nodes.

**Minor.**
* Q(a)'s upper side omits `+outs_sub(w_1′) ≤ Δ₁(w)`, which is excess own keys.
* topDesc children have `N_H ≈ −O_L(u) ≠ 0`, so the table's "λ = 0" is false. It is harmless (tiny).
* The Δ-related deep terms in O_L(w) from w's children are `≤ kμδ(A/ν)c_w` (this is the μδA²k term). Fine.

## 3. Legitimacy of centring (task 3): legitimate

* o depends only on the node type, side and capacity, all of which are design data.
* The intervals are derived from worst-case P, Property B and conservation, so they hold for every input,
  modulo issues 1–2 and the unproved far/sidedness lemmas.
* Signs are consistent in INDUCTION: s > 0 means B_j receives from below, and N_L > o gives s > 0.
* CENTRED-SHIFT's early sections mix `o′ = −o` with "[−U, 0]". They are superseded and should be marked so.
* Q(a) is genuinely two-sided, and the midpoint must be **type-specific**:
  * end-low children: `[−λ_end, μ + β_end]`;
  * others: `[−λ_int, μ]`.

**Sidedness (open, medium).** The derivation needs two facts:
* `Out_w(t) ⊂ range(w_1′)`;
* u's F1 own keys are range(w_1′), i.e. `Y ≥ π/2 − O_L(u)`.

At mid senders this holds by size (Y ≈ 0.026c against π/2 ≈ 2.4e-4c). It needs a written lemma per role,
especially botDesc and the sparse bottom levels at (4,4,3), where the bottom ratios R/c have not been
computed.

## 4. Roles and design invariants (task 4)

**Roles.**
* **topDesc and topRise:** fine. A top node's bag is its children's F blocks, so its N_L is order-1
  small, and with o = 0, |s| ≤ μ ≤ w̄/2 at Aν = 2.
* **botDesc and botRise:** fine via conservation. botRise children's N_L is never used.

**(I1)** `g* = (p/2 + w̄/2)/(Aν − 1) = 2.94e-4` reproduces. It uses `|o| ≤ w̄c/2`, which is
conservative (o ≈ μc/2).

**(I2)**
* `package_point.out` prints `θ ≤ (p/2 + g*)c`, but the high end is `θ_k = π/2 + G + o`. The correct
  bound is `(p/2 + g* + w̄/2)c ≈ 5.9e-4 c`, still well below `0.061 c`.
* The botDesc case (needs R_x/k > θ) and the separator geometry (the m window and fringe classes) are
  **not checked at (4,4,3).** R1 checked them only at (4,5,3).

**(I3)** `η = p(1/ν² + kA/ν) + g*/ν² = 1.0178` reproduces. topRise gives exactly 1 here
(`pkA/ν + 1/(νAk) = 1`).

**package_point.py**
* It matches (4.2-c), except that γ̂Aν and ROUND share one 0.1μ reserve while INDUCTION lists them
  separately.
* φ̄ = 0 is assumed. With φ̄ = 1e-7, the margin at δ = 2e-6 drops from 1.016 to 1.004.

## 5. Corrected budget (task 5)

Exact rationals, same point and conventions as `package_point.py` (bulk d = 1.8966e-5). The margin is
the allowed ε_B divided by d.

| term in (4.2-c) | η | margin δ=1e-6 | margin δ=2e-6 |
|---|---|---:|---:|
| doc v4: `(μAν + ε_Bη/2)/(2(Aν−1))` | 1.0180 | 1.059 | 1.016 |
| (a) B only: `(μAν + ε_Bη)/(2(Aν−1))` | 1.0199 | **0.881** | **0.845** |
| (a) + sib kΔ₁/2 (issue 2, centred correctly) | 1.0199 | 0.879 | 0.841 |
| (a) + sib + φ̄ = 1e-7 | 1.0199 | 0.868 | 0.831 |
| (b) mid-range lemma, φ̄′ = 0: `μAν/(2(Aν−1))` | 1.018 | ≈ 1.32 | ≈ 1.27 |

Under (a), even δ → 0 gives at most `ε_B ≤ 0.9μ/(1.5η) = 1.74e-5 < 1.897e-5`. **The package point is
infeasible.**

**Answer to task 5.** Replacing `μ + r*` by a centred w̄/2 is correct in mechanism, but the stated
w̄/2 is **too optimistic by `ε_Bη/(4(Aν−1))`** unless the end-child crossings are bounded more sharply.
* The best term I can justify from P, B and conservation is `w̄/2 = (μAν + ε_B η)/(2(Aν−1))`, plus
  `kΔ₁/2` for the sib term and the far terms.
* With a mid-range crossing lemma, the documented term is safe, and even improvable.

## 6. Remark: the μ floor looks removable (not verified to proof level)

w's bag at t+1 is exactly `B_w(t)` plus its children's F blocks; nodes empty on activity. So, dynamically:
* `O_L(w) ≤ s_u⁺ + ε_B a/2 + kμδ(A/ν)c_w + far`;
* the end child has `O_L(w_1) ≈ crossings only`.

Using this in place of P's cap (§9's "refinement") makes every child's interval about symmetric:
`|N_L(child)| ≤ (|s_u| + ε_B a/2 + Δ-part)/(Aν c)`. The fixed point is then roughly

    w̄/2 ≈ (ε_B η + k μ sib + Aν·μδA²k-type)/(2(Aν − 1)),

with no μ term. This is consistent with SLACKFREE's observation that D2 has zero outsiders under exact
sorting. At Aν = 2, with ε_Bη/2 from the shift plus ε_Bη per block, this would allow
`ε_B ≲ (2μ − 0.14μ)/(1.5η)`, i.e. about 3.6e-5. That is a far
larger lever than the 1–2% margins discussed. It is worth a careful write-up; P's cap is still needed
for (4.4) and support.

## 7. Required before this can back a proof

1. **Decide issue 1:** either price case (a), which fails at (16,16,1/8), or state and certify a
   crossing-distance lemma at displacement about `Y − π/2`, per role.
2. Define X̂ and Ĝ_L in §2. Use type-specific midpoints and correct Δ midpoints, and re-state
   (I1)–(I3) for negative interior θ.
3. Rewrite the §4 cancellation via the conservation identity, and add the deep (Δ) terms.
4. Write a sidedness lemma, and check the bottom ratios and geometry at (4,4,3).
5. Certify φ̄, and use separate reserves for ROUND and γ.
