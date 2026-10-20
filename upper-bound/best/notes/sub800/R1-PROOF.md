# R1 at (16, 32, 1/8): proof of D(n) ≤ 789.75·lg n + O(1)

Claude (Opus 5.5), 2026-10-19. This is a hand proof. It modifies Chvátal, DCS-TR-294 §3–4: page
numbers below are printed pages, and §5–6 are the separator chapters. The numbers it needs come from
`r1_point.py` (exact rationals), `designP_sim.py` (exact simulation), the fringe certificates
`fringe_cert_R1_f*.out` (interval arithmetic) and `../../../experiments/walk-bound/ROUND2.md` (bulk; float
certified by `cert_walk.py`). **Reviewed twice in fresh contexts (2026-10-19).** The second review found no
blocking issue and judged the proof complete at the paper level, modulo the single-review
dependencies listed at the end; its should-fix items are applied. Nothing here is in Lean beyond
`../../AKS/Sub800/NegAssoc.lean` (LEAN-PLAN W4.3).

Parameters: k = 2^4, A = 2^5, ν = 2^-3, so Aν = 4 and Aνk = 64. N = k^d, and Chvátal's capacities
are c(i,t) = N·A^i·ν^t/(Aνk). The constants are:

| constant | value |
|---|---|
| μ | (1 − 2^-10)·μ₄₄, μ₄₄ = ½δ_F(Aνk−1)/(A²k²) = 63/4194304 |
| δ | 135/10^8 |
| ε_B | 1/105,000 |
| J = 1/ε_F | 190,000 |
| δ_F | 1/8 |
| r* | (k−1)/(2A²k²) = 15/524288 |
| g* | k·r*/(k−1) = 1/(2A²k) = 2^-15 |
| η | 1 + 7/4096 |

## 0. What changes, and what does not

Chvátal's schedule (α, ω, t_f, roles, the up-flows π(i,t), Lemma 3.2) is used **unchanged**. Only
the *down*-flows change: each sender splits its non-fringe wires among its k children unequally.

The invariant **P** (p. 10) is unchanged: a node on level i holds fewer than μδ^r·c(i,t) outsiders
of order r. Lemmas 4.3–4.5 are unchanged in statement. Lemma 4.3 is fed by the new Lemma 4.2′,
whose residual replaces Chvátal's (Aνk−2Aν+1)/(2A²k²) by r* plus explicit separator-geometry
charges.

## 1. Deficit bookkeeping (replaces the closed forms of p. 7–9, and Lemma 3.1)

For a node y on level l write R_y = k^{d−l} for the number of keys addressed below y, and W_y(t) for
the number of wires in subtree(y) at time t. Let G_y(t) = R_y − W_y(t) be y's **deficit**. Then:

1. **Occupancy.** For a node x with children w_1..w_k, the wires in x are
   a_x(t) = W_x − Σ_l W_{w_l} = Σ_l G_{w_l}(t) − G_x(t), since R_x = Σ_l R_{w_l}.
   For a leaf, a_x = R_x − G_x.
2. **Sending.** An active sender x at time t sends π_x(t) wires up and b_l wires to child l, with
   Σ_l b_l = a_x − π_x. Write θ_l := G_{w_l}(t) − b_l. Then Σ_l θ_l = π_x + G_x(t).
3. **Updates.** After the step, G_{w_l}(t+1) = θ_l and G_x(t+1) = G_x(t) + π_x. Children of an
   active node are inactive at t (parity), so nothing else changes their subtrees' wire counts.

A table is any choice of integers θ_l ≥ 0 with b_l ≥ 0 and Σθ = π + G. Chvátal's uniform table
is θ_l = G_{w_l} − β(i,t).

**Lemma 3.1′.** Top nodes have G = 0, because all N wires lie below the top level.

**Design P (integer).** Let x be an active sender at time t with capacity c = c(i,t), deficit
G = G_x(t) and up-flow π = π(i,t) (Chvátal's value). Put s = 0 if G = 0, and s = r*·c otherwise.
Then:
- the two end children get θ_1 = θ_k = π/2 + G − s;
- the k−2 interior children share I = 2s − G as evenly as possible, each getting ⌊I/(k−2)⌋ or
  ⌈I/(k−2)⌉.

Roles: for topDesc (α(t+1) > α(t)), π = 0 and θ ≡ 0, so all children become top nodes with G = 0.
For botRise, π = a and nothing goes down. In both cases this agrees with Chvátal.

**Integrality.** Every active non-top node lies at least two levels below the top. So
c ≥ A²·c(α(t),t) ≥ A²·2k² = 2^19 (p. 8: c(α(t),t) ≥ 2k²). Hence r*·c = 15c/2^19 is an integer.
Chvátal's π are even integers (p. 9). So θ_end is an integer.

## 2. Invariants of design P

Let c_x denote x's capacity at its active times. The child's capacity at the time it next sends is
c(i+1, t+1) = Aν·c.

**(I1) Deficit bound: G_x ≤ g*·c_x at every active time of x.** By induction over the step at
which x's parent last assigned θ_x:
- **x becomes a top node** (parent topDesc, or t = 1): G = 0.
- **The parent is a top node with G = 0 and π = νc/(Ak)** (topRise, p. 8, including t = 1→2):
  - end child: g = (π/2)/(Aνc) = 1/(2A²k) = g*;
  - interior child: g = 0.
- **The parent is interior or botDesc, with π = p·c, p = (Aνk−1)/(A²k²), and parent deficit
  g ≤ g*:**
  - end child: g′ = (p/2 + g − r*)/(Aν) ≤ (p/2 + g* − r*)/(Aν) = g*, because
    p/2 − r* = (Aν−1)/(2A²k) = (Aν−1)·g* exactly;
  - interior child: θ ≤ ⌈I/(k−2)⌉ ≤ 2r*c/(k−2) + 1, so
    g′ ≤ 2r*/((k−2)Aν) + 1/(Aνc) ≤ r*/28 + 2^-21 < g* = 2^-15, using c ≥ 2^19.
- **The parent is a non-top node with G = 0** (so s = 0): the end child gets
  g′ = p/(2Aν) = 63/2^21 < g*, and the interior children get 0.

So I ≥ 0 always (G ≤ g*c ≤ 2r*c), and θ ≥ 0. (Simulated: max G/c = g* exactly, d ≤ 22.)

**Bottom ratios.** At (4,5,3), ω*(t) = (t+2)/3, so the bottom ratio R_x/c = 2^{3t+6−9ω(t)}
depends only on t mod 6. Checking the six residues: R/c = 1 or 1/64 at botDesc times, and 1/4096
at botRise times. (The code agrees for all d < 500.)

**(I2) Nonnegative blocks.** We need b_l = G_{w_l}(t) − θ_l ≥ 0. A child w satisfies
G_w(t) = G_w(t−1) + π_w(t−1) ≥ π_w(t−1), or G_w(t) = R_w if subtree(w) is empty.
- **Interior and topRise senders.** Their children were active at t−1 and were not botRise, since
  a botRise child would empty level i+1 and make x a bottom node. So
  G_w(t) ≥ p·c(i+1,t−1) = p·A·c/ν = 256·p·c ≈ 0.0615c. Meanwhile
  θ_l ≤ π/2 + G ≤ (p/2 + g*)·c < 1.6e-4·c, and topRise has the smaller value π/2 = c/8192.
- **botDesc senders.** Children have empty subtrees, so G_w = R_w = R_x/k ≥ c/1024 > θ_l, using
  the bottom ratios.
- **topDesc:** θ = 0. **botRise:** no blocks.

(The simulation shows no negative blocks for d = 10…22.)

**(I3) Occupancy: a_x(t) ≤ η·c, with η = 1 + 7/4096.** By §1.1 and the updates, when x was active
at t−2 and its children at t−1,

a_x(t) = π_x(t−2) + Σ_l π_{w_l}(t−1) + θ_x^{(t−3)} − θ_x^{(t−1)}.

Here θ_x^{(s)} is the deficit the parent assigned to x at step s, and G_x(t−2) = θ_x^{(t−3)}.
- Σ_l π_{w_l}(t−1) = k·p·c(i+1,t−1) = 4096·p·c.
- π_x(t−2) is either 64·p·c (interior or botDesc at t−2) or 64·c/4096 (topRise at t−2, in which
  case θ_x^{(t−3)} = G_x(t−2) = 0).
- θ ≤ g*·c(i,t−2) = 64·g*·c.
- So a/c ≤ max(4160·p + 2^6·2^-15, 1) = max(1 − 2^-12 + 2^-9, 1) = 1 + 7/4096.

Bottom nodes have a = R_x − G_x ≤ R_x ≤ c. Top nodes have **a = c exactly**: with G = 0 at t and
t−2, the formula gives 64·c/4096 + 4096·p·c = 1/64 + 63/64 = 1 times c after topRise, and
k·ν·c(i+1,t−1)/(Ak) = c otherwise.
The simulated maximum is exactly 1.001709 = 1 + 7/4096. (`r1_point.py` uses the larger,
conservative 1 + 15/8192 from SLACKFREE §4.)

**(I4) Residual.** Let T_j = θ_1 + … + θ_j, L_j = T_{j−1} − π/2 and R_j = π/2 + G − T_j. Then
max_j (L_j⁺ + R_j⁺) ≤ s ≤ r*·c.
- If G = 0, then s = 0 and θ = (π/2, 0, …, 0, π/2). So T_j = π/2 for 1 ≤ j ≤ k−1 and T_k = π,
  and therefore L_j ≤ 0 and R_j ≤ 0 for every j: the residual is 0.
- Otherwise:
  - j = 1: R_1 = s, and L_1 < 0.
  - j = k: L_k = s, and R_k < 0.
  - L_j is nondecreasing and R_j nonincreasing in j, since θ ≥ 0. So a single positive term is at
    most s.
  - If both terms are positive at an interior j, then L_j + R_j = G − θ_j ≤ G − ⌊I/(k−2)⌋. This
    is an integer below s + 1 when G ≤ k·s/(k−1), which is (I1). So it is at most s.

(Simulated: integer residual = r*c exactly.)

## 3. Lemma 4.1′ and Lemma 4.2′ (replace p. 11–12)

Write Δ₁ = μδkA²c/(1 − δ²k²A²).

**Lemma 4.1′.** If P holds at time t and i < ω(t), then u holds at most G_w(t) + Δ₁ keys addressed
below its child w.

*Proof.* Keys addressed below w number R_w. Of the W_w wires below w, all but the outsiders held
there hold keys addressed below w. By P, those outsiders number at most
Σ_{j≥1} k^{2j−1}·μδ^{2j−1}·c(i+2j,t) < Δ₁ (p. 11, verbatim). So u holds at most
R_w − (W_w − Δ₁) = G_w + Δ₁. If i = ω(t), there are no wires below w, and the count is exactly
G_w. ∎

**Lemma 4.2′.** If P holds at time t ≥ 1, then u sends to child j fewer than

μc + (k−1)Δ₁ + (L_j⁺ + R_j⁺) + ε_B·a + γ

keys not addressed below child j. Here γ is the geometry charge of §4, and γ = 0 for exact sorters.

*Proof.* The separator output is F₁, B_1, …, B_k, F₂, with |F_i| = π/2 and
|B_h| = b_h = G_h − θ_h.
- **Lower intruders under a sort.** Keys of u addressed left of child j's range are the outsiders
  O_L below u's range plus the keys addressed below children h < j. There are at most
  O_L + Σ_{h<j}(G_h + Δ₁) of them. A sort puts them in the first positions. B_j starts after
  π/2 + Σ_{h<j} b_h positions, so at most (O_L + (j−1)Δ₁ + T_{j−1} − π/2)⁺ ≤ O_L + (j−1)Δ₁ + L_j⁺
  of them reach B_j.
- **Upper intruders.** By symmetry, using a = Σ_l G_l − G (§1.1): positions after B_j number
  π/2 + Σ_{h>j} b_h, and Σ_{h>j} θ_h = π + G − T_j. So the upper intruders are at most
  O_R + (k−j)Δ₁ + R_j⁺.
- **Total.** O_L + O_R < μc by P, which gives the sorted bound. A separator adds at most ε_B·a
  further intruders per block (Property B), plus γ (§4). ∎

**Lemma 4.3′.** Chvátal's proof of Lemma 4.3 (p. 12) goes through verbatim with the bound of
Lemma 4.2′. Divide by c(i+1,t+1) = Aν·c and use (I3), (I4) and γ ≤ γ̂·Aν·c (§4). Then P of order 0
holds at t+1, provided

**(4.2′)** μ + (k−1)μ·sib + μδA²k + r* + γ̂·Aν + ε_B·η ≤ μ·Aν, with sib = δkA²/(1 − δ²k²A²).

`r1_point.py` checks (4.2′) in exact rationals, with a reserve of 0.1μ for γ̂·Aν: the ratio is
0.99909. It also checks (4.3), (4.4), (4.5) and δkA < 1: ratios 0.983, 0.999, ≈ 1 − 10^-6 and
6.9e-4. Condition (4.1) concerns only the root separator (§6).

**Lemma 4.4** (p. 13) is unchanged. It uses (4.3) and Lemma 3.2 to get π/c ≥ (Aνk−1)/(A²k²), then
(4.4), so that u's order-(r−1) outsiders number at most δ_F·|F|, and then Property F. Since π is
Chvátal's, only the support step needs a word.
- For scramble senders, Property F is the padded form of §4: j real keys, at most
  jmax = δ_F·f·n, with the protected (f+1)·n ≤ π/2. Support μc ≤ δ_F·f·n is checked per sender.
  The package's `F2Params.jmax` and its Chernoff preconditions hard-code 128/4095 (`F2Defs.lean:75`).
  The deterministic F2 chain uses jmax only as a number, so a δ field in `F2Params` is a
  mechanical refactor (LEAN-PLAN W2/W3). The certificates check the preconditions at δ = 1/8.
- For exact sorters, |F| = π/2, and no order-(r−1) outsider is sent down.

**Lemma 4.5** is unchanged. c(α(t_f), t_f) < 2A²k² = 2^19, and μδ·2^19 < 1, so at t_f there are no
order-1 outsiders.

## 4. Separator modules (replaces §5–6 as used by the 1419 package)

- **Small senders (a ≤ 2^45):** Batcher's sort on 2^45 wires, of depth S(45) = 1035, where
  S(q) = q(q+1)/2. Then ε_B = ε_F = 0 and γ = 0.
- **Large senders (a > 2^45):** the padded two-round separator `paddedPack2Net` of
  `../../../experiments/tapered/BaselineFringe.lean` and `PaddedSeparator.lean` (kernel-checked in the tapered
  experiment). It uses an (m+1) × n rectangle with a ≤ (m+1)·n and m·n ≤ a, so at most one partial
  dummy row, and three column sorts of height m + 1 ≤ 2^26. That is depth 3·S(26) = 1053.
  - **Geometry, for every sender except topDesc.** Try the fringe classes f ∈ {7934, 406109} in
    order. For a class, take n = ⌊π/(2(f+1))⌋, so the protected (f+1)·n ≤ π/2. Require support
    μc ≤ δ_F·f·n, and m = ⌈a/n⌉ − 1 ∈ [2^25.6, 2^26 − 1].

    By hand, for all d: n ≥ 2^19, so m = (2(f+1)·a/π)(1 + O(2^-19)). By role:
    - **mid, and botDesc with R/c = 1:** π = p·c and a/c ∈ [1 − 2^-12 − 2^-15, 1 + 7/4096]. For
      f = 7934, 2(f+1)/p = 6.6036×10^7, so m ∈ [6.60, 6.62]×10^7.
    - **topRise:** π = c/4096 and a = c, so m ≈ 2·7935·4096 = 6.50×10^7.
    - **botDesc with R/c = 1/64:** a/c ∈ [1/64 − g*, 1/64]. For f = 406109, m ≈ 5.27×10^7.
    - **Support:** n ≥ π/(2(f+1)) − 1, so δ_F·f·n ≥ δ_F·π/2·(1 − 1/(f+1)) − δ_F·f, and
      δ_F·π/2 = μ₄₄·c = μc/(1 − 2^-10). Since 1/(f+1) < 2^-10 and c ≥ 2^45, support holds. For
      topRise, δ_F·π/2 = δ_F·νc/(2Ak) ≥ μc/0.9834, by (4.3).

    The exact simulation agrees (d = 14…22; every large sender fits; m ∈ [5.27×10^7, 2^26 − 1]).
  - **Large topDesc senders** (the root in the early oscillation phase, with π = 0) hold no
    outsiders, so they need only Property B. Use n = ⌈a/2^26⌉ and m + 1 = ⌈a/n⌉ ≤ 2^26.
    Lemma 3.2 makes every other topDesc node small.
  - **Property B.** The walk bound (ROUND2.md, n-uniform for n ≥ 16) gives, at every row threshold,
    excess < (d/2)·m·n. `cert_walk.py` certifies d ≤ ε_B = 1/105,000 in interval arithmetic:
    θ* by a concavity-based lower enclosure, a rigorous quadrature for the round-1 MGF, a continuous
    cover of p ∈ (0,1), and every m in the admitted window [2^25.6, 2^26] (`cert_walk.out`; float
    values from 8.29e-6 at 2^25.6 to 6.74e-6 at 2^26). Here m is the rectangle's row count, which
    is m+1 in the padded notation.
  - **The charge γ.** `paddedPack2Net_all_cut_bounds` (`../../../experiments/tapered/PaddedSeparator.lean`) bounds
    each cut direction by (ε_B/2)·(m+1)·n + n, at any cut position (not only row-aligned ones) and with
    padding. So per block γ ≤ 2n + ε_B·((m+1)·n − a) ≤ 3n.
    - With n ≤ π/(2(f+1)) ≤ c/(8192·7935), or n ≤ a/2^26 + 1 for topDesc, we get
      γ/(Aν·c) < 1.2e-8 ≈ 0.0008μ, inside the 0.1μ reserve.
  - **Property F (padded).** `paddedPack2Net_fHigh_baseline` and `_fLow_baseline` give escapes
    < j/J for j ≤ jmax real keys, with no dummy-rank surcharge. They require F2ROUND's
    small-rank, R1 and R2 witnesses for the truncated m-row scrambles at (f, J, δ_F). The
    witness parameters (g1, g2, c, b) are:
    - f = 7934: (2380, 7616, 1/4, 1596); interval certificate ln(2P₁) ≤ −3154, ln(2P₂) ≤ −24;
    - f = 406109: (60916, 292398, 1/20, 150); ln(2P₁) ≤ −631, ln(2P₂) ≤ −559.

    These are `fringe_cert_R1lean_f*.out` (per-E route with exact range E ≤ 60). They are also
    proved in Lean: `Fringe7934.fringe_fail` and `Fringe406109.fringe_fail` bound each of SR, R1
    and R2 by 1/10000 for every n ≥ 16 (LEAN-PLAN W3). They replace the earlier choices
    (1586, 6743, 2/5, 1201) and (81221, 345192, 2/5, 31), certified in `fringe_cert_R1_f*.out`.
    The new choices were picked so that the package's closed-form R1 lemmas apply.

    Notes:
    - The ln(2P) values already include both orientations: the factor 2 is F2ROUND §5's flip
      doubling.
    - For f = 406109, J/D = 3.74 < 16, so the certificate evaluates its worst points below the
      admissible n ≥ 16. This is conservative because the ln n coefficient is negative.
    - With the bulk budgets 1/100 (round 1) and 1/1000 (round 2), the total failure probability
      is below 1. So for each shape (m, n, f) a scramble pair exists satisfying B and F, and every
      node of that shape uses it.

## 5. Depth

- **Per stage.** Every active node runs its module in parallel, so a stage has depth
  max(1053, 1035) = 1053. Scrambles are wire permutations.
- **Stage count.** At (4,5,3), α*(t) = (3t − 4d + 15)/5 and ω*(t) = (t+2)/3. At t = 3d − 14:
  - α* = d − 5.4, which rounds up with parity d to d − 4;
  - ω* = d − 4.

  So t_f = 3d − 14, the meeting level is d − 4, and c(α(t_f), t_f) = 2^16. The code agrees for
  every 6 ≤ d < 500.
- **Constants.** The root separator at t = 0 (§6) and the final sorters on k^4 = 2^16-wire blocks
  (Lemma 4.5) have depth independent of N.
- **Total.** With lg N = 4d, D(N) ≤ 1053·(3d) + O(1) = 789.75·lg N + O(1). For general n, pad to
  N = 16^⌈log₁₆ n⌉ < 16n; this adds O(1) (restriction of a sorting network). Hence
  limsup D(n)/lg n ≤ 789.75.

## 6. Root separator, (4.1)

At t = 0 the root splits N wires into k parts with an ε_*-separator, ε_* ≤ μ/k = 9.38e-7. Use a
separator with a fixed number of rows (one round of Lemma 6.1 / Theorem 5.1 on m rows), so the
depth is O(1). sqrt(2(1 + ln m)/m) ≤ 9.38e-7 needs lg m ≥ 47; the package uses m = 2^79. This is
an additive constant.

## Open items

1. **Review of the revision.** The first review (2026-10-19) found B1 (the padded fringe) and S1
   (large topDesc senders); both are fixed above. Its smaller points (bulk window, hand facts,
   γ lemma, nits) are folded in.
2. **Single-review dependencies.** ROUND2's walk bound and FRINGE-CERT §3's R2 tail have one review
   each. The per-E fringe route at δ_F = 1/8 is a parameter change of reviewed code.
3. **Lean.** Formalized end to end in `../../AKS/Sub800/` (2026-10-19): `R1T.limsup_minimum_div_logb_le_78975`
   and `R1T.limsup_minimum_div_logb_le_800`, standard axioms only. Two departures from the text:
   (I3) is proved in the form a ∈ [4094, 4104]·c/4096 for non-bottom senders (a slightly wider
   upper bound than 1 + 7/4096, still inside the geometry and Property-B budgets), and the root
   separator at t = 0 uses the package's two-sided B2 separator on 2^42 rows (depth 3·S(42) = 2709)
   instead of one round on 2^79 rows.
