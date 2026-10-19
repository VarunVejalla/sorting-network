# R1 at (16, 32, 1/8): proof of D(n) ≤ 789.75·lg n + O(1)

Claude (Opus 5.5), 2026-10-19. This is a hand proof. It modifies Chvátal, DCS-TR-294 §3–4: page
numbers below are printed pages, and §5–6 are the separator chapters. The numbers it needs come from
`r1_point.py` (exact rationals), `designP_sim.py` (exact simulation), the fringe certificates
`fringe_cert_R1_f*.out` (interval arithmetic) and `../walk-bound/ROUND2.md` (bulk; float
constants). **Not yet reviewed.** Nothing here is in Lean.

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

So I ≥ 0 always (G ≤ g*c ≤ 2r*c), and θ ≥ 0. (Simulated: max G/c = g* exactly, d ≤ 22.)

**(I2) Nonnegative blocks.** b_l = G_{w_l}(t) − θ_l ≥ 0, i.e. θ_l ≤ G_{w_l}(t), where G_{w_l}(t)
is the deficit of the inactive child. At interior nodes, G_{w_l}(t) ≥ π_{w_l}(t−1) = p·c(i+1,t−1),
which is far above θ_l ≤ (π/2 + g*c). This is not yet written for every role; it is **checked by
the exact simulation** (no negative blocks for d = 10…22, all roles); a hand proof
for the sparse bottom is still owed. Chvátal's own table needs the same fact.

**(I3) Occupancy: a_x(t) ≤ η·c.** By §1.1 and the updates,

a_x(t) = π_x(t−2) + Σ_l π_{w_l}(t−1) + θ_x^{(t−3)} − θ_x^{(t−1)},

where θ_x^{(s)} is the deficit the parent assigned to x at step s. For an interior node, the first
two terms equal Chvátal's p·c(i,t−2) + k·p·c(i+1,t−1) = (1 − 2^-12)·c. Also θ ≤ g*·c(i,t−2) = 64·g*·c.
So a/c ≤ 1 − 2^-12 + 2^6·2^-15 = 1 + 7/4096 = η. The simulated maximum is exactly 1.001709; other
roles are smaller in the simulation.

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
Chvátal's, only the support step needs a word: |F| is the *certified* fringe f·n ≤ π/2 (§4), and
μc ≤ δ_F·f·n is checked per sender. For exact sorters, |F| = π/2, and no order-(r−1) outsider is
sent down.

**Lemma 4.5** is unchanged. c(α(t_f), t_f) < 2A²k² = 2^19, and μδ·2^19 < 1, so at t_f there are no
order-1 outsiders.

## 4. Separator modules (replaces §5–6 as used by the 1419 package)

- **Small senders (a ≤ 2^45):** Batcher's sort on 2^45 wires, of depth S(45) = 1035, where
  S(q) = q(q+1)/2. Then ε_B = ε_F = 0 and γ = 0.
- **Large senders (a > 2^45):** a padded m × n rectangle with the two-round separator (sort,
  scramble, sort, scramble, sort) of the package, with column sorts of height m < 2^26. That is
  depth 3·S(26) = 1053.
  - **Geometry.** Fringe classes f ∈ {7934, 406109} are tried in order. For a class, take
    n = ⌊π/(2f)⌋, so f·n ≤ π/2, and require μc ≤ δ_F·f·n and m = ⌈a/n⌉ ∈ [2^25.6, 2^26). The
    exact simulation finds a class for every large sender of every role (d = 18 and 22; 5,737
    senders). A hand argument covering all d is still owed: the class choice depends only on
    a/c ∈ [0.0156, 1.0018] and π/c.
  - **Property B.** The walk bound gives, for every row threshold, excess < (d_m/2)·m·n (ROUND2.md).
    Here d_m ≤ 8.07e-6 on the m range, against ε_B = 9.52e-6. The padding has m·n − a < n dummy
    wires.
  - **The charge γ.** A block boundary that is not row-aligned moves at most n keys relative to the
    nearest row cut. With two cuts per block plus padding, γ ≤ 4n.
    γ/(Aνc) ≤ 4·1.0018/(5.27×10^7·4) < 2e-8 < 0.1μ/Aν.
  - **Property F.** For each class, F2ROUND (`../../best/notes/two-round/F2ROUND.md`) holds with
    (f, J, δ_F) as certified (per-E route, interval arithmetic):
    - f = 7934: ln(2P₁) ≤ −3648 and ln(2P₂) ≤ −559;
    - f = 406109: ln(2P₁) ≤ −94 and ln(2P₂) ≤ −15773.

    These hold for every n ≥ 16 and m ≥ f. The failure budgets (1/100 bulk round 1, 1/1000 round 2,
    1/1000 for each fringe event) sum below 1, so for each shape (m, n, f) a scramble pair exists
    satisfying B and F. Every node of that shape uses it.

## 5. Depth

- **Per stage.** Every active node runs its module in parallel, so a stage has depth
  max(1053, 1035) = 1053.
- **Stage count.** The schedule meets at t_f = 3d − 14 for d ≥ 14 (simulated; t_f − d(x+y)/z is
  bounded by Chvátal's closed forms).
- **Constants.** The root separator at t = 0 (§6) and the final sorters on k^{d−λ}-wire blocks
  (Lemma 4.5, λ = α(t_f) − O(1)) have depth independent of N.
- **Total.** With lg N = 4d, D(N) ≤ 1053·(3d) + O(1) = 789.75·lg N + O(1). For general n, pad to
  N = 16^⌈log₁₆ n⌉ < 16n; this adds O(1) (restriction of a sorting network). Hence
  limsup D(n)/lg n ≤ 789.75.

## 6. Root separator, (4.1)

At t = 0 the root splits N wires into k parts with an ε_*-separator, ε_* ≤ μ/k = 9.38e-7. As in
the package, use a separator with a fixed number of rows (one round of Lemma 6.1 on m rows), so the
depth is O(1):
- Lemma 6.1 gives sqrt(2(1 + ln m)/m) ≤ 9.38e-7 for lg m ≈ 45 (the package uses m = 2^79);
- the walk bound's round 1 reaches it at smaller m.

## Open items (all flagged above)

1. A hand proof of (I2) b ≥ 0 at sparse bottom nodes (the simulation shows it).
2. A hand proof that every large sender finds a fringe class, for all d (the simulation shows it
   for d = 18 and 22).
3. A hand proof of (I3) for the frontier roles.
4. t_f closed form at (4,5,3).
5. The γ lemma (aligned cuts and padding) written out against the package's Property B2 statement.
6. Interval certification of the walk-bound constants (ROUND2 §7).
7. Independent review of this document.
