# Sided, centred invariant: induction skeleton (2026-10-21)

Claude (Opus 5.5). **Claim level: proof sketch for the mid role. The other roles are listed, not done.**
This backs the `center2` pricing (`CENTRED-SHIFT.md` v3). Chvátal's notation follows
`../../best/notes/sub800/R1-PROOF.md`.

## State at a sending time of node u (capacity c, children `w_1 … w_k`)

* `O_L`, `O_R`: u's order-0 outsiders below and above range(u). Invariant P gives `O_L + O_R < μc`.
* `X_h`: keys of range(`w_h`) in u's bag. `X̂_h` is the design value (from the flow table).
* `D_h := X̂_h − X_h`, the missing count. For interior h, `|D_h| ≤ Δ₁ + far`. Far is spill more than a
  child's range in rank, which the energy method bounds by about `1e-7` of the parent's wires.
* The **net imbalances** `N_L := O_L − D_1` and `N_H := O_R − D_k`.

**Invariant Q** (on top of P): at every sending time of every non-top node,

    N_L, N_H ∈ [−w_lo c, w_hi c],   w_hi = μ + μ/(2Aν)·[end],   w_lo = (w/2 + ε_B η/2 + μ/2·[end])/(Aν),

with `w = w_lo + w_hi`. Here "[end]" means u is an end child of its parent, on the corresponding side.

## Step lemma (mid sender u, exact sort; separators add `ε_B a` per block)

**Design.** `b_1 = X̂_1 − π/2 + o`, `b_h = X̂_h` for interior h, and `b_k` = the rest. The offset o is the
midpoint of the N_L interval, chosen at the design level (input-independent).

**Shift identity.** Every interior boundary has shift `s = N_L − o + (Δ₁ terms)`, and the top boundary
`B_k | F₂` is exact (`CENTRED-SHIFT.md`; checked in `centred_shift_check.py`). So

    intruders(B_j) ≤ w c/2 + (k−1) Δ₁/2 + μ δ A² k c + ε_B a + γ.

Dividing by `c(i+1, t+1) = Aν c` gives the centred (4.2-c3). So **P of order 0 holds at the children.**

**Q at child w at its next sending time** (t+1; w was inactive at t):
1. **Upper side.** `N_L(w) ≤ O_L(w) ≤ μ c_w` by P at w. Intruders that u's positive shift sent into w are
   w's low outsiders, already inside `O_L(w)`. For `w = w_1`, u's F₁ took `O_L(u)` outsiders and
   `π/2 − O_L(u)` of w's lowest keys up. The design assumed `o_u`, so w holds `±μc/2` more or fewer own
   low keys than designed, which adds `μ/(2Aν)` in w's units.
2. **Lower side.**
   * A negative shift of u (`|s_u| ≤ w_u c/2`) makes w lose own low keys to `w_{h−1}`'s block.
   * u's separator errors at w's lower cut add up to `ε_B a/2`.
   * The F₁ term above contributes its other half.

   In w's units: `(w_u/2 + ε_B η/2 + μ/2·[end])/(Aν)`.
3. **Cancellation of the children's F composition.** Between t and t+1, w's children send their F
   blocks up to w. Grandchild outsiders in those slots arrive at w as w's low (or high) outsiders,
   exactly when the corresponding own keys are missing. So `O_L(w)` and `D_1(w)` rise together and
   `N_L(w)` is unchanged.
4. **No other change.** w's bag at t+1 is u's block `B_w` plus its children's F blocks. The deficit
   bookkeeping is R1-PROOF §1, with `θ_w = G_w − b_w`.

Steps 1–2 give `w_hi`, `w_lo` as stated. The fixed point is `w = (2μ(Aν+1) + ε_B η)/(2Aν − 1)`.

## Roles (sketch)

| role | argument |
|---|---|
| **topDesc** (π = 0, θ ≡ 0) | Large topDesc senders hold no outsiders and have G = 0 (R1-PROOF §4). So `X_h` is exact and the shift is 0; only `ε_B a` remains. The children become top nodes with `N_L = O_L ≥ 0`, so `w_lo = 0`. |
| **topRise** (π = νc/(Ak), G = 0) | Top nodes have no ancestors, so `D_1` comes only from lateral moves between top siblings. Swaps cancel in `N_L`. A non-swap shift needs a parent's shifted blocks, and the last parent (topDesc) had shift 0 up to `ε_B`. So `w_lo ≤ ε_B η/(2Aν)`, and the children follow the mid step. |
| **botDesc** (children have empty subtrees) | The shift identity is the mid one. The design `X̂` comes from `R_w`, with `G_w = R_w`. Q at the children follows the mid step. |
| **botRise** (π = a) | No child blocks. All keys go up, and the parent's accounting is the F-composition cancellation. |

### Design checks at the package point (`package_point.py`)

Sided end-deficit design: the end child gets `θ = π/2 + G + o`, with `|o| ≤ w c/2`.
* `g* = (p/2 + w/2)/(Aν − 1) = 2.84e-4`.
* **(I3)** `η = p(1/ν² + kA/ν) + g*/ν² = 1.0172`.
* **(I2)** `θ ≤ (p/2 + g*) c = 5.2e-4 c`, against a child deficit `≥ p(A/ν) c = 0.061 c`, so the blocks are
  nonnegative.
* With this η the centred (4.2) leaves a **9.0% bulk margin at δ = 2e-6** (J = 2.5e5), or 4.4% at δ = 3e-6.

## Still open

* Integer rounding of o, `b_h`, θ: the 0.1μ reserve, as in R1.
* Separator geometry γ and padding, as in R1-PROOF §4.
* The far-spill bound, certified.
* A full write-up of the induction (P, Q jointly over all roles and stages), and **a review**.

## Honest status

The sub-500 package (490 in the model) rests on:
1. this invariant;
2. the far-spill bound;
3. band repair (UB-32), at the walk-bound tail;
4. merge-first (UB-39; the Lean core is done);
5. the route (d) fringe (UB-34; tabled, float-level, n-uniform version only sketched).

The exact check at (4,4,3), q = 24 (`package_point.out`) is feasible with a 5.8% bulk margin before the
band. None of these is proved.

## Band repair at the package point (clarification)

The band repair's escapes are **round-1** excess beyond a margin. A one sits at row `r ≥ w_v + W` only if
its source has `z > b + W`, so the escapes are `Σ_u (z_u − b − W)₊`. That is the quantity the band
adversary achieves at `0.26 j/W` (`band_adversary.py`). It is not the round-2 column deviation.
* The energy method gives `Σ (z − b − W)₊ ≤ Σ (z − b)₊²/(4W) ≈ 0.25/W` of mn at `j = mn/2`. That prices
  the same as the walk-bound tail (490).
* The adversarial `0.13/W` (477) would need a sharper round-1 tail lemma.

So the band stays at the walk-bound tail in the 490 package.
