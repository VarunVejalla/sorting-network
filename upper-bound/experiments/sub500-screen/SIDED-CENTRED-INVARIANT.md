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

## Roles still to do (Chvátal p. 7–9 and R1-PROOF §1)

| role | issue |
|---|---|
| topRise (π = νc/(Ak), G = 0) | children are fresh. Start Q with no inherited term, or with a smaller one. |
| topDesc (π = 0; all children become top nodes) | there is no F, so `O_L` goes straight into `B_1`. Chvátal treats top nodes separately (Lemma 3.1′: G = 0, and outsiders at top nodes need their own count). |
| botDesc (children have empty subtrees) | `G_w = R_w`. The design X̂ comes from R. Check that Q is not needed below. |
| botRise (π = a) | nothing goes down, so there is nothing to do. |
| integer rounding | o, `b_h`, `θ_h` integral. Reserve `ROUND = 0.1μ` (as R1). |
| (I1)–(I4) for the centred end-deficit design | η, nonnegative blocks, `θ ≥ 0` with the offset o. |
| separator geometry γ and padding | as R1-PROOF §4. |
| far terms | the energy-method far-spill bound, certified, enters `D_h` for interior h. |

## Honest status

The sub-500 package (490 in the model) rests on:
1. this invariant;
2. the far-spill bound;
3. band repair (UB-32), at the walk-bound tail;
4. merge-first (UB-39; the Lean core is done);
5. the route (d) fringe (UB-34; tabled, float-level, n-uniform version only sketched).

The exact check at (4,4,3), q = 24 (`package_point.out`) is feasible with a 5.8% bulk margin before the
band. None of these is proved.
