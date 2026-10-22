# Joint induction for P and the sided, centred invariant Q (2026-10-21)

Claude (Opus 5.5). **Claim level: complete hand argument, unreviewed.** It extends
`../../best/notes/sub800/R1-PROOF.md` (cited as R1) and replaces its design P, Lemma 4.2′ and (4.2′).
Supporting notes: `CENTRED-SHIFT.md` and `SIDED-CENTRED-INVARIANT.md`. Check script:
`package_point.py`.

## 0. Objects

* **Schedule, capacities, roles, up-flows π:** Chvátal's, unchanged (R1 §0).
* **Node u**, active at time t with capacity c, wires a, children `w_1 … w_k` (inactive at t), parent p.
* `G_y = R_y − W_y`: the deficit (R1 §1). It is a deterministic function of the flow table.
* **Order-0 outsiders** of u: keys in u not addressed below u. `O_L` and `O_R` are those below and above
  range(u).
* `X_h`: keys of range(`w_h`) in u's bag; `X̂_h` is its design value; `D_h := X̂_h − X_h`.
* `N_L := O_L − D_1` and `N_H := O_R − D_k`: the net imbalances.
* **Far terms.** `φ_u`: keys of u's interior children's ranges that are outside subtree(u) or misdelivered
  more than one child-range away, in units of c. These arise only from separator crossings far in rank
  (`../lateral-line/PLAN.md`, energy method: `φ ≤ φ̄`).

## 1. Statements, at every active time t of every node u

* **P** (Chvátal): u holds fewer than `μ δ^r c` outsiders of order r. In particular `O_L + O_R < μc`.
* **Q**:
  * (a) `N_L, N_H ∈ [−λ_u c, μ c + β_u c]`, with (**v4**, see §9)
    * `β_u = (w̄/2)/(Aν)` if u is an end child of its parent on that side, else 0;
    * `λ_u = (w̄/2 + ε_B η/2)/(Aν) + φ̄`;
    * `w̄ = (μAν + ε_B η/2)/(Aν − 1)`, the fixed point of `w = μ + β + λ`, so
      `w̄/2 = (μAν + ε_B η/2)/(2(Aν − 1))`.
  * (b) For interior h, `|D_h| ≤ Δ₁ + φ̄ c`.

## 2. Design (replaces design P)

For a mid or botDesc sender u:
* `b_1 = X̂_1 − π/2 + o_L`, `b_h = X̂_h` for `1 < h < k`, and `b_k = a − π − Σ_{h<k} b_h`;
* `θ_h = G_h − b_h`;
* `o_L` = the midpoint of Q(a)'s interval for `N_L`, an input-independent design constant, rounded to an
  integer;
* per-boundary centring of the Δ₁ terms: boundary j gets an extra offset `(j−1)Δ₁/2`, so the sib term is
  halved.

topRise and topDesc are as in Chvátal. botRise has no blocks.

## 3. Step lemma (P and Q at t imply P at t+1 for u's children)

* **Exact sort.** Positions are ranks. F₁ holds the `O_L` low outsiders and the `π/2 − O_L` lowest keys of
  `w_1` (`O_L ≤ π/2` by (4.4)). F₂ is symmetric.
* **Shift identity** (`CENTRED-SHIFT.md`, checked numerically). The top boundary is exact. The boundary
  between `B_j` and `B_{j+1}` has shift `s_{j+1} = N_L − o_L − Σ_{1<h≤j} D_h + (Δ₁ offsets)`.
* **Intruders.** `intruders(B_j) ≤ |s_j|⁺-part + |s_{j+1}|⁻-part ≤ w̄ c/2 + (k−1)Δ₁/2 + μ δ A² k c + 2φ̄ c`.
* **Separator.** Property B adds at most `ε_B a/2` crossings per cut and direction, so `≤ ε_B a` per block,
  plus the geometry charge γ (R1 §4).
* **Order-0 at child w.** Dividing by `c(i+1, t+1) = Aν c` gives

      (4.2-c)  w̄/2 + (k−1) μ sib/2 + μ δ A² k + 2φ̄ + ROUND + γ̂Aν + ε_B η  ≤  μ Aν.

* **Higher orders.** R1's Lemma 4.3′ chain, Lemma 4.4 and Lemma 4.5 are unchanged. They use only
  order-0 bounds and Property F.

## 4. Step lemma (P and Q at t imply Q at the children's next active time)

The child w is next active at t+1. Its bag is u's block `B_w` plus the F blocks its own children sent up
at t.
* **Upper side of `N_L(w)`.** `N_L(w) ≤ O_L(w) + (excess own low keys)`.
  * `O_L(w) ≤ μ c_w` by P at t+1. This includes the intruders from u's positive shift.
  * Excess own low keys occur only for `w = w_1`. u's F₁ took `O_L(u)` outsiders instead of own keys, and
    the design assumed the midpoint, so this is `≤ μc/2 = β_w c_w`.
* **Lower side.** w's own low keys go missing without a matching low outsider only through:
  * u's negative shift, `≤ w̄ c/2`;
  * u's separator crossings at w's lower cut, `≤ ε_B a/2`;
  * u's F₁ composition (the other half, `μc/2`, end child only);
  * far terms.

  In w's units this gives `λ_w`.
* **Cancellation.** The children's F blocks bring own keys and low outsiders together: a grandchild's
  outsider takes the slot of one of w's own keys and arrives at w as w's outsider. So they leave `N_L(w)`
  unchanged.
* **Q(b)** for w: interior keys of w go missing only far in rank, as `φ̄`.

## 5. Roles and base case

| role | step |
|---|---|
| t = 1, and every node that becomes a top node | `G = 0`, no outsiders, `N = 0`. Q holds with `λ = 0`. |
| **topDesc** | no outsiders (R1 §4) and exact X, so the shift is 0. Children become top nodes. |
| **topRise** | `G = 0`. Lateral moves between top siblings are swaps, which cancel in N. Non-swap shifts come only from the last topDesc, which had shift 0 up to `ε_B`. So `λ ≤ ε_B η/(2Aν)`, and §4 applies. |
| **botDesc** | as mid, with `X̂_h` from `R_{w_h} = G_{w_h}`. |
| **botRise** | no blocks. The parent's accounting is the §4 cancellation. |

## 6. Design invariants (as R1 (I1)–(I4))

* **(I1) Deficits.** End child: `g' ≤ (p/2 + g + w̄/2)/(Aν)`, so `g* = (p/2 + w̄/2)/(Aν − 1)`. Interior
  children have `θ = 0` (plus the integer rounding of the Δ₁ offsets).
* **(I2) Nonnegative blocks.** `θ ≤ (p/2 + g*) c`, against a child deficit `≥ p(A/ν) c`
  (`package_point.out`: `5.2e-4 c` against `0.061 c`).
* **(I3) Occupancy.** `η = p(1/ν² + kA/ν) + g*/ν² = 1.0172` at (4,4,3).
* **(I4)** is replaced by §3: there is no residual beyond the centred shift.

## 7. Numbers at the package point (`package_point.py`)

At (4,4,3), q = 24, `δ = 2e-6`, `ROUND = 0.1μ`, `φ̄ = 0` (the far term is about `1e-7`, below 0.01μ):
* (4.2-c) allows `ε_B ≤ 2.067e-5`;
* the walk-bound bulk gives `1.897e-5`, a 9.0% margin;
* `J = 2.51e5`, and the fringe must reach `f ≤ 3967` (route (d)).

## 8. Known weak points (for the reviewer)

1. **The §4 lower side** is the crux: every way w loses own low keys without receiving a low outsider
   must be listed. Have we missed any, e.g. keys sent by grandparents in a topRise/topDesc oscillation?
2. **The F₁-composition term.** Is the midpoint design legitimate when `O_L(u)` is unknown but the number
   of own keys that went up enters w's design count `X̂_1(w)`?
3. **The cancellation in §4** assumes a child's F block is exactly "outsiders first, then own extreme
   keys". That holds under an exact sort. Under a separator it holds up to F-escapes (Property F),
   which go into `φ` or into higher-order outsiders.
4. **The far terms** need the energy-method bound certified at the actual margin (one child range).
5. **Rounding** of `o_L`, the Δ₁ offsets and the design counts.

## 9. Correction v4 (end children)

For `w = w_1`, u's F₁ composition and u's own ancestral uncertainty combine to exactly
`−(N_L(u) − o_L)`. So w holds `N_L(u) − o_L ∈ [−w̄c/2, w̄c/2]` **own** low keys more than designed. These
are not outsiders, so they lie outside w's `O_L ≤ μ c_w` cap, and the upper side gains `(w̄/2)/(Aν)`, not
`μ/(2Aν)`.

The new fixed point is `w̄/2 = (μAν + ε_B η/2)/(2(Aν − 1))`: at Aν = 2 this is `μ + ε_B/4`, against v3's
`μ + ε_B/6`.

| package | cost |
|---|---:|
| v4, walk-bound band tail (about 0.5/W) | 503.3 |
| v4, band tail 0.30/W | **491.3** |
| v4, band tail 0.25/W | **490.0** |
| v4, band tail 0.13/W | 480.0 |

Exact check (`package_point.out`): `η = 1.0178`; the bulk margin is 1.6% at `δ = 2e-6` and 5.9% at
`δ = 1e-6` (`J = 5e5`).

**So the package now also needs a band tail of at most about 0.4/W.** The energy method's
`Σ (z − b − W)₊ ≤ A_global/(4W) ≈ 0.25/W` (global round-1 energy at levels near W, where the support is
only about `mn/W²` columns) is the candidate. It must be certified.

**A possible refinement (not priced).** The upper side uses P's cap `O_L ≤ μc`. Dynamically, `O_L(u)` is
only the parent's positive shift plus crossings plus deeper outsiders (`μδ`-small) plus F-escapes. Bounding
it that way would make the width contract by `1/(Aν)` without the μ floor. That is a larger change to the
invariant and needs care: P's cap is still required for (4.4) and support.

## 10. The band tail is not easily improved (same day)

`Σ_u (z_u − b − W)₊ ≤ A/(4W)` needs the **global** round-1 energy A with uncapped weights.
* Capped levels give each level its own `≈ 2j` budget, so the sum is `≈ Σ_ℓ 2j/lo_ℓ ≈ 4j/W`, worse than the
  walk bound.
* A single uncapped level needs a union over the profiles of all n columns, with entropy far too large.

So the band stays at the walk-bound tail, and **the v4 package prices at 503**: on the knife edge, just
above 500. Getting below 500 needs a sharper round-1 tail (≤ 0.4/W) or about 1% from elsewhere, such
as the rounding reserve, merge alignment, or stage fusion.

## 11. Merge alignment is not a free lever

Without the alignment cost `+l`, the v4 package prices at 495.3 (q = 25). But the child runs are
`p m/2 ≈ 2^12.95` rows (q = 25), just under a power of two.
* A merge tree over the actual, unaligned runs (odd-even merges of arbitrary sizes) costs
  `Σ_i ⌈lg(2^i L)⌉ ≈ 260`.
* Aligned blocks plus one depth-l merge cost `247 + 12 = 259`. The same.
* The saving needs runs `≥ 2^13`, i.e. about 3% more rows than the q = 25 window allows.

So 503 stands.

## 12. After review (`REVIEW-centring.md`, 2026-10-22): confirmed with corrections

**Confirmed:**
* the shift identity, with outsiders on both sides;
* the exact top boundary;
* the conservation law `N_L + N_H = const + Σ_int D_h`, so centring the low side alone is sound;
* centring with a design constant;
* the v4 end-child inheritance;
* no missed grandparent, oscillation, cousin or deficit-split terms;
* η and g*.

**Major correction.** At the F₁|B₁ cut, separator crossings can push a key from outside range(w_1′) up
while a range(w_1′) key stays down. This raises the end child's upper side by own keys, which P's cap
does not cover.
* With Property B alone the term is `w̄/2 = (μAν + ε_B η)/(2(Aν − 1))`, and the (4,4,3) package is
  **infeasible**: `ε_B ≤ 1.74e-5 < 1.897e-5` for every δ.
* **Repair: a far-crossing lemma.** The relevant crossings span about half a child range, i.e. a margin of
  `d0 ≈ 0.026 m` rows. Their count is round-1 excess beyond `d0`, bounded by the walk-bound tail at `d0`
  (`2·tail(d0) ≈ 1.9e-6` at q = 24) or adversarially by `0.26/d0`.
* With the lemma, the term is `(μAν + cross)/(2(Aν − 1))`, with no `ε_B` coefficient. The bulk margin at
  the package point then rises to **1.22–1.28** (`δ = 2e-6` / `1e-6`), against 1.02–1.06 for v4.
* `screen.py` has this as `center3`, and the package prices at **490** ((4,4,3), q = 24, walk-bound band
  tail).

**Medium items to fix in the write-up:**
* the Δ terms are two-sided: centre `[−Δ₁(j−1), …]` correctly, which gives `kΔ₁/2` (negligible);
* define `X̂` and `Ĝ_L` via `Ĝ_L(w) = Ĝ_L(u) + π/2 − o`, with per-node-type midpoints;
* prove the sidedness lemma;
* check the bottom ratios, the separator geometry and (I2) for botDesc at (4,4,3).

**Minor items:**
* replace the §4 "cancellation" argument by the conservation identity;
* interior `θ = −Δ₁/2` is negative: drop sib centring, or round up;
* fix the topDesc λ entry;
* include o in the (I2) printout;
* keep separate reserves for φ̄, γ and ROUND.

**Reviewer's remark (open lever).** Bounding `O_L` dynamically (the parent's positive shift, crossings,
deeper outsiders and F-escapes), instead of by P's cap, appears to remove the μ floor: `ε_B ≈ 3.6e-5` at
this point. That would be a much larger gain than the current margins, and needs its own careful
derivation.

## 13. Dynamic order-0 bound (the reviewer's remark), priced and checked (2026-10-22)

**Idea.** Bound `O_L(u)` by what can actually arrive, not by P's cap μc. That is:
* (a) the parent's intruders into u's block, meaning its positive centred shift plus its crossings at u's
  cuts;
* (b) the children's order-≥1 outsiders arriving in their F blocks (P at order 1: `μδ` times the child's
  capacity, which is small);
* (c) F-escapes from u's previous send (Property F, `< j/J`);
* (d) F overflow, which (4.4) excludes.

The `N_L` interval then contracts by `1/(Aν)` with no μ floor: `w = 2·cross/(Aν − 1)` plus small terms. The
order-0 condition (4.2) becomes

    2 cross/(Aν − 1) + (k−1) μ sib/2 + μ δ A² k + ROUND + ε_B η ≤ μ Aν.

P's cap μ is still needed, for (4.4) support and Property F, but it is no longer the shift.

**Model (`screen.py` `dyn`, self-consistent rows only, i.e. `q_hint` = the resulting q):**

| package | cost |
|---|---:|
| band + merge-first, **current certified fringe** | **477.3** ((4,4,3), q = 24) |
| band + merge-first, current fringe | 495.0 ((3,3,2), q = 20) |
| band + merge-first, fringe /5.8 | 480.0 ((3,3,2), q = 19) |

(Rows with a mismatched `q_hint`, such as 449, are not valid: the crossing term depends on q.)

**Exact check at (4,4,3), q = 24, δ = 2e-5 (`dyn_point_443.py`, `.out`):**
* `η = 1.0143`, `g* = 2.38e-4`, `cross = 1.88e-6`.
* Allowed `ε_B = 3.13e-5` against the walk bound's `1.90e-5`: a **1.65× bulk margin**. The surplus `1.2e-5` is
  the band repair's room, roughly `W ≈ 2^16.3`.
* `J = 26068`: the existing certified fringe route needs about `f ≈ 2906` against a ceiling of 3967, a
  **27% margin**. No route (d).
* At (3,3,2), q = 19 (`dyn_point.py`), the current fringe is infeasible, since J and f conflict there.

**What this rests on, all unproved:**
1. the dynamic order-0 lemma (a)–(d) as an induction jointly with P and Q. This is new and needs a review.
2. centring, as reviewed in §12;
3. the far-crossing lemma;
4. band repair (UB-32);
5. merge-first in the node spec (the Lean core is done);
6. a fringe certificate at `J ≈ 2.6e4` with the existing per-E route (`gen_fringe.py`).

## 14. Correction to §13: the parent's crossings are not far terms

In Chvátal's schedule an active node sends **all** its wires out. So u's bag at t is exactly the parent's
block for u (sent at t−1) plus the children's F blocks. Hence

    O_L(u) = (parent's low intruders into B_u) + (children's order-≥1 outsiders, μδ-tiny).

F-escapes cycle back through the second term, which makes the dynamic lemma clean. But the parent's low
intruders include **all** separator crossings at u's lower cut, up to `ε_B a_p/2`, not only far ones. With
them:
* end child: `w̄ (1 − 3/(2Aν)) = ε_B η/(Aν) + 2·far`;
* at Aν = 2: `w̄/2 = ε_B η + 4·far`.

The ε_B coefficient in (4.2) roughly doubles. §13's 477 used only far crossings and **is withdrawn**.

Re-priced (`screen.py` `dyn2`, self-consistent q):

| package | cost |
|---|---:|
| band + merge-first, current fringe | 503.3 ((4,4,3), q = 25) |
| band + merge-first, fringe /5.8 | **490.0** ((4,4,3), q = 24) |
| band + merge-first, current fringe | 527.0 ((3,3,2), q = 21) |

The dynamic bound and the reviewed centred bound with the far-crossing lemma (§12, 490) now land in the
same place. **The architecture's sub-500 edge is about 490, and it needs the route (d) fringe.**
