# Centred sided invariant: consolidated argument (v5, 2026-10-22)

Claude (Opus 5.5). **Claim level: hand argument, unreviewed in this form.** It supersedes `INDUCTION.md`
§0–11 and incorporates `REVIEW-centring.md` and `INDUCTION.md` §12–17.

The design is Chvátal's schedule with:
* end-first ("spill") deficits;
* a type-specific centred offset;
* no r*.

Notation follows `../../best/notes/sub800/R1-PROOF.md` (R1).

## 0. Data and notation

* Sender u: active at t, capacity c, wires a, up-flow π, children `w_1 … w_k`, parent p.
* `G = R − W`, the deficit. It splits as `G = G_L + G_H`, design quantities defined by the recursion in §2.
* In u's bag:
  * `O_L`, `O_R`: order-0 outsiders below and above range(u). P gives `O_L + O_R < μc`.
  * `X_h`: keys of range(`w_h`). `X̂_h` is the design value. `D_h := X̂_h − X_h`.
* `N_L := O_L − Σ_{h∈Pre_L} D_h`, where `Pre_L` is the low prefix of children that receive low deficit
  (§2). `N_H` is symmetric.
* **Conservation** (review, §1): `N_L + N_H = (a − Σ_h X̂_h) + Σ_{h∉Pre} D_h`. So only the `N_L` interval
  needs centring. `N_H` follows.

## 1. Lemmas to prove (the dependencies)

* **L1. Shift identity** (exact sort). The top boundary `B_k | F₂` is exact. Each boundary above the low
  prefix has shift `s = N_L − o − Σ_{h ∉ Pre_L, h < j} D_h`. Every block's intruders are at most
  `s_j⁺ + (−s_{j+1})⁺`. (Checked numerically in `centred_shift_check.py`; the review confirms it.)
* **L2. Separator crossings.** Property B at arbitrary cut positions adds at most `ε_B a` per block (both
  directions at both of its cuts), plus γ (R1 §4).
* **L3. Far-crossing lemma (new, needs certification).** For a sender whose own child-1 count satisfies
  `X_1 − π/2 ≥ χ a` (the crossing distance), the number of separator crossings at the F₁|B₁ cut that move
  a key from outside range(w_1′) **up** past `χ a` ranks is at most `φ′ a`. Here `φ′` is the round-1 excess
  beyond a margin of `χ m` rows: the walk-bound tail at `d0 = χ m`. At (4,4,3), q = 24:
  `χ ≥ 0.062` (mid, topRise; `centred_sim.py`), and `2·tail(0.026 m) ≈ 1.9e-6` is a conservative `φ′`.
* **L4. Prefix sidedness.** Every key of range(u) that is outside subtree(u) and not a far crossing lies in
  `Pre_L ∪ Pre_H`. The reason: F₁ and F₂ take the extreme keys of the bag, and the spill rule fills
  prefixes in order.
* **L5. Far terms** `φ̄`: interior keys displaced by more than one child range (energy method, about `1e-7`).

## 2. Design (per sender type, all constants input-independent)

* **topDesc:** θ ≡ 0, as in R1.
* **botRise:** no blocks.
* **mid, botDesc, topRise:**
  * `θ_low = π/2 + G_L(u) + o_T`, filling children `1, 2, …` with each `θ_h ≤ G_{w_h}` (spill), and
    `θ_high = π/2 + G_H(u) − o_T` from the high end;
  * the remaining children get `θ = 0`;
  * children's sided deficits: `G_L(w_h) = θ_h` for `h ∈ Pre_L`, 0 otherwise (symmetric for H);
  * u afterwards: `G_L += π/2`, `G_H += π/2`;
  * `o_T` is the midpoint of the `N_L` interval **for u's type T** (end-low child, end-high child,
    interior, top), rounded to an integer.
* **Δ midpoints.** At boundary j the deep-lateral terms lie in `[−(k−j+2)Δ₁, (j−2)Δ₁]` (review issue 2).
  Use the per-boundary midpoint, which gives a per-block bound of `kΔ₁/2`.
  * Interior θ stays ≥ 0 by applying the Δ offsets through b, not θ: `b_h = X̂_h + (offset differences)`,
    with integer rounding.

## 3. Invariant Q and the step

**Q(T).** At u's sending time, `N_L ∈ [−λ_T c, μ c + β_T c]`, and the midpoint `o_T` depends on the type:
* **End child** (low side). Both crossing terms at its F₁|B₁ cut are far crossings (L3, review case (b)), so
  * `β_end = (w_end/2 + Aν φ′)/(Aν)`;
  * `λ_end = (w_end/2 + Aν φ′)/(Aν)`;
  * hence `w_end/2 = (μAν + 2Aν φ′)/(2(Aν − 1))`, with no ε_B term.
* **Interior child.** No own-key inheritance (`β_int = 0`), and its lower cut carries ordinary crossings, so
  * `λ_int = (w_par/2 + ε_B η/2)/(Aν) + (k/2) μ sib/(Aν)`;
  * hence `w_int/2 = μ/2 + λ_int/2`, where `w_par/2 ≤ w_end/2` is the parent's half-width.
* **Spilled prefixes** (sparse botDesc): Property B only, scaled by `a/c` (§3, Step 2).

The (4.2) term is the larger half-width over the sender's possible types:
`w̄/2 := max(w_end/2, w_int/2)`.

**Step 1 (P at the children, order 0).** By L1 and L2, `intruders(B_j) ≤ w̄c/2 + kΔ₁/2 + μδA²k c + ε_B a + γ`.
Dividing by `Aν c`:

    (4.2-v5)  w̄/2 + (k/2) μ sib + μ δ A² k + ROUND + RES_γ + RES_φ + ε_B η ≤ μ Aν,

with separate reserves for rounding, γ and φ̄.

**Step 2 (Q at the children).** The child's bag at t+1 is u's block plus its children's F blocks.
* By conservation, the children's F blocks change `N_L(w)` only through keys outside w's range that
  arrive (low outsiders) or own low keys that leave. These are equal in number, by F's composition
  (the review's corrected form of the "cancellation").
* u's shift and crossings give `λ`, and the end-child own-key inheritance gives `β`.
* Spilled prefixes (sparse botDesc, `a/c ≤ 0.0076` at (4,4,3)) use Property B only (review case (a)), with
  cost `≤ ε_B η (a/c)/2`. That is included in `RES_φ` (≤ 0.004 ε_B).

**Higher orders:** Lemma 4.3′–4.5 as in R1, unchanged.

## 4. Design invariants (`centred_sim.py`, SPILL=1, d = 10–22)

* No negative blocks.
* `η ≤ 1.0158`; `G/c ≤ 2.66e-4`.
* Crossing distance `χ ≥ 0.062` at mid and topRise.
* Spills only at botDesc with `a/c ≤ 0.0076`.

## 5. Numbers at (4,4,3), q = 24 (exact rationals; `φ′ = 2·tail(0.026 m)/2 ≈ 0.94e-6`)

| δ | max ε_B | bulk margin (walk bound `1.897e-5`) | `w_end/2` | `w_int/2` |
|---|---:|---:|---:|---:|
| 1e-6 | 2.31e-5 | **1.22** | 3.14e-5 | 2.58e-5 |
| 2e-6 | 2.20e-5 | 1.16 | 3.14e-5 | 2.59e-5 |
| 3e-6 | 2.10e-5 | 1.11 | 3.14e-5 | 2.60e-5 |

The end-child width dominates. The bulk margin is the room the band repair uses. Geometry fits with fringe
classes 3027 … 3.8e6. Package price: about 490 (route (d) fringe), 503 (current fringe).

## 6. Proof obligations, in order

1. L1 (written), L2 (R1 §4), **L3** and **L4** (new), and L5.
2. The Q step for each type: an explicit list of every key movement, plus conservation.
3. Exact rationals for (4.2-v5) with all reserves.
4. Band repair (UB-32) and merge-first in the node spec.
5. Fringe certificates for every class at J; route (d) for the 490 variant.
6. Lean.
