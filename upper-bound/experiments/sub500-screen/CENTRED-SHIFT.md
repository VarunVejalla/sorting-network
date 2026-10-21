# Centred block offsets: halving the outsider term of Lemma 4.2′ (derivation, 2026-10-21)

Claude (Opus 5.5). **Claim level: hand derivation, unreviewed.** This is model input for
`screen.py` (`center=True`). Notation follows `../../best/notes/sub800/R1-PROOF.md` §3.

## Setting

Sender u has capacity c and a wires. Its separator output is `F₁, B_1, …, B_k, F₂`, with
`|F_i| = π/2` and `|B_h| = b_h`. In u's bag:
* `O_L`, `O_R` are the order-0 outsiders below and above u's range, with `O_L + O_R < μc` (P).
* `X_h` is the number of keys addressed below child h.

Under an exact sort, positions are ranks.

## The shift identity

The F₁ positions hold the `π/2` smallest keys. These are all `O_L` low outsiders, provided
`O_L ≤ π/2` (which (4.4) gives), and the `π/2 − O_L` smallest keys of child 1. Symmetrically for F₂.
So:

* **The top boundary is exact.** The keys above `B_k`'s top position are exactly F₂'s `π/2` keys:
  `O_R` outsiders plus the top `π/2 − O_R` keys of child k. No key above child k's range is in `B_k`,
  and no key of child k is above F₂ except those that go up.
* **The boundary between `B_j` and `B_{j+1}`** sits at position `P_{j+1} = π/2 + Σ_{h≤j} b_h`. The keys
  ranked below child `j+1`'s range number `Q_{j+1} = O_L + Σ_{h≤j} X_h`. So
  `s_{j+1} := Q_{j+1} − P_{j+1} = O_L + Σ_{h≤j} (X_h − b_h) − π/2`.

Let the design choose `b_1 = X̂_1 − π/2 + o` and `b_h = X̂_h` for interior h, where `X̂` are the design
counts and o is a **design offset**. Then

    s_{j+1} = (O_L − o) + Σ_{h≤j} (X_h − X̂_h),

and the miscount terms satisfy `|X_h − X̂_h| ≤ Δ₁` plus the sided-deficit misattribution (R2). Block
`B_j` receives `s_j⁺` keys from below (child `j−1`'s keys) and `(−s_{j+1})⁺` keys from above (child
`j+1`'s keys). With the miscount terms removed, `s_j = s_{j+1} = O_L − o`, so

    intruders(B_j) ≤ |O_L − o| + (Δ₁ terms) + (misattribution) + ε_B a + γ.

Chvátal's Lemma 4.2′ bounds the lower and upper intruders separately, as `O_L + …` and `O_R + …`, and
adds them, giving `μc`. The identity shows the outsider part is a **single uniform shift**, so only
`|O_L − o|` counts.

## Centring

* `O_L ∈ [0, μc)` is unknown to an oblivious network.
* The R2 misattribution `e` of u's designed ancestral keys lies in a one-sided interval `[−U, 0]`,
  with `U = (μ + ε_B/2) c/(Aν − 1)` (SLACKFREE §4, κ = 1).
* Both enter s with the same sign, through the low side, so `s ∈ [o' − U, o' + μc]` for the design's
  `o' = −o`. Choosing o at the midpoint gives

      |s| ≤ (μc + U)/2.

The (4.2′) budget becomes

    μ/2 + (k−1) μ sib + μ δ A² k + U/(2c) + γ̂ Aν + ε_B η ≤ μ Aν     (U/(2c) = (μ + ε_B/2)/(2(Aν − 1))),

in place of `μ + … + r* + …`.

## What must still be checked

1. **The R2 invariant itself** (SLACKFREE Q): "the designed low/high ancestral keys of x lie in
   range(x₁)/range(x_k), up to `κ(μ + ε_B/2)c/(Aν − 1)`". This is a derivation, not a proof. Its chain
   errors are the parent's low outsiders occupying F₁ slots and B errors at the π/2 cut.
2. **The Δ₁ terms are not uniform** across j: `(j−1)Δ₁` from below, `(k−j)Δ₁` from above. They remain
   as in Chvátal, i.e. `(k−1)Δ₁ = (k−1) μ sib c`.
3. **Separator errors.** Property B errors at each cut are not part of the uniform shift. They stay as
   `ε_B a` per block.
4. **Sign conventions** of `e` relative to `O_L`. If e enters with the opposite sign, centring still
   gives `(μc + U)/2`, since the bound only needs both to lie in known intervals.
5. **Compatibility of the offset with the flow table.** `θ_1 = G_1 − b_1` changes by o, which needs
   `θ ≥ 0` and `b ≥ 0`. o is about `μc/2`, much smaller than `θ_end ≈ π/2`.
6. **The child-side accounting** (Lemma 4.3′): intruders become order-0 outsiders at the child,
   unchanged.

## Pricing (`screen.py`, `runfix`, band + merge-first)

| invariant | fringe | band tail | cost |
|---|---|---|---:|
| design P (`r*`) | /5.8 | walk bound | 603.8 |
| R2 κ = 1, centred | /5.8 | walk bound | **503.3** |
| R2 κ = 1, centred | /5.8 | 0.13/W | **480.0** |
| R2 κ = 1, centred | current | walk bound | 529.3 |
| `r* = 0`, centred | /5.8 | walk bound | 464.0 |

The run's "R2 κ = ½, centred" row (477.3) double-counts centring and is not valid.

## Check and a one-sided variant (same day)

`centred_shift_check.py` builds explicit sorted bags (random and extreme `O_L`, `O_R`). The maximum
per-block intruder count is **exactly** `|O_L − o|` when the design counts are exact. The worst case is
μc uncentred and ½μc centred.

**One-sided centred** (`center1=True`; no new invariant). Even without R2, the unknown split
`Y_low ∈ [0, G]` of the sender's deficit is the same uniform shift. So centring gives `(G + μc)/2` per
child.
* With end-only deficits (interior θ = 0), the steady state is `g = p/(2(Aν − 1))`.
* That is larger than design P's `2^-15`, but the halving more than pays for it.

| package | cost |
|---|---:|
| 3 sorts, design P (calibration) | 789.8 |
| 3 sorts, one-sided centred | **761.2** ((4,6,4), q = 28) |
| 3 sorts, one-sided centred, fringe /5.8 | 674.7 |
| band + merge, one-sided centred, fringe /5.8 | 558.8 |
| band + merge, R2 centred, fringe /5.8 | 503.3 |

The one-sided variant is a near-term candidate for improving the **proved** bound (789.75 → about
761). It needs:
* the centred block design and its (I1)–(I4) re-derivation with end-only deficits;
* new bulk and fringe certificates at (4,6,4), q = 28.

Everything else reuses Chvátal's invariant.

## Sibling-term centring and a near-term 731.25 (same day)

The `(k−1)Δ₁` term comes from one-sided miscounts `X_h − X̂_h ∈ [0, Δ₁]`. Boundary j's cumulative error
lies in `[0, (j−1)Δ₁]`, so centring each boundary offset halves it (`center_sib=True`).

| package | cost |
|---|---:|
| R2 centred (+ sib centred), band tail walk bound | 503.3 |
| R2 centred, band tail 0.25/W | **490.0** |
| R2 centred, band tail 0.13/W | 480.0 |
| **one-sided centred + sib centred, 3 sorts, current fringe** | **731.25** ((4,5,3), q = 25) |

**The 731.25 point without route (d).** Under one-sided centring the (4.2′) budget grows enough that:
* allowed `ε_B = 1.385e-5`, `ε_F = 3.17e-5` (`J ≈ 3.2e4`), `δ = 8.2e-6`;
* the fringe needs `f ≈ 3270`, inside the class-A window `f + 1 ≤ 4024`;
* the old certified route scales as `f ≈ 18√J ≈ 3200` there.

The bulk is the kernel-checked R1Cells25/R2Cells25. These certify `ε_B = 1/70000 = 1.43e-5`, which is
**3% above** the model's allowed value. So an exact-rational (4.2′) check (as in `r1_point.py`) with
the centred terms is the first gate. If it is short, the margin can come from:
* centring the γ̂ reserve as well;
* tighter rows;
* or rerunning `gen_r1_cells.py` at a slightly smaller ε_B.

**Path to a proved 731.25:**
1. Lemma 4.2″: the uniform-shift identity plus centred offsets.
2. A centred end-only-deficit design table, with (I1)–(I4) re-derived.
3. An exact (4.2″) check.
4. Fringe certificates at `J ≈ 3.2e4`, using the existing per-E route.
5. Lean: the R1 layer with the new (4.2″) and the design.

## Exact check at (4,5,3), q = 25 (`centred_point.py`, `centred_point.out`)

One-sided centred design with ε_B = 1/70000 (the kernel-checked bulk), exact rationals:
* `g* = (p + μ)/(2Aν − 3) = 5.1e-5 ≈ 3.4μ`. This is the end-child deficit with the centring offset. Design
  P's is `2^-15 ≈ 2μ`.
* `η = 1.003024`.
* The centred (4.2″) holds for `δ ≤ 5e-6`, so the smallest admissible J is **J = 51045** (lhs/rhs 0.988).
* The fringe at that J needs about `7934·sqrt(51045/190000) ≈ 4110` on the old certified route. That is
  **about 2% over** the class-A ceiling of 4023.

**Verdict: marginal.** The one-sided residual `g*/2 ≈ 1.7μ` is only slightly below design P's
`r* ≈ 1.9μ`. Most of the gain comes from halving the outsider and sib terms. Closing the 2% needs one of:
* a sharper end-child deficit bound;
* a smaller rounding reserve (0.1μ is assumed);
* the exact per-E fringe certificate at J ≈ 5e4 instead of the √J extrapolation;
* or the route (d) fringe.

R2's known split brings the residual down to about 0.17μ after centring, and that is what drives the
sub-500 package.

## Derivation v2: the net low imbalance (fixes a gap in the first version)

The first version treated the child counts `X_h` as known up to Δ₁. In fact x can be **missing** keys of
its own range, sitting laterally in a sibling, while holding other keys in their place (wire counts are
fixed). The shift at every interior boundary is

    s = N_L − o + (Δ₁ terms) + (far terms),    N_L := O_L − D_1,

where `D_1` is the number of child-1 keys missing beyond the design (`X̂_1 − X_1`). Then:
* **Swaps cancel.** If x lost low keys to `x−1` and holds `x−1`'s high keys instead, `O_L` and `D_1` rise
  together and `N_L` is unchanged.
* **Missing child-k keys** change only `b_k`, which is absorbed at the exact top boundary.
* **Missing interior keys** (`D_h`, `1 < h < k`) require spill that is far in rank. The energy method
  (`../lateral-line/PLAN.md`) bounds that at about `1e-7` of the parent's wires, which goes into the far
  terms.
* **`N_L < 0` without a swap** means x's block at the parent was shifted up: it lost low keys to `x−1` and
  gained high outsiders from `x+1`. That happens only through the parent's boundary shift `s_p` (centred,
  `≤ (μ c_p + U_p)/2`), the parent's separator errors at x's cut (`≤ ε_B a_p/2`), and the R2 misattribution.
  In x's units these carry a factor `1/(Aν)` per level, which is the R2 chain:
  `N_L ≥ −U`, with `U = (μ + ε_B/2) c/(Aν − 1)` up to the centring of the parent's share.
* **`N_L ≤ O_L ≤ μc`** by P.

So `N_L ∈ [−U, μc]`, and the midpoint offset gives `|s| ≤ (μc + U)/2`, as priced. The **negative side is
small only because it is inherited**. Without R2's lower bound on ancestral and lateral composition, the
negative side could reach `−O_R`, and centring would gain nothing. The one-sided centred variant has the
same structure, with the deficit split `[0, G]` in place of U; that is how `g*/2` enters.

**Simulation caveat.** `centred_shift_check.py` checks the identity `max intruders = |s|` for given
`(O_L, D, …)`. It does not check the interval `N_L ∈ [−U, μc]`, which is a statement about the
multi-level dynamics. That is the R2 + centring induction, and it is the next thing to derive.
