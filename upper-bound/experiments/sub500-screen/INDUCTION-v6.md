# Centred sided invariant, v6: the argument with a per-node width certificate (2026-10-22)

Claude (Opus 5.5). **Claim level: hand argument plus a float certificate; unreviewed in this form.** It
supersedes v5 (`INDUCTION-v5.md`) and closes the items of `REVIEW-v5.md`. R1 refers to
`../../best/notes/sub800/R1-PROOF.md`.

## 1. Structure

The argument has three parts:
* **(i) Local lemmas.** These are statements about one sender's output, valid for every input: L1–L5.
* **(ii) Type rules.** These say how a child's `N_L` interval is obtained from its parent's interval and
  the parent's output (§3).
* **(iii) A certificate.** It enumerates every node class Chvátal's schedule produces (exact flow
  bookkeeping, hash-consed) and checks, at every send, that the order-0 bound P holds at all children:
  `intruders ≤ μ c_child`. This is `width_sim.py`.

v5 needed one closed-form inequality, plus a bottom-boundary lemma for the nodes where it failed. (iii)
replaces both: each node is checked with its **own** a/c, crossing distances and type.

## 2. Local lemmas (one sender u; every input)

* **L1 (shift identity; exact sort).** The positions are F₁, then the low prefix blocks, then the remaining
  blocks, then F₂. Every boundary after the low prefix has shift `s = N_L − o − Σ_{h∉Pre_L, h<j} D_h`.
  Intruders into a block are at most `s_j⁺ + (−s_{j+1})⁺`. (Reviewed twice; checked numerically.)
* **L1′ (top boundary).** The top boundary is exact **when the high prefix is the single end child**. At
  spill nodes (high prefix longer than 1), F₂ can overshoot into the highest non-prefix block, by at most
  `|s|` (review C). The certificate charges spill senders' children the spilled width
  `(μc′ + 2h + ε_B a)/2`, which contains this overshoot.
* **L2 (separator crossings).** Property B at arbitrary cuts gives at most `ε_B a` per block (both cuts,
  both directions), plus γ (R1 §4).
* **L3 (far crossings, two cuts).** For the end child `w = w_1`, with `Y` = the number of keys of range(`w_1′`)
  in u's bag and `b₁ = G_w − θ_w`:
  * at **F₁|B₁**, keys entering w's own low part cross at least `dB·a = Y − π/2` ranks;
  * at **B₁|B₂**, w's own keys leaving cross at least `dL·a = b₁ + π/2 − Y` ranks.

  For a distance `d ≥ 0.02`, the number of such crossings is at most `tail(d·m)·a`: the round-1 excess
  beyond a margin of `d·m` rows. That is the walk-bound tail at that margin, for the three-sort separator,
  **and** for band repair provided the repair fully sorts **disjoint** bands of `2W ≤ (d·m)` rows (review D).
  For `d < 0.02` the certificate uses Property B (`ε_B a/2`).
* **L4 (prefix sidedness, count form).** Every key of range(u) outside subtree(u), other than the crossings
  of L2/L3 and the far terms L5, lies in the **union** of u's low and high prefixes. The prefixes are
  contiguous, and **count**: `Σ_{h∈Pre_L} D_h^{anc} = G_L(u) + O(crossings)`.
  * *Reason:* the only keys of u's range that leave u's subtree are those u (or an ancestor holding u's
    range at its extreme) sends up in F₁/F₂. These are the extreme keys of the respective bag, and the
    spill rule assigns deficits to children in the same order.
  * *Meeting prefixes:* when `θ_low` and `θ_high` exhaust all children, every child is a prefix child and
    L1 has no free boundary. Such senders are sparse botDesc; the certificate charges them as spill.
* **L5 (far terms).** Interior keys displaced by more than a child range: the energy method, about `1e-7`.
  Charged in the certificate's reserve.

## 3. Type rules (implemented in `width_sim.py`)

For a sender with half-width h (absolute) and child capacity c′ (`kΔ₁/2` is the centred deep-lateral term,
review issue 2):

| child type | half-width of `N_L` at the child's next send |
|---|---|
| end (low or high), non-spill | `(μc′ + 2h + c_B + c_L)/2`, with `c_B, c_L` from L3 at `dB`, `dL` |
| interior, non-prefix | `(μc′ + h + ε_B a/2 + kΔ₁/2)/2` |
| prefix child at a spill sender (incl. partial, fully consumed) | `(μc′ + 2h + ε_B a)/2` |
| child of topDesc | `ε a/(2c′)`, with `ε = μ/k` for the oversized early root (R1 (4.1)) and `ε_B` otherwise |
| botRise | no children |

The midpoint `o` of each type is the design constant. The certificate stores widths, not midpoints. A
midpoint is input-independent because each width is.

## 4. Certificate statement and result

For every sender at every stage:

    intruders = h + kΔ₁/2 + μ δ A² k c + ε_B a + ROUND·μ c′  ≤  μ c′.

Here ROUND covers integer rounding (at most about k keys per block), γ (about 0.0004μ, R1 §4) and the far
terms L5.

At (4,4,3), q = 24, δ = 1e-6, `ROUND = 0.01`, d = 14 and 18 (`width_sim_443_r001.out`):
* the largest admissible `ε_B ≈ 2.68e-5`, against the walk-bound bulk precision `1.897e-5`;
* the binding senders are mid and botDesc;
* every node class of the schedule is enumerated (the flow is exact rationals; the widths are quantised
  upward).

Consequences:
* the band repair room is `ε_B − 1.897e-5 = 7.8e-6`, so the band has depth 171;
* stage `245 + 300 + 171 = 716`, so the **coefficient is about 477** (`8/12` stages per bit);
* the fringe needs route (d) at `f ≤ 3967`, `J = 5e5`. Sweeps over `n = 2^13 … 2^26` show 0 FAIL
  (`../fringe-duality/rd_pkg/`).

## 5. What remains before a claim

1. **Make the certificate rigorous.**
   * Exact or interval arithmetic for the widths (currently floats, quantised upward).
   * A proof that hash-consed classes cover all nodes for all d. The schedule is periodic in d (R1 checks
     d < 500); show that the per-node ratios stabilise, as the d = 14/18 agreement suggests.
2. **Proofs of L3 and L4.** These are the new lemmas.
   * L3 uses the walk-bound tail at a margin (existing machinery).
   * L4 is combinatorial.
3. **Band repair (UB-32)** with disjoint bands, `2W ≤ dL·m`. Also check that its escapes enter `ε_B` as
   priced.
4. **Merge-first** in the node spec, and the fringe certificates for every class (route (d) certified;
   the n → ∞ argument).
5. **A review** of this document, then **Lean**.

## 6. Stabilisation in d (`width_sim_443_final.out`)

At `ε_B = 2.68e-5` the mid ratio is 0.9988 / 1.0005 / 1.0021 / 1.0022 for d = 14 / 18 / 22 / 26, converging
just above 1. The package uses **`ε_B = 2.6e-5`**, which still gives band depth 171 and cost about 477.
Ratios at that value are recorded for d = 22, 26 and 30.

A proof needs the periodic structure of the schedule in d (R1's bottom ratios depend only on t mod 6) to
turn this observed convergence into a bound for all d.

## 7. Band repair shrinks the crossing margin (L3 step 4)

The disjoint bands of `2W = 2^18` rows (depth 171) shrink the far-crossing margin from `d·m` to
`(d − 2W/m)·m`, with `2W/m = 0.0156`. With this in the certificate (`BAND2W_FRAC=0.015625`, d = 22 and 26):

| ε_B | max ratio | band depth | cost |
|---|---:|---:|---:|
| 2.6e-5 | 0.9986 (slack 0.14%) | 171 | **477** |
| 2.5e-5 | 0.9814 (slack 1.9%) | 190 | **490** |

The band depth is a step function of the band room `ε_B − 1.897e-5`. So **the package is 477 with thin
slack, or 490 with about 2% slack.** Both are below 500.

## 8. Third review (`REVIEW-v6.md`, 2026-10-22) and fixes

**The per-node certificate is the right replacement for (4.2), but both headline numbers needed fixes.**
1. **Crossing count bug, fixed.** `Y = G(w_1′) − G_L(u)`, not `G_L(w) − G_L(u)`. With the fix the binding
   distance is 0.026 again, and **477 fails** (ratio 1.002–1.004).
2. **Band and depth consistency.** Depth 190 allows `2W` anywhere up to `2^19`, but the band's **own** tail
   needs `2·tail(W) ≤ ε_B − d_bulk`. The margin cut is `2W/m`. The two pull against each other:

   | `2W` | margin cut | `2·tail(W)` |
   |---|---:|---:|
   | `2^18.2` | 0.0179 | 5.89e-6 (exceeds the room at ε_B 2.5e-5) |
   | `2^18.35` | 0.0199 | 5.25e-6 |
   | `2^19` | 0.0312 | 3.2e-6, but the cut exceeds the 0.026 distance |

   Certificate with `2W/m = 0.0199`:

   | ε_B | max ratio |
   |---|---:|
   | 2.4e-5 | 0.988 (the band room `4.8e-6` then needs `W ≈ 2^17.45`) |
   | 2.5e-5 | **1.005 (fails)** |

   The self-consistent point is about `ε_B ≈ 2.43e-5` with about 0.5% slack, still at band depth 190, so
   **cost 490 on a knife edge**.
3. **Row window.** The bulk check must hold at the smallest admitted m. With rows in
   `[2^23.98, 2^24)`, a fringe-class ladder of ratio 1.01 up to about 1e7 fits **every** large sender at
   d = 16 and 20 (`designP_sim.py`, `GEOM_CUT=37`). Bulk at `2^23.98` is `1.916e-5`, and the band depth stays 190.
4. **Still open, per the review:**
   * type-specific midpoints, not one `o = μc`;
   * L4 per child, plus a schedule lemma (spilled children are botRise next, checked for d ≤ 18);
   * a ROUND reserve that covers `γ ≈ 0.003 μc′` and `2φ̄`;
   * topDesc sends at t ≥ 1, checked separately;
   * ratios still rising with d, so a bound for all d is needed;
   * the written L3 corollary of WALK-BOUND §3, with a rigorous tail at each node's m.

**Status: about 490 with about 0.5% slack at the model level.** Effectively at the boundary; the open
items could push it either way.

## 9. Bulk precision uniform over n ≥ 2^13: about 6% slack at 477 (2026-10-22)

`na_precision.py` certifies the walk-bound bulk **uniformly over n ≥ N_CERT = 16**. At this point every
separator sender has `a > 2^37` (Batcher sorts exactly up to `2^37`) and `m ≤ 2^24`, so `n ≥ 2^13`. Uniform
over `n ≥ 2^13`, at `m = 2^23.98` (the bottom of the row window):

| N_CERT | E1 | d |
|---:|---:|---:|
| 16 | 5.851e-4 | 1.916e-5 |
| 1024 | 5.201e-4 | 1.446e-5 |
| **8192** | 5.185e-4 | **1.436e-5** |

So the band room `ε_B − d` roughly doubles. Re-solving band against certificate (crossing count fixed):

| band `2W` | depth | needs ε_B ≥ | margin cut | certificate at ε_B | cost |
|---|---:|---:|---:|---|---:|
| `2^17` | 153 | 3.0e-5 | 0.0079 | 1.06 at 3.0e-5 (fails) | — |
| `2^18` | 171 | 2.124e-5 | 0.0158 | **0.927 at 2.15e-5**, 0.952 at 2.3e-5 | **477.3** |

**Choice: ε_B = 2.2e-5**, giving about 6% certificate slack and about 10% band-tail slack
(`7.6e-6 ≥ 6.88e-6`). **Package about 477 at the model level, with real slack.** The bulk certificate
(`cert_walk.py`, interval arithmetic) must be rerun with `N_CERT = 2^13` and the row window
`[2^23.98, 2^24)`.

## 10. Interval-certified bulk for n ≥ 2^13, and the package at ε_B = 2.25e-5

**Bulk certificate.** `cert_walk_n.py` is `../../best/notes/sub800/cert_walk.py` with the 1/n terms at
`N_CERT = 8192` instead of 16. The 1/n terms decrease in n, so the bound covers every `n ≥ 2^13`. Run with
mpmath interval arithmetic, outward rounding, 8 m-cells:

    m ∈ [16547000, 2^24] (≥ 2^23.98), n ≥ 2^13:   d ≤ 1.49084e-5   CERTIFIED vs 1/66000   (cert_walk_n8192.out)

(Target 1/68000 failed by a hair: `cert_walk_n8192_target68000.out`.)

**Package point.** (4,4,3), q = 24, δ = 1e-6, `ε_B = 2.25e-5`, `ROUND = 0.01μ`:
* band `2W = 2^18`, depth 171; its own tail `2·tail(2^17) = 6.88e-6` is at most the room
  `ε_B − d = 7.59e-6`;
* width certificate with margin cut `2W/m = 0.01584` (`width_sim_443_pkg477.out`): max ratio
  0.942 / 0.944 / 0.945 at d = 14 / 18 / 22, i.e. **about 5.5% slack**;
* stage `245 + 300 + 171 = 716`, so the **coefficient is about 477.3** (8/12 stages per bit);
* fringe: route (d) at `f ≤ 3967`, `J = 5e5`, `n ≥ 2^13` (0 FAIL in the sweeps).

**Rigorous now:** the bulk precision on this window (interval arithmetic, built on the existing walk
bound).

**Still model-level or sketch:**
* the width certificate (floats; the type-rule open items of §8);
* L3 / L4;
* the band-tail values (`tail_frac`);
* route (d);
* the separator / node-spec wiring.

### Band tail from the certified round-1 machinery (floats)

Band escapes beyond W rows equal the round-1 excess beyond a margin W:
`tail(W) = max_p (x(p) − W p n)₊/(mn)`, where `x(p)` is `na_precision`'s NA-Chernoff bound on a set of `pn`
output columns (`n ≥ 2^13`, union `nH(p)`). On a geometric p-grid from `1/n` to 1/2:

| W | 2^16 | 2^17 | 2^17.5 | 2^18 |
|---|---:|---:|---:|---:|
| NA route | 7.18e-6 | **3.36e-6** | 2.34e-6 | 1.63e-6 |
| model `tail_frac` | 7.80e-6 | 3.44e-6 | 2.34e-6 | 1.61e-6 |

So the band-tail values the package uses agree with the certified machinery.

**Caution.** `na_precision`'s **uniform** float routines sample only `P_GRID = k/64` (p ≥ 1/64). That misses
sets below n/64 columns, and on the margin tail it gave a spurious 0. `cert_walk`'s interval certificate
covers all p, including the cell `[0, P0]`, so the certified bulk d is unaffected.

**Next:** an interval version of this margin tail, i.e. `cert_walk`'s round-1 cells with `−W p n` added.

### Band tail, interval-certified (`cert_walk_n.py tail`, `cert_tail_W2e17.out`)

`certify_tail` bounds the round-1 excess beyond a margin of W rows by `sup_p (phi1(p) − W p)/m`, using
`cert_walk`'s certified round-1 cells (`phi1_up − W·p_lo` per p-cell, plus the `[0, P0]` cell). The
geometric p-cells need ratio 1.02 near small p (ratio 1.25 lost 25% of the margin term:
`cert_tail_W2e17_coarse.out`).

    m ∈ [16547000, 2^24], n ≥ 2^13, W = 2^17:   band tail ≤ 3.60899e-6   CERTIFIED

So `2·tail = 7.22e-6 ≤ ε_B − d = 2.25e-5 − 1.491e-5 = 7.59e-6`, about 5% slack.

**Rigorous now** (interval arithmetic, on the existing walk-bound framework):
* the bulk precision `d ≤ 1.491e-5`;
* the band tail at `W = 2^17`;
* both on `[2^23.98, 2^24]` for `n ≥ 2^13`.

**Still to do:**
* the width certificate in exact arithmetic, with the review's type-rule items and all-d;
* the L3 / L4 proofs;
* route (d) certification;
* node-spec wiring;
* a review;
* Lean.

### Width certificate with certified tails (`width_sim_443_pkg477_certtail.out`)

The far-crossing tails come from the same round-1 machinery, and the tail decreases in the margin. So the
certified `3.609e-6` at `W = 2^17` bounds every margin of at least `2^17` rows; shorter margins use
Property B. The tail is also capped at Property B's `ε_B a/2`. At the package point (ε_B = 2.25e-5, margin
cut 0.01584):

| d | 14 | 18 | 22 |
|---|---:|---:|---:|
| max ratio | 0.976 | 0.979 | 0.979 |

That is **about 2% slack**, and the package stays at **about 477**. The width recursion's inputs (bulk d,
band and crossing tails) are now interval-certified. The recursion itself is still a float run with the
type-rule items of §8 open.

### Review items: type-specific midpoints and topDesc at t ≥ 1 (`width_sim_443_pkg477_v7.out`)

* **Type-specific midpoints** (`TYPEMID=1`). Each class carries the centre of its `N_L` interval, and the
  sender's offset o is its own centre:
  * end: `(μc′ + c_B − c_L)/(2c′)`;
  * interior: `(μc′ − λ_int)/(2c′)`;
  * spilled: `μ/2`;
  * top: 0.

  The max ratio improves slightly, 0.979 to 0.977.
* **topDesc senders at t ≥ 1.** These have no outsiders and exact X, so intruders are `ε_B a + ROUND`. Their
  ratio is 0.396, far inside budget.

At the package point (certified tails, ε_B = 2.25e-5), the max ratio is 0.9736 / 0.9770 / 0.9770 at
d = 14 / 18 / 22, about **2.3% slack**. Still open: exact arithmetic for the recursion, a bound for all d,
and a γ / far-term reserve audit (review item 6).
