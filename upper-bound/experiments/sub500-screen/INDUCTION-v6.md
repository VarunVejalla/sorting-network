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

**Convergence in d** (`width_sim_443_pkg477_v7_d26_30.out`). Max ratio 0.977031 / 0.977043 / 0.977044 /
0.977044 at d = 18 / 22 / 26 / 30, with 52k and 85k classes at d = 26 and 30. The per-node widths reach a
fixed point. A proof for all d needs the schedule's periodicity (R1: bottom ratios depend only on t mod 6)
together with the contraction of the width recursion (a factor `1/(Aν)` per level).

**Reserve audit** (review item 6). `ROUND = 0.01 μc′` must cover integer rounding (about k keys per block,
negligible), `γ ≈ 0.003 μc′` and `2φ̄ ≈ 0.0034 μc′`, i.e. about `0.0064 μc′`. That fits, with about 0.0036
left.

## 11. Why the certificate holds for all d (sketch)

**Contraction.** For every child type, the half-width recursion is affine in the parent's half-width:

    hw_child ≤ (μ c′ + κ_T·h_parent + loc_T)/(2c′),   κ_end = κ_spill = 2, κ_int = 1,

where `loc_T` collects crossings, `ε_B a`, `kΔ₁/2`, and the like. In units of the child's capacity
`c′ = Aν c`, `h_parent = hw_parent·c`, so the coefficient on `hw_parent` is `κ_T/(2Aν) ≤ 1/Aν = 1/2` at
(4,4,3). The recursion is therefore a contraction with factor at most 1/2 per level. An ancestor k levels
up affects the current width by at most `2^{−k}` times its own width.

**Local terms.**
* The local terms are functions of the node's role and of the relative quantities `a/c`, `π/c`, `G/c`,
  `G_L/c`, and the crossing distances.
* By Chvátal's schedule these depend only on `(t mod 6, i − α(t), ω(t) − i)` (R1 §2: the bottom ratios depend
  only on t mod 6), plus a bounded number of "boundary" effects near the top and bottom levels.
* So for each d the set of local configurations is a fixed finite set, plus boundary configurations that
  stabilise once d exceeds a few periods.

**Consequence.**
* The supremum over all nodes and all d of the order-0 ratio equals the supremum over the finitely many
  periodic configurations of the recursion's fixed point, plus a term `≤ 2^{−K}` for depth-K truncations.
* The run's agreement 0.977044 = 0.977044 at d = 26 and 30 is this fixed point. The d = 22 value differs by
  `1e-6`, consistent with the `2^{−k}` decay.

**A proof needs:**
1. the periodicity lemma for the relative local quantities, extending R1's bottom-ratio computation to all
   roles and to `G_L`;
2. an evaluation of the fixed point on the periodic configurations in exact arithmetic;
3. a boundary-layer bound.

This replaces "run every d" with a finite computation.

**Correction to §11 (same day).** The set of local configurations is **not** finite. Counting distinct
`(role, a/c, π/c, G/c, G_L/c, c′/c)` at 9-digit resolution:

| d | 14 | 18 | 22 | 26 |
|---|---:|---:|---:|---:|
| configurations | 572 | 1150 | 1864 | 2304 |
| new versus the previous d | — | 578 | 795 | 534 |

The relative deficits depend on history. Growth slows, but there is no finite set to enumerate.

**Replacement argument: a box bound.**
1. Prove a d-independent interval for each relative quantity, per role: `a/c`, `π/c`, `G/c`, `G_L/c`, the
   crossing distances, `c′/c`. For example `η` bounds `a/c`, `g*` bounds `G/c`, the schedule fixes `π/c`, and
   the spill rule bounds the prefix.
2. Bound the order-0 ratio over that box in interval arithmetic. The inherited half-width uses the
   contraction (factor `≤ 1/Aν` per level, so the fixed point of the box recursion is finite).

The observed ratio converges (0.977044 at d = 26 and 30). A box bound is cruder than the run, and whether
it stays below 1 still has to be checked.

**Box test** (`BOXTERMS=1`, d = 26). Per role, take the separate maxima of the inherited width term
`h/(μc′)`, the deep term D and the crossing term `ε_B a/(μc′)`:

| role | h | D | e | sum + ROUND |
|---|---:|---:|---:|---:|
| mid | 0.562 | 0.018 | 0.387 | **0.977** (= the coupled maximum) |
| botDesc | 0.596 | 0.018 | 0.381 | **1.005** (over) |
| topRise | 0.251 | 0.018 | 0.387 | 0.666 |

A fully decoupled box fails by 0.5% at botDesc. Its largest inherited width and its largest `a/c` come from
different nodes (they are anticorrelated). The all-d proof must therefore bound botDesc **jointly**, for
example by splitting botDesc into its schedule subclasses (the bottom ratios `R/c` by t mod 6) and bounding
each subclass's box separately. mid already closes by the box.

**Subclass box** (botDesc split by `a/c` in `log₂` bins, d = 26). Every bin closes:

| botDesc bin `a/c ~` | 2^0 | 2^-1 | 2^-2 | 2^-3 … 2^-10 |
|---|---:|---:|---:|---:|
| sum of maxima + ROUND | **0.971** | 0.781 | 0.686 | 0.58 – 0.67 |

mid is at 0.977 and topRise at 0.666. **So an all-d box argument is viable.** It needs:
1. a d-independent bound on the inherited half-width h per subclass (observed `≤ 0.596 μc′`), from the
   contraction `≤ 1/(Aν)` and the bounded local terms;
2. the `a/c` range of each subclass (schedule periodicity);
3. the deep term D (fixed, about 0.018) and ROUND.

Then the order-0 ratio is at most `max(0.977, 0.971, …) < 1` for every d, with about 2.3% slack.

## 12. Transition box: a finite, depth-independent system (`TRANS=1 TRANS_LOCBIN=1`; `transbox_443.out`)

**Tags.** A sender's tag is its role, its `a/c` bin (for botDesc) and the bin of its **incoming** local
term (`round(loc/μ·50)`).

**Transitions.** Each recorded transition `p → q` carries:
* the largest coefficient on the parent's relative half-width (`c/c′` for end and spilled children,
  `c/(2c′)` for interior children);
* the largest local term (crossings, `ε_B a`, `kΔ₁/2`, relative to `c′`).

**Box recursion**

    hw[q] = max_{p→q} ( μ/2 + coef·hw[p] + loc )

is solved to its fixed point. Each tag's ratio bound is then `hw[q]·(c/(μc′))_max + D_max + e_max + ROUND`.

| d | 18 | 22 | 26 | 30 |
|---|---:|---:|---:|---:|
| transitions | 46 | 48 | 46 | 46 |
| worst ratio bound | 0.9773 | 0.9773 | 0.9773 | 0.9773 |

The tight case is mid nodes in local bin L3 (`hw ≤ 1.125μ`). Bin L5 has a larger local term but a smaller
inherited width (0.886μ).
* Without the local-term bins the box is 1.020: too coarse.
* With them it equals the observed maximum (0.977).

**All-d argument.** The fixed point of a finite transition system bounds every depth, **provided the
transition set, with its coefficient and local-term ranges, is complete for all d**. Here it is stable at
46 transitions from d = 26 to 30 (d = 22's two extra are a boundary effect).

**To prove:** the transition set is complete. The tags are determined by the schedule's periodic roles and
by bounded relative quantities. The box then gives **ratio ≤ 0.9773 < 1 for every d**, about 2.3% slack.

**Exact evaluation** (`transbox_exact.py transbox_443_d30.json`). The d = 30 dump is evaluated in
Fractions:
* every coefficient, local term and ratio factor is rounded **up** to a `1e-12` grid;
* the recursion is iterated down from `hw = 10μ` to a post-fixed point `T(hw) ≤ hw`, verified exactly, which
  bounds the least fixed point.

Exact worst ratio bound: **0.977298 < 1**.

Caveat: the inputs are the float simulation's recorded maxima, so this is exact arithmetic on
float-derived data. The transition set's completeness and its ranges for all d are still unproved.

## 13. The all-d box with every transition allowed: reduction to four structural lemmas

`transbox_coarse.py`, `transbox_complete.py`, and the dump `transbox_443_analytic_d22.json`
(`TRANS_TYPEBIN=1 TRANS_ANALYTIC=1`).

**Analytic local caps.** Every local term is replaced by its formula:
* near side: Property B `ε_B a/2` if `dB < 2W/m + 0.005`, else the certified tail;
* far side: the certified tail;
* interior: `ε_B a/2 + kΔ₁/2`;
* spilled: `ε_B a/2`.

**Groups**, by the receiver's incoming child type:

| group | meaning |
|---|---|
| E | end child, both sides beyond the band |
| En | end child, near side at Property B |
| I | interior child |
| S | spilled child |
| T | topRise |

**Diagnostics** (d = 22):
* Binning by child type instead of local-term value reproduces 0.9773.
* Charging Property B on every near side gives **1.043**, which fails. So the near/far flag is needed.
* With the flag, the box is 0.9773 again (`TRANS_ANALYTIC` dump).

**Complete box.** Allow **every** transition `p → q` with `q ≠ T`. Each local cap is linear in the sender's
`a/c`, at `κ_q · (a/c)_max(p)`. Inheritance coefficients are 1/2 for E, En and S, and 1/4 for I. S may be a
dense sender. Spills come only from senders with `a/c ≤ 2^-7`. Solving exactly (Fractions, inputs rounded
up, post-fixed point verified):

| group | E | En | I | S | T |
|---|---:|---:|---:|---:|---:|
| hw / μ | 1.1246 | 1.1899 | 0.8861 | 1.0965 | 0.5 |
| ratio bound | **0.977298** | 0.6710 | 0.8524 | 0.9632 | 0.6650 |

So **the order-0 ratio is at most 0.977298 at every node, for every d**, assuming the following lemmas
(each a statement about the deterministic design recursion, not about randomness):

* **(S1) Capacity:** `a/c ≤ 1.0149` for every sender (observed max 1.01490).
* **(S2) Near ⇒ sparse:** if a sender's near-side margin is `dB < 2W/m + 0.005`, its end child has
  `a/c ≤ 2^-2.5` at its next send (all `En` receivers are in bins `≤ 2^-3`).
* **(S3) Far side:** `dL ≥ 2W/m + 0.005` for every sender (no violations; minimum 0.0277 against 0.0208).
* **(S4) Schedule:** `c/c′ ≤ 1/2` (1/4 for interior inheritance); topRise nodes inherit nothing (`Anc = ∅`);
  spills only at senders with `a/c ≤ 2^-7` (observed 0.0076).

Also used: the per-receiver data `c/(μc′)`, `ε_B a/(μc′)` and D are analytic in `a/c` and `c/c′`, so they
follow from S1 and S4.

The all-d obligation is now four lemmas about the design recursion. S1 and S4 should follow from R1's
schedule computation. S2 and S3 are statements about the deficits `G`, `G_L` and `G(w₁′)` (§2), which are
the next to prove.

### S3 in deficit form (`S3PROBE=1`)

From `b₁ = G(w₁) − θ₁` and `θ₁ = π/2 + G_L(u) + o`:

    dL·a = b₁ + π/2 − Y = G(w₁) − G(w₁′) − o.

**S3 ⟺ `G(w₁) − G(w₁′) ≥ (2W/m + 0.005)·a + o`**: the end child's deficit exceeds its own first child's
deficit by a fixed fraction of the sender's bag.

The tightest dense senders at d = 22 (per phase t mod 6; `G(w₁′)/a` is Y/a less `G_L(u)/a`):

| role | `G(w₁)/a` | `G(w₁′)/a` | `dL` |
|---|---|---|---|
| mid | 0.084 – 0.091 | 0.056 – 0.063 | 0.0277 – 0.0279 |
| topRise | | | 0.0279 – 0.0280 |

The ratio `G(w₁′)/G(w₁) ≈ 0.69` is stable across phases.

**Proof route.** Both deficits are design quantities set at the last sends of u and of w₁. They are:
* `θ₁(w₁) = π/2(w₁) + G_L(w₁) + o(w₁)` for `w₁′`;
* the accumulated `θ` plus `π/2` increments for `w₁`.

So S3 is an inequality between two linear combinations of schedule quantities (`π/c` per phase), plus the
inherited `G_L`. That is a finite computation over the six phases, provided `G_L/c` is bounded, which is
itself a box (`G_L/c ≤ 2.5e-4` observed).

### S3 proved in the generic case; non-generic cases moved into the box (`S3FORM`, `S3CASE`)

**Exact form.** Let w₁ be u's end child. In the design recursion:
* a child's G is reset to its θ at each parent send, and increases by π at its own send;
* the first child's G_L is reset to θ.

If w₁ was an **active mid or botDesc sender at t−1**, then:

    G(w₁) = θ₁(t−2) + π(w₁, t−1),   G_L(w₁) = θ₁(t−2) + π(w₁)/2,
    G(w₁′) ≤ π(w₁)/2 + θ₁(t−2) + o(w₁)        (a spill cap only lowers it)
    ⇒ dL·a = G(w₁) − G(w₁′) − o(u) ≥ π(w₁, t−1)/2 − o(w₁) − o(u).

The numbers in this bound:
* `π(w₁, t−1)/c(u,t) = (Aνk − 1)A/(νA²k²) = 0.060547` (`c(w₁, t−1) = (A/ν)·c(u, t)`);
* centres satisfy `o ≤ (μ/2 + ε_B/4)·c`;
* `a ≤ 1.0149c` (S1).

Together:

    dL ≥ (0.030273 − 0.002610 − 0.00002)/1.0149 = 0.027237 > 2W/m + 0.005 = 0.020840.  ∎ (generic case)

Numerically, `formula ≤ dL` holds for every generic sender (`max(formula − dL) ≤ 0`).

**Non-generic cases** (w₁ botRise or inactive at t−1). These feed only sparse receivers (bins
`a/c ≤ 2^-4.5`). In the complete box they form the group **Eb**: both sides charged at Property B,
`loc = ε_B a/(2c′)`, the receiver sparse, and Eb free to feed every group.

| group | E | Eb | En | I | S | T |
|---|---:|---:|---:|---:|---:|---:|
| ratio bound | **0.986661** | 0.708 | 0.676 | 0.855 | 0.982 | 0.665 |

So the worst is **0.98666 < 1**, exact and with every transition allowed.

**Remaining structural lemmas** (S3 is now done in the generic case):
* **S1:** `a/c ≤ 1.0149`.
* **S2:** sparseness at the next send (`a/c ≤ 2^-2.5`) for the end children of
  1. near-charged senders, and
  2. senders whose w₁ was botRise or inactive at t−1.
* **S4:** the schedule facts, plus the centre bound `o ≤ (μ/2 + ε_B/4)c`, which follows from the centre
  formulas of §12 and `cB, cL ≤ ε_B a/2`.

### S1: the bag-size bound (`S1PROBE`)

The design bag exceeds Chvátal's allocation, `a − alloc ≤ 0.01488c` (mid and topRise; botDesc is
`≤ alloc + 2e-5·c`). **Source** (telescoping the deficit recursion for a mid sender u at t):

    Σ_kids G(kid) = Σ θ_kid(t−2) + Σ π_kid(t−1) = π_u(t−2) + G_u(t−2) + Σ π_kid(t−1)   (conservation)
    a(u,t) = Σ_kids G − G(u) = π_u(t−2) + θ_u(t−3) − θ_u(t−1) + Σ_kids π_kid(t−1)
           ≤ (31·64 + 16·31·128)/65536 · c + θ_u(t−3) = 0.999023c + 64·g·c,

where `g = θ_u(t−3)/c(u, t−2)` is u's deficit ratio at its previous send, since `c(u, t−2) = c/ν²`.

**Deficit fixed point.** `θ_child ≤ π_p/2 + G(p) + o_p` (spill caps only lower it), and
`c(child, next send) = Aν·c(p) = 2c(p)`. So `g_child ≤ (π_p/(2c_p) + g_p + o_p/c_p)/2`, which gives

    g* ≤ π/(2c)_max + o/c ≤ 16/65536 + (μ/2 + ε_B/4) = 2.645e-4      (observed max 2.53e-4)

using `π/c ≤ ν/(Ak) = 32/65536` (the topRise formula, the largest). Hence

**S1: `a/c ≤ 0.999023 + 64·2.645e-4 = 1.01595`** (observed 1.01487).

The complete box with `AC_BOUND = 1.01595` (e terms scaled up accordingly) gives a worst ratio of
**0.987128 < 1**.

**Gaps in this S1 sketch:**
1. Senders whose children were not all mid at t−1 (topRise, botDesc, chains near the boundary) use other
   π formulas. Each is `≤` the mid case or observed `≤ 1`, but each needs the same telescoping.
2. The base of the g recursion: top nodes have `G = 0`, and the root has `θ = 0` at topDesc.

### S2: sparse receivers after near-charging (`S2PROBE`, `S2W`, `s2_schedule.py`)

**Argument.**
1. Near-charging means `dB·a = G(w₁′) − G_L(u) − π_u/2 < thr·a`, with `thr = 2W/m + 0.005 = 0.02084`.
2. In the design the bag holds exactly the keys of the node's range at the node, so `a(w₁) ≤ R(w₁) = k·R(w₁′)`.
3. If `G(w₁′) = R(w₁′)`, i.e. **w₁′ is empty**:

       a/c(w₁, t+1) ≤ k·R(w₁′)/c(w₁, t+1) = k·G(w₁′)/(2c(u))
                   < (k/2)·(thr·1.01595 + g* + π/(2c)) = 8·(0.021172 + 0.000265 + 0.000244) = 0.1735 < 2^-2.5,

   using S1, `G_L ≤ g*·c` and `c(w₁, t+1) = Aν·c(u,t)`.

**Observed:** `W(w₁′) = 0` at **every** near-charged sender (4070 botDesc, 772 mid, 1 topRise at d = 22). So
S2 reduces to:

* **(S2e)** a near-charged sender's grandchild `w₁′` is empty.

Plausibly: near-charging needs `G(w₁′) < 0.021a`, i.e. range(w₁′) is tiny against u's bag. That happens
only where w₁′ lies below every level the bottom has reached with it in range.

**Schedule check** (`s2_schedule.py`). Taking "non-generic" to mean w₁ was inactive, botRise, or a
spilling botDesc at t−1, dense receivers do occur (`mid → botDesc` with `alloc/cap ≈ 1`). They are not
near-charged, because there `G(w₁′) ≈ R(w₁)/k` is large. So S2 has to be stated through `G(w₁′)`, as above,
not through roles.

**Box sensitivity.** Eb/En receivers can be as dense as `a/c ≤ 0.499` before the complete box reaches 1
(`AC_EB` scan: 0.45 → 0.99831; 0.5 → 1.00036). With S2 (`≤ 0.1735`), the worst is 0.987128.

**Status of the all-d lemmas:**

| lemma | status |
|---|---|
| S1 | sketched; boundary roles to finish |
| S2 | reduced to S2e (observed always) |
| S3 | proved in the generic case; non-generic cases charged at Property B |
| S4 | schedule facts plus the centre bound |

### S2e and S4: arguments

**Invariant E (bottom emptiness).** At the start of step s, every node at a level `> ω(s)` is empty.

*Proof by induction on s.*
* Keys move down only from an active level to the level below it. The only active level with an empty
  level below it is ω(s).
* If ω(s) is **botDesc**, then `ω(s+1) = ω(s) + 1` (roles: `ω(s) < ω(s+1)`, parity ±1). Its blocks land at
  level ω(s+1), so levels `> ω(s+1)` stay empty.
* If ω(s) is **botRise**, it sends its whole bag up (`π = a`) and receives nothing. Then `ω(s+1) = ω(s) − 1`
  and levels `≥ ω(s)` are empty after s.

∎

**Capping lemma.** If the spill rule caps a child's θ at its deficit (`θ = G(child)`), that child's block is
`b = G − θ = 0`.

**S2e** (a near-charged sender's grandchild w₁′ is empty).
* *u botDesc* (`i = ω(t)`): `i + 2 > ω(t)`, so w₁′ is empty by E.
* *u mid or topRise.* If w₁ was a generic sender at t−1 with θ₁ uncapped, then
  `G(w₁′) = π(w₁)/2 + G_L(w₁) + o(w₁) ≥ π(w₁)/2`. Here `o ≥ 0`, since the end-type centre is
  `≥ μ/2 − ε_B/4 > 0`. So `dB ≥ (0.030273 − g* − π/(2c))/1.01595 = 0.0293 > thr`, not near-charged.
  Hence a near-charged u had **w₁ botDesc at t−1 with θ₁ capped**:
  * w₁′ (level `i + 2 > ω(t−1)`) was empty by E;
  * it received a zero block by the capping lemma;
  * and it received nothing at t, since u sends only to level `i + 1`.

  ∎

With §S2, the receiver satisfies `a/c < 0.1735`.

**S4** (schedule facts and centres).
* `c(child, next send) = Aν·c(sender)` and `c(u, t−2) = c(u, t)/ν²`: these are the cap formula.
* **Centres.**
  * end: `(μc′ + cB − cL)/(2c′) ∈ [μ/2 − ε_B/4, μ/2 + ε_B/4]`, using `cB, cL ≤ ε_B a/2` and `a ≤ c′`;
  * interior: `≤ μ/2`;
  * spilled: `μ/2`;
  * top: 0.

  So `o ≤ (μ/2 + ε_B/4)c`.
* **Spills only at sparse senders** (corrects the 2^-7 used before). A spill caps the first child, so that
  child is empty (E plus capping) and `G = R(w₁′) < π/2 + G_L + o ≤ 5.29e-4·c`. Hence
  `a/c ≤ k·R(w₁′)/c < 0.00846`.
* **topRise receivers.** By the mirror invariant (levels `< α(s)` are empty: topDesc sends its whole bag
  down), their last width-setting parent send is a topDesc send. That gives `hw = ε a/(2c′)` with no
  inherited term. The box now includes this (`hw_T ≤ 0.6935μ`; it was 0.5μ before).

**Complete box with all proved or conservative inputs:**
* `AC_BOUND = 1.01595` (S1);
* `AC_EB = 0.1735` (S2);
* spill senders `≤ 0.00847`;
* T as above.

Result: **worst ratio 0.986994 < 1** (exact, post-fixed point verified).

**Still open in the all-d argument:**
1. S1 for the boundary roles.
2. The inputs `rf`, `D`, `e` per group are measured maxima. They are analytic (`rf = c/(μc′)`,
   `e = ε_B a/(μc′)`, D a formula), but should be recomputed from the formulas rather than read from the
   dump.
3. The root's oversized topDesc phase, which uses R1 (4.1).

## 14. The all-d width bound from formulas only (`transbox_analytic.py`)

This uses no simulation input. Inputs:
* the package constants `(A, k, ν) = (16, 16, 1/8)`, `ε_B = 2.25e-5`, `δ = 1e-6`, `ROUND = 0.01`, and
  `μ = 2.953503e-5` (the order-0 budget fraction of the package point);
* the certified band tail `3.60899e-6`;
* the lemma bounds S1 (`s ≤ 1.01595`), S2 (`s ≤ 0.1735`) and S4 (spill senders `s ≤ 0.00847`; `c′ = Aν c`).

**Ratio** at a sender of fill `s = a/c` with inherited half-width hw (relative to c):

    ratio = hw/(2μ) + D + ε_B s/(2μ) + ROUND,   D = δA²k(k/(2(1−(δkA)²)) + 1)/2 = 0.018432.

**Inheritance**, with `loc = (cB + cL)/(2c′) = (cB + cL)/(4c)` for end children:

| child type | inherited half-width |
|---|---|
| E | `μ/2 + hw_p/2 + tail·s/2` |
| En | `μ/2 + hw_p/2 + (ε_B/2 + tail)·s/4` |
| Eb | `μ/2 + hw_p/2 + ε_B s/4` |
| S | `μ/2 + hw_p/2 + ε_B min(s, 0.00847)/4` |
| I | `μ/2 + hw_p/4 + ε_B s/8 + kΔ₁/(8c)` |
| T | `μ/2 + ε_B s_max/4` (conservative) |

Every group may feed every receiver group.

| group | E | S | I | Eb | En | T |
|---|---:|---:|---:|---:|---:|---:|
| ratio bound | **0.986974** | 0.982481 | 0.860770 | 0.727045 | 0.694191 | 0.762156 |

**Worst: 0.986974 < 1**, exact, with the post-fixed point verified. This matches the data-based complete box
(0.986994).

So **the order-0 width certificate holds at every node, for every depth d**, given:
* S1 (the boundary roles still to be written out);
* the per-node intruder decomposition of §2 and §3, with lemmas L2 – L4;
* the certified tails.

The previous per-depth float runs are now only cross-checks.

### S1 for every role

* **Senders active at t−2.** Since `G(u) ≥ 0`, telescoping gives
  `a(u,t) ≤ π_u(t−2) + G_u(t−2) + Σ_kids π_kid(t−1)`.
  * The kids' G at t−1 is `θ_kid(t−2) + π_kid(t−1)`: they are inactive at t−2 by parity, and are touched
    only by u's send and their own.
  * The largest π formula is topRise's: `π/c = ν/(Ak) = 32/65536`, so
    `π_u(t−2)/c(u,t) ≤ 64·32/65536 = 0.03125`.
  * botRise does not send blocks, so it never enters as the sender of θ. A botRise u at t−2 is handled by
    `a ≤ R(u)` below.
  * The kids of a mid or topRise sender are mid or botDesc at t−1. A botRise kid would force u to be the
    bottom level, by the parity of ω. Their π is `31/65536·c(kid)` with `c(kid, t−1) = 128c`, so
    `Σ ≤ 0.96875c`.
  * The deficit term is `G_u(t−2) ≤ g*·c(u, t−2) = 64 g* c`.
* **Bottom senders** (botDesc at ω, including botRise at t−2): the bag holds only keys of the range, so
  `a ≤ R(u) = alloc + c/Q ≤ c`.
* **Senders new at the top** (inactive at t−2): the levels above them are empty (mirror invariant), so
  `a ≤ Σ π_kid(t−1) ≤ 0.96875c`.

Hence **S1: `a/c ≤ 0.03125 + 0.96875 + 64·2.6453e-4 = 1.016930`**, and S2 becomes
`8·(0.02084·1.01693 + g* + 16/65536) = 0.173612`.

Formula box with these: **worst ratio 0.987414 < 1**.

## 15. Gap found and closed: interior-grandchild crossings in the end-child rule (REVIEW-v6 item 6)

**Gap.** At u's cut B₁|B₂, keys of the end child w's **interior-grandchild** ranges can cross upward into
B₂. At w's next send they raise the interior `D_h(w)` and shift w's boundaries
(`s_j = N_L − o − Σ_{h<j} D_h`). The end rule `(μc′ + 2h + cB + cL)/2` did not count them:
* cL counts only range(w₁′)'s keys, at distance ≥ dL;
* the interior keys lie closer to the cut.

This is the review's "φ̄ in the width recursion". The interior rule is unaffected. Its `ε_B a/2` bounds all
leaving keys at once, since the shift stays in `[−out_total, in]`.

**Bound (cH).** The interior-grandchild keys sit at rank distance at least w's top-grandchild keys in u's
bag. That is θ_last at w's send, `≥ π(w₁)/2 − o`, the same margin as S3: `≥ 0.027237·a`. By L3a
(margin `d₀ − W`), `cH ≤ T(321400 rows)·a`.

**Certified:** `T(321400) ≤ 1.42704e-6` for `m ∈ [16547000, 2^24]`, `n ≥ 2^13` (`cert_tail_W321400.out`).
The same certified value now also serves cB and cL, whose generic margins are at least as large.

**Joint Property B.** cL and cH are disjoint sets of upward crossings at the same cut, pushing w's shifts
the same way. So `cL + cH ≤ min(2T, ε_B/2)·a`. In the non-generic case Eb this adds nothing beyond
Property B.

**Near threshold.** "Near-charged" now means `dB < 0.02734` (margin below 321400 rows), so S2 becomes
`a/c ≤ 8·(0.02734·1.01693 + g* + 16/65536) = 0.2265`.

**Formula box** (`transbox_analytic.py`, `TAIL_X = 1.42704e-6`, `AC_EB = 0.2265`): **worst ratio
0.985815 < 1**.

| group | E | S | I | T | Eb | En |
|---|---:|---:|---:|---:|---:|---:|
| ratio | 0.9858 | 0.9825 | 0.8608 | 0.7626 | 0.7466 | 0.7104 |

Without the crossing-margin certificate, i.e. charging cH at the band tail `3.6e-6`, the box would be
1.009 and fail. That certificate is what closes the gap.
