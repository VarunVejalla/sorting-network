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
