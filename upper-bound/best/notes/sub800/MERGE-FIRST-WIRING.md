# Merge-first separators in the R1 stage network: wiring audit and the unaligned run merge

Ticket UB-43 · branch `ub-43-mergefirst-731` · Claude (Opus 5.5) · 2026-10-24.

**Claim level.** §1 is a read of the Lean model (`AKS/Sub800/R1Exec.lean`, `R1Wire.lean`,
`R1NodeSpec.lean`, `R1Fields.lean`, `PaddedSeparator.lean`, `R1GeomGen.lean`, `R1Nets.lean`,
`R1Sched.lean`/`R1Table.lean`) plus hand arithmetic on the design-P flow sizes. Nothing in it has been
reviewed independently. §2 is proved in Lean with the standard axioms only.

**Verdict.** The current R1 wiring does **not** feed a node column-run-sorted input, and no choice
inside a node network can make it do so. A merge-first first stage therefore needs a new stage
framework (§1.5). That is not a modest change, so per the ticket we stopped after the unaligned run
merge (§2), which is done.

## 1. How a node's bag reaches its separator matrix

### 1.1 What fixes the placement

* **Stage network.** `R1T.stageNet` (R1Exec.lean) runs `nets t b (S b).card` on the wires of
  `S b = wireSets F t b`, embedded by `(S b).orderEmbOfFin rfl`. So local cell `k` is the `k`-th
  smallest global wire of the bag, for input and output alike.
* **Wire sets.** `wireSets` (R1Wire.lean:283) is defined from ranks in that same order:
  * `parentPart` = `downSetB` = the parent's cells with rank in `[π/2 + off j, π/2 + off (j+1))`;
  * `childPart` = `upSet` = each child's first `π/2` and last `π/2` cells.
* **Node contract.** `NodeSpecAll` (R1NodeSpec.lean) and `R1Specs` (R1Fields.lean:28) quantify over
  **every** input permutation. They are positional: output cell `c` must hold a key of rank about `c`.
* **Separator layout.** `paddedPack2Net = (physicalPack2Net m n).restrictWires a`
  (PaddedSeparator.lean) puts local cell `k` at matrix wire `k`, row-major, so its row is `k / n`.
  The `m n − a < n` padding cells sit at the tail of the last row and are fed `⊤`.

**(a) Placement is fixed, up to a permutation within each row.** A comparator network's input and
output wires are the same wires, so the input layout is the output layout. The output layout is
pinned by the positional spec. The orientation of comparators pins it too: stages 2 and 3 compare
arbitrary pairs of rows, and `columnSortNetwork_relabel_lt` needs the relabelling to preserve rows.
So matrix row `r` must be the cell interval `[r n, (r+1) n)` of the bag's global order. The only
freedom left is which cell goes to which column inside a row.

Allowing a within-row output permutation would also need a recheck of the `+ n` slack in
`pack2_arbitrary_cut_bounds`. That is minor next to the obstruction below.

### 1.2 Are the incoming pieces sorted along the receiver's columns? No.

* **Where a sender's output is sorted.** By `physicalPack2Net_exec` it is the semantic output
  composed with a row scramble. It is sorted only along its final, scrambled columns: one cell
  `(r, π_r(j))` per sender row. In global order those cells are `n_s` apart.
* **Row windows.** Every node's rectangle has `m ∈ [Mlo, 2^q]` rows (`R1GeomGen.geom`), so `n ∝ a`.
* **Capacities.** `cap(l+1, t) = 32 · cap(l, t)` and `cap(l, t+1) = cap(l, t) / 8` (`eN = 4d + 5l − 3t − 6`).
  So a child at stage `t` has `X_c = 256 X_b`, where `b` is its parent at stage `t+1`, and
  `n_c ≈ 256 n_b`.
* **Where a node's content comes from.** At `t+1` node `b` holds `a ≈ 2^19 X_b`.
  * Its 16 children send `2 · (63 or 64) · X_c` each: `16 · 2 · 63 · 256 X_b = 516096 X_b`, about 98%
    of the node.
  * The parent's block is about `a_p / 16 = 2^19 (X_b / 4) / 16 = 8192 X_b`, about 1.6%.

  So the content is almost all child F blocks.
* **Why the child F blocks cannot form runs.** Take two consecutive cells of one child column, say
  `(r, j)` and `(r+1, j)` of the child. Between them the child's order has `n_c − 1` other fringe
  cells, and all of them are in the receiver's bag. So in the receiver's order the two cells are at
  least `n_c − 1 ≥ 256 n_b − 1` cells apart, which is at least 255 receiver rows.

  Any receiver column therefore runs through about 256 consecutive receiver rows that hold cells of
  a single child row. Those cells lie in different child columns, so their order is arbitrary.
  Within the child F blocks, a receiver column has guaranteed sorted runs of length only **1**, and
  no within-row choice changes that. The best one can say is that the receiver column restricted
  to rows `≡ i (mod 256)` is sorted: a 256-way stride interleave, not runs.
* **The parent's block would work but is too small.** Its sender has `n_p ≈ n_b / 4`, smaller than the
  receiver's. So if `n_p | n_b`, any `n_b` consecutive cells of the block hold `n_b / n_p` cells of
  each parent column, at consecutive parent rows. A within-row assignment would then make every
  receiver column sorted across the block. But that is only about 1.6% of the input, and the pieces
  also interleave in global order (wire sets are unions of many global intervals).

**(b), answered.** Every key does arrive from a final column sort, but not as contiguous column
segments of the receiver's matrix. `ColumnRunSorted` (aligned) and `ColumnDescentsApart` (unaligned,
§2) both fail on about 98% of every column, for all inputs that are not specially arranged.

### 1.3 Run length in a redesigned wiring (c)

Suppose input placement were free (§1.5). Each child column segment of an F block could then be put
contiguously into a receiver column.

* **Child F blocks.** Runs would be the child's F-block column segments, of length `f` or `f + 1`
  (π/2 = 63X or 64X cells against `n_c (f+1)`). At the 731.25 point:
  * runs `≥ 3329` (`f + 1 ∈ (3329, 4024]`), so `s = 11` (`2^11 ≤ R + 1`);
  * for the second class, `f + 1 ∈ (210012, 258048]`, so `s = 17`.
* **Parent block.** Its runs are `≈ 8192 X_b / n_p ≈ 512 (f+1)` rows long.
* **Boundaries.** They fall at segment ends, which are not aligned to powers of 2. So the unaligned
  merge of §2 is the right tool. Aligned `RunSorted` would need `2^l`-aligned segment ends, which the
  flow sizes do not give.

### 1.4 Padding (d)

The `m n − a < n` padding cells are the tail of the last row, fed `⊤`. They add no descent at the
bottom of a column. `Bitonic.uRunMergeNetwork` pads with `true` and its proof covers this
(`uRunMergeNetwork_sorts_bool`). The row windows have no other dummy wires.

### 1.5 What the headline would need (e), and the size

1. **Per-node cell orders (the bulk of the work).**
   * Give each node an input placement `e_in` and an output order `e_out`, instead of
     `orderEmbOfFin` and global-order ranks.
   * Realise the reversed comparators by untangling (`AKS/Sort/Untangle.lean`). The untangled net's
     output is the original output composed with a fixed permutation, which `e_out` absorbs.
   * Re-port `wireSets`/`blockOf`/`upSet` and `stageNet`, then everything built on rank in global
     order: `execPlacement` and `mem_image_downSet_iff` (R1Exec), R1Window, R1BadSend, R1FringeSend,
     R1Fields, R1StageKernel, R1Subtree, R1Final (the final layer also uses `wireSets`) and
     R1Induction.

   Estimate: 3–6k lines touched, multi-week.
2. **Sender output lemma.** The separator output, including `uMergePack2Net`'s by `_exec_eq`, is
   sorted along its final scrambled columns. Small, about 100 lines, from `physicalPack2Net_exec`.
3. **Placement invariant.** Define `e_in` from the flow sizes (63X/64X fringes, partial last F rows,
   the parent block, padding). Prove `ColumnDescentsApart m n hn 3330` for the node's actual input
   `X F nets v t ∘ e_in` at every `t` and `q`. About 1–2k lines.
4. **Restricted contract.** `NodeSpecAll` with the input quantifier restricted to `Q x`, and
   `R1Specs` in that form. The consumers apply the contract to `rankPerm` of the actual input
   (`NodeSpecAll.fHigh_keys`, `intruder_keys`), and `ColumnDescentsApart` is invariant under strictly
   monotone relabelling, so the change propagates mechanically. About 300 lines.
5. **Node networks.**
   * `spec_padded` and `spec_Bonly` switch to `uMergePack2Net`, using `uMergePack2Net_exec_eq`
     pointwise. The B-only separator must switch too, since 975 > 930.
   * `spec_sorter` still fits: `S(38) = 741 ≤ 930`.
   * New `R1Point.stage` and `stage_big`/`batcher` fields, and the headline arithmetic.

   About 300 lines.

**Payoff, with headline = 3 · stage / 4.**

| Point | Rows | Current stage | Unaligned merge-first (§2) | Aligned merge-first (`l = 11`) |
|---|---|---|---|---|
| 731.25 | `≤ 2^25` | 975 | 930 → **697.5** | 909 → 681.75 (unachievable, §1.3) |
| 789.75 (`q = 26`) | `≤ 2^26` | 1053 | `21 + 351 − 66 + 702 = 1008` → 756 | — |

The second class at `s = 17` would give a first stage of `33 + 172 = 205`, if all F blocks had
`f ≥ 2^17`.

## 2. The unaligned run merge (Lean, done)

**Modules.** `AKS/Bitonic/UnalignedRunMerge.lean` and `AKS/Sub800/UnalignedMergePack.lean`.

**Input class.** `DescentsApart R v`: any two descents (`¬ v p ≤ v (p+1)`) are at least `R` apart.
Equivalently, sorted runs with arbitrary boundaries and interior runs of length `≥ R`. If
`2^s ≤ R + 1`, every aligned `2^s` block holds at most one descent, so it is a `TwoRun`
(`blockTwoRun_of_descentsApart`).

**Two-run sorter `ssSort s`.** Depth `≤ 2s − 1` (`ssSort_depth_le`).
* The steps:
  1. sort the even and the odd positions recursively (each is again two runs);
  2. interleave;
  3. two layers `(2i, 2i+1)` and `(2i+1, 2i+2)`.
* Why it works: for a Boolean two-run input, `#false(odd) ≤ #false(even) + 1` and
  `#false(even) ≤ #false(odd) + 2` (`twoRun_counts`). With sorted halves, the two layers then
  produce exactly `[k ≥ kE + kO]`.
* Correctness for any linear order is `ssSort_sorts`, by the 0-1 principle restricted to two-run
  inputs, which are closed under monotone maps.
* Python cross-check: every two-run 0-1 input up to `2^7` wires.
* The obvious alternative, one merge step (flip layer plus bitonic merge), does **not** sort two-run
  blocks: there are counterexamples from `2^2` wires on. So "one extra merge level" is not
  achievable this way. `2s − 1` levels is what we prove.

**`uRunMerge s k = ssBlocks s k ; runMerge s k`** (`ssBlocks` = `ssSort` on every aligned block).
* Correctness: `uRunMerge_sorts`, `uRunMergeNetwork_sorts`, and
  `uRunMergeNetwork_sorts_of_descentsApart` (any `m` wires, padding `true`).
* Depth: `uRunMerge_depth_le`, `uRunMergeNetwork_depth_le`:
  `depth + S(s+1) ≤ 2s + 1 + S(s + 1 + (clog m − s − 1))`.

**Column and pack versions** (namespace `Chvatal`).
* `columnURunMergeNetwork` (`_columnMonotone`, `_exec_eq` against `columnSortNetwork`, `_depth_le`).
* `uMergePack2Net` (`uMergePack2Net_exec_eq`): it equals `physicalPack2Net` on
  `ColumnDescentsApart` inputs. This is the unaligned analogue of `mergePack2Net_exec_eq`.
* Instances at `≤ 2^25` rows, `s = 11`:
  * `columnURunMergeNetwork_depth_le_280`: first stage `≤ 21 + 325 − 66 = 280`;
  * `uMergePack2Net_depth_le_930`: separator `≤ 930`;
  * `uMergePack2Net_exec_eq_3330`: runs of length `≥ 3330`.

**Checks.** `#print axioms` shows only propext, Classical.choice and Quot.sound. `python scripts/sorry-gate`
passes. No new `AKS/<dir>`.
