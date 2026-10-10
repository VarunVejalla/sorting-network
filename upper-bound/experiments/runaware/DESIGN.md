# Run-aware first column sort — design note (experiment `runaware`)

Status: design only. `best/` is untouched; this package starts as a copy of `best`
(+ `NodeChoice`, which exposes σ, m, n, f, b of every node network: `AKS/Chvatal/RealNets.lean`).

## 1. Idea

A big node runs `physicalPackNet`: sort columns, scramble rows, sort columns again
(`PhysicalPack.lean`). Its input is not arbitrary: it is the previous stage's output, and every
semantic column of a previous separator node is exactly sorted. What a node receives is therefore a
union of sorted **runs** (consecutive rows of one semantic column: the parent's `b`-row blocks, the
children's `f`-row fringes). If every aligned block of `2^s` rows of each input column is
sorted, the first column sort can skip its first `s` merge levels:

    depth(first sort) = T(L) - T(s)        (T(p) = p(p+1)/2, L = clog2 m = 59 / 58)

Proven in scratch (`scratch/runaware/Block5.lean`, builds, standard axioms only):
`bitonicBlockSort`, `bitonicBlockNetwork` (any n), `blockColumnSortNetwork_exec_eq`,
`physicalPackNetBlock_exec : ColumnsBlockMono s m n hn v → (physicalPackNetBlock s m n hn σ).exec v = (physicalPackNet m n hn σ).exec v`,
`physicalPackNetBlock_depth_le`. Since exec is equal on block-sorted inputs, every downstream
guarantee (`packSpec_*`, `NodeSpec`, `packNodeSpec`) is reused verbatim on that domain.

## 2. Payoff (measured on the real flow table, d = 14 … 30; `scratch/run_check2.py`)

Only the 2-adic valuation of the run lengths is usable (`b = 2^29·(2^24-1)`-type values, not
powers of two). Over the large-node stages the saving per stage is

| scheme | saving per big stage | slope |
|---|---|---|
| uniform `s = 29` (binding node type, all `d`) | `T(29) = 435` of 3540 (12.3%) | 1770 → **~1553** |
| stage-dependent `s` (435 / 561 / 465 / 820 …) | avg ≈ 500–560 in the steady state | ≈ 1500–1520 |
| ideal merge tree of the actual runs (greedy model, unequal-length merge) | first sort 1209 instead of 1770 | ceiling ≈ 1490 |

So the realistic gain is **−12% (to ≈ 1553)**, with a ceiling of about −16%. Earlier estimates
(−23% average, 1100–1300 after stacking) overcounted: they used the tail/root stages and assumed
the run lengths were powers of two. Recommendation: target the uniform `s = 29` (no per-stage
schedule, depth bound `depthBound t = 3540 - 435 = 3105` for big non-root stages).

## 3. Why a placement change is needed

The proof places a node's cell `k` on the `k`-th smallest wire of its wire set `S` (`stageNet`,
`orderEmbOfFin`). The previous node's output is physical = semantic ∘ `rowScrambleWirePerm`, so a
sorted semantic column is spread across physical columns, and sources interleave by wire index. A
row-preserving relabelling cannot fix this: the second sort must leave outputs on the standard
row-major cells (`NodeSpec` is stated in those positions), which forces any relabelling of the
first sort to be row-monotone, i.e. a permutation within rows only. Runs live in different rows, so
we need a genuine inter-stage wire permutation.

## 4. Architecture (smallest change found)

Keep every wire **set** exactly as now (`wireSets`, `parentPart`, `childPart`, `upSet`, `downSet`:
all set/cardinality statements, `execPlacement_succ_regs`, `stage_preserves_node_keys`,
`wireSets_inv` stay as they are). Insert a free permutation `Π_t` of the wires **between** stages,
with `Π_t` preserving every incoming node set `U_b = parentPart ∪ childPart` setwise:

    X (t+1) = stage_t.exec (X t ∘ Π_{t-1})      -- local input vector of node q: i ↦ X t (Π (orderEmb i))

Because `Π_t` permutes inside each `U_b`, every statement about *sets of keys on a node* is
unchanged (`image_X_Π`); only the local input vector `xr` is permuted inside the node. `NodeSpec`
is quantified over all input permutations, so `NodeKeys`/`BadSendReal`/`FringeSendReal` only need
`xr` injective with `keySet xr = K` (confirmed by the scoping read). Concretely:

* **W1 (done)** σ, m, n, f, b readable per node: `nodeChoice`, `nodeChoice_pack`.
* **W2 execution with Π.** `X` takes the family `Π : ℕ → Equiv.Perm (Fin (64^d))` with
  `Π_t` preserving each `wireSets F t b` (`PiOK`); adapt `X_succ_inside`, `X_eq_comp_perm`,
  `stage_preserves_node_keys` and the `xr` construction sites (ExecPlacement, BadSendReal,
  FringeSendReal, NodeKeys). Pure refactor with `Π = 1` recovering the current statements.
* **W3 network assembly.** The stage comparators of stage `t` must sit on the *relabelled* wires.
  Build the whole network as an `Untangle.GenNetwork` (stage `t` conjugated by the cumulative
  permutation), prove exec/depth of the conjugation (`relabelNet`-style for `GenNetwork`) and finish
  with `Untangle.untangle` as `FinalSorts` already does for the last blocks. Depth is unchanged by
  conjugation (`untangle_depth`), additive over stages.
* **W4 chunk invariant (the new mathematics).** For every node and stage, the output wires of every
  semantic column are monotone in `X`: define `SortedChunks` on wire sequences; prove it for
  separator output (`physicalPackNet_exec` + sortedness of `semanticExec` columns), for small nodes
  (`bitonicNetwork_sorts`: whole node sorted), for pass-through nodes (no comparators: chunks
  inherited). The pieces sent (`upSet`: first/last `π/2` cells, `downSet`: block `j`) are unions of
  `2^29`-aligned sub-chunks because every `f`, `b`, `up/2` of a large node, small-source `up/2` and
  `down` is divisible by `2^29` (**to be proved from `NodeGeom` templates and `flowSizes7`;**
  measured minimum over d = 14…30 is exactly `v2 = 29`, e.g. `b = 2^29(2^24-1)`. Caution: the Lean
  geometry scale `r` (template `f = 4095·2^r`, `b = 128R·2^r`, `m = (8192R+8190)·2^r`) is chosen by
  `exists_pow_scale` and may differ from the largest-`n` choice used in the model, so `v2` may be
  as low as ~21 for some `d`; fix `r` canonically in `NodeGeom` if needed. Slope for `s = 22`: ≈1643).
* **W5 choice of `Π_t`.** From the chunk structure, produce `Π_t` (Classical existence is enough:
  `Π_t` is a static, input-independent permutation of the *positions* of chunks) such that the
  local input vector of every big node satisfies `ColumnsBlockMono 29 m n`: arrange the `2^29`-chunks
  of the sources into `(row-block, column)` slots (counting: `m n / 2^29` chunks, `2^29 | m`).
* **W6 switch the networks and the depth bound.** `NodeChoice.net` for packs uses
  `physicalPackNetBlock 29`; `realNets_depth_le` uses `bitonicDepthBudget` difference giving
  `depthBound t = 3105` for `t ≥ 1` big nodes (root keeps `6320`, small nodes `2016`); `totalDepth`
  becomes `6320 + (3d-21)·3105 + 903` (modulo the tail stages, which keep small nodes only);
  headline `D(n) ≤ 1553·lg n − c`.

## 5. Obstacles / risks (from the scoping read)

* Small-bag nodes (`a ≤ 2^63`) keep full sorts; they are fine as *sources* (their `up/2`, `down`
  are multiples of `2^29` for all big-node parents — to be proved) but not changed.
* Pass-through nodes (`down = 0`): keys do not move, chunk structure inherited through chains.
* The root (t = 0, arbitrary input) keeps the full first sort.
* `Π_t` must also respect the Untangle direction conventions (min to the lower *physical* wire)
  when assembling the final network.
* Scale: ≈ 1500–3000 lines over ExecPlacement, NodeKeys, BadSendReal, FringeSendReal, RealNets,
  RealNetwork, FinalSorts, DepthSkeleton plus 2–3 new modules (block sorter promotion, chunk
  invariant, Π construction).

## 6. Order of work / checkpoints

1. W3-prototype in scratch: conjugated `GenNetwork` stage composition + untangle lemma (small, de-risks the network side).
2. v2 lower bound: `2^29 ∣ f, b` (large nodes), `2^29 ∣ up/2, down` (small sources) from `NodeGeom`/`flowSizes7` for all `d ≥ 14` (also decides 29 vs 22).
3. W4 chunk invariant for one node type (large with large children) in scratch.
4. W2 refactor with `Π = 1` (green build, no statement changes), then W5/W6.
Promotion rule: nothing moves to `upper-bound/best` until the full package builds with the axioms
guard and the headline theorem is restated with the new constant.
