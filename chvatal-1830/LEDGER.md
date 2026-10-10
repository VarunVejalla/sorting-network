# chvatal-1830: modular ledger (completed 2026-10-07)

Every row below is kernel-checked (✔) except where a row says otherwise; this is the record of how the proof was
built, kept for reference (see `README.md` for the proof map).

Reference: `docs/dcs-tr-294.pdf` (text extraction is garbled; decode `/NN` tokens as
ASCII, low codes are cmmi Greek: 11 α, 14 δ, 15 ε, 22 ν, 25 π, 27 σ, 31 τ, 33 ω).
**Rule: follow the paper's proof structure.** Kernel-checked = ✔. `[me]` needs
careful analysis; `[delegate]` is mechanical once statements are fixed. Delegated
(Haiku) output has repeatedly contained `sorry`s or `rfl` tautologies reported as
success: always rebuild, `grep sorry`, and `#print axioms` before trusting it.

**Audit of the abstract model vs. the paper.** The `Placement`/`perm` model is
faithful if a Lean "register" is a *key* identified by its initial index, `perm` is
its address (the input rank map), and the placement is data-dependent; then
`perms (t+1) = perms t` is correct. The paper's wire sets of nodes are
input-independent (wires stay put, keys move). The final 2^42 blocks are made
contiguous by one global relabeling of the wires (inputs are arbitrary). The
constant `58657` matches the paper's Theorem 1.1 (`N ≥ 2^78`).

### A. Separators for every bag size (paper §5–6)

| # | Piece | Status |
| --- | --- | --- |
| A1 | Property B for general `n`: **✔** `lemma61FailBound_onPipeline` is already general in `(m,n)`; used in `ExistsScrambleSeparator_general` | ✔ |
| A2 | Claim (ii): tops counting + binomial estimates ([Lemma62TopsCount](AKS/Chvatal/Lemma62TopsCount.lean), [Lemma62TopsAnalytic](AKS/Chvatal/Lemma62TopsAnalytic.lean)) | ✔ |
| A3 | Two-sided geometric tail sum ([GeomTail](AKS/Chvatal/GeomTail.lean)) | ✔ |
| A4 | Per-`s` tail and ratio bounds: **✔** `p(s) ≤ C(n,s)(e j s/(nT))^T` ([Lemma62Tail](AKS/Chvatal/Lemma62Tail.lean)); `key_right`, `ratio_left/right`, `gfun_sum_le_G1` (`Σ_{s≤n} g(s) ≤ (1+e^-5)/(1-e^-5) G1(b)`) and `pbound_le_gfun` ([Lemma62Ratio](AKS/Chvatal/Lemma62Ratio.lean)), for `n ≥ 16`, `f ≥ 1.7e10`, `j ≤ (128/4095) f n`; integrality of `ε_F j` and evenness of `f` not needed | ✔ |
| A5 | Event-E bound per `E`: **✔** `fail_prob_at_E` (`|badSetF j| ≤ 1.025 (3/10)^E |Scramble|`, [Lemma62FailE](AKS/Chvatal/Lemma62FailE.lean)) from the tops reduction ([Lemma62FailReduce](AKS/Chvatal/Lemma62FailReduce.lean)), the closed tops count, the tail sum (incl. `⌊2εj/f⌋ = 0`) and `x ≤ 3/10` | ✔ |
| A6 | Rigorous `x ≤ 1/4 ≤ 3/10` for all `j` (`xval_le_three_tenths`, [Lemma62Numerics](AKS/Chvatal/Lemma62Numerics.lean); `n` cancels via `u = j/(fn)`) | ✔ |
| A7 | Assembly: **✔** (2026-10-07). Corrected `HasPaperPropertyF` (tie `totalColumnOnes c = j`; the old `HasCombinatorialPropertyF` was false for every `σ` once `m ≥ f+1`), rounding to multiples of `1/ε` and summing `E ≥ 1` (fail fraction `≤ 0.44`, [Lemma62Round](AKS/Chvatal/Lemma62Round.lean)), corrected F-bridge to the pack ([Lemma62Bridge](AKS/Chvatal/Lemma62Bridge.lean)), pigeonhole with pipeline B (`< 1/100`): `ExistsScrambleSeparator_general` ([GeneralSeparator](AKS/Chvatal/GeneralSeparator.lean)) for every `ScrambleGeometry` with `f ≥ 1.7e10`, `δ_F ≤ 128/4095`, `ε_F ≥ 1/(8e7)`. Still needed to *use* it: build `Theorem51Params g` for each `g` (A8: `ε_F` floors, `4e/f`, `ε_B` bound) | ✔ |
| A8 | `Theorem51Params g` for every geometry: **✔** ([GeneralParams](AKS/Chvatal/GeneralParams.lean)): `epsF_floor_general`, `four_e_div_le`, `epsB_general` (`m ≥ 2^59`), `epsB_root_general` (`m ≥ 2^79`), `theorem51Params_general`, `ExistsScrambleSeparator_ordinary/_root` | ✔ |
| A9 | Scaling a template into `m ∈ (2^59, 2^60]` with `f > 1.7e10`, even ([GeometryScale](AKS/Chvatal/GeometryScale.lean)) | ✔ |
| A10 | The four paper templates (§5) are not needed: node geometries come from `nodeGeom_exists` ([NodeGeom](AKS/Chvatal/NodeGeom.lean)) | not needed |
| A11 | Small bags: `bitonicNetwork a` meets `NodeSpec` by sortedness (`NodeSpec_of_sorts`, [RealNets](AKS/Chvatal/RealNets.lean)) | ✔ |
| A13 | Two-sided Property B/F: **✔** ([FlipSpec](AKS/Chvatal/FlipSpec.lean)): `flipScramble` (involution), `semanticExec_flip`, `physicalPackNet_flip`, `packSpec_low`, `exists_twoSided_pipelineB_paperF`/`_B`, `ExistsScrambleSeparator_twoSided`/`_B` (failure fractions `2·(0.01+0.44) = 0.90 < 1`) | ✔ |
| A12 | Root separator (`m = 2^79`, root `ε_B`) for general `n`: **✔** `ExistsScrambleSeparator_root` | ✔ |

### B. The actual network (paper §3, §4)

| # | Piece | Status |
| --- | --- | --- |
| B1 | Integer flow table `flowUp`/`flowDown` over the rational scheduler, with the send identity `a = π + kτ` (`allocation_eq_flowUp_add_flowDown`, [FlowTable](AKS/Chvatal/FlowTable.lean)); table confirmed against the paper by the author (pp. 7–9) and by exact Python checks for `d = 14, 15, 20, 30` | ✔ |
| B2 | Flow table: send identity (`t+1 ≤ t_f`), conservation, instantiation for `levelSchedule7`, and natural-number sizes `flowSizes7 d hd : FlowSizes d (tf7 d)` ([FlowSizes7](AKS/Chvatal/FlowSizes7.lean); integrality, evenness of `up`, the `t = 0, 1` special steps). Corrections found while proving: rising-top exponent is `e ≥ 6` (not 8), `τ` interior is `c(2^24−1)/2^30` | ✔ |
| M2′ | **Resolved (2026-10-07).** Paper (4.2) ends with `μδAk/ν` (author-confirmed; (4.5) matches Lean). Lean's `Cond42` had `μδ/(Akν)`, assuming a fair-density send-up. Fixed: `Cond42`, `cond42_coeff_form`, `cond42_scaled`, `lemma43_of_sources` and the order-0 children bound in `StageKernel`/`PlacementStep`/`RoutingFromP`/`StageDynamics`/`SeparatorContract` now use the worst case `μ δ k A² c(l−1,t)`; the old fair-density derivation (`fromChildren0_of_cover`) is weakened to it. `cond42_params7` and the paper-ordinary version still hold (exact check: `LHS/μ = 0.960` at `ε_B = 1.25e-8`). Consequence: the real network only has to supply `fromChildren ⊆ ⋃ child registers` (children part) and the parent-side Property B/F bounds (B7) — no goods-first rule or `c/Q` send budget | ✔ |
| B3 | Wire sets over time: **✔** ([WireFlow](AKS/Chvatal/WireFlow.lean)). `wireSets F t` from any `FlowSizes F` (sorted-order splitting: first/last `up/2` positions go up, middle cut into 64 blocks), with `wireSets_card`, `wireSets_disjoint`, `wireSets_complete`, `wirePlacement`, and the destination characterisation `mem_wireSets_succ` | ✔ |
| B4 | Wire sets need not be contiguous at `t_f`: use generalized comparators and **✔ `Untangle.untangle`** ([Untangle](AKS/Sort/Untangle.lean): a generalized network sorting into any fixed output order τ yields a standard network of equal greedy depth that sorts; supersedes the depth-`k` `KnownPermutation` correction). Remaining: generalized-network versions of the stage nets (embedding packs along arbitrary bijections) | partly ✔ `[me]` |
| B5a | `physicalPackNet`: standard network realizing the sort–scramble–sort pack on a node's wires (second column sort relabeled through the scramble); `physicalPackNet_exec` (= semantic output ∘ `wirePerm`), row-region counts agree, depth `≤ 2·bitonicDepthBudget` ([PhysicalPack](AKS/Chvatal/PhysicalPack.lean)) | ✔ |
| B5b | `stageNet`: heterogeneous node networks on sorted wire lists, `stageNet_exec_inside`, `stageNet_outside`, `stageNet_depth_le` ([StageNet](AKS/Chvatal/StageNet.lean)) | ✔ |
| B5c | Per-node networks `realNets` (bitonic for small bags; physical pack with the chosen two-sided σ for `a > 2^64`; root `m = 2^79` geometry at `t = 0`; empty when `down = 0`), `realNets_specs : RealSpecs`, `realNets_depth_le` (3660 for `t ≥ 1`, 6320 at `t = 0`) ([RealNets](AKS/Chvatal/RealNets.lean)). **Open:** the full network `stages 0..t_f−1 ++ final sorters` and its total depth `≤ totalDepth d` (C3) | partly ✔ |
| B6 | Execution-defined placement: **✔** ([ExecPlacement](AKS/Chvatal/ExecPlacement.lean)): `X v t`, `execPlacement` (keys on each node's wires), `fromParentK`/`fromChildrenK`, `execPlacement_succ_regs`, `stage_preserves_node_keys`, `fromChildrenK_subset`, cell/key dictionary `mem_image_downSet_iff`/`_upSet_iff` | ✔ |
| B7a | Lemma 4.1/4.2 counting: **✔** pure window counting (`BlockWindow` (archived); `rankIn` renamed `rankNat`), real Lemma 4.1 `keys_below_child_le` ([Lemma41Real](AKS/Chvatal/Lemma41Real.lean)), scalar §7 facts `total_mass`, `hwires7_real` (Lemma 3.1), per-type `τ`/`π`, `slack_*` ([Wires31](AKS/Chvatal/Wires31.lean)) | ✔ |
| B7b | Real parent/children sends: **✔** `bad_send0_real` ([BadSendReal](AKS/Chvatal/BadSendReal.lean): `(b.strangers 1 (fromParentK b)) ≤ (q.strangers 1 K) + 63ρ − π/2 + 2·EB` given `hM`, `hpos`, the node spec; it carries a private copy `BW` of the window lemma that can now be replaced by the `BlockWindow` import), `fringe_send_real` ([FringeSendReal](AKS/Chvatal/FringeSendReal.lean)), children bounds `hFromChildren0/R_of_subset` ([StrangerBounds](AKS/Chvatal/StrangerBounds.lean)), `NodeSpec` ⇒ key counts ([NodeKeys](AKS/Chvatal/NodeKeys.lean)) | ✔ |
| B7c | `StageKernel` for the real network, `t ≥ 1`: **✔** ([RealKernel](AKS/Chvatal/RealKernel.lean): `realStageKernel`, `realStep`; fields `badSendField_real` ([BadSendField](AKS/Chvatal/BadSendField.lean)), `fringeSendField_real` ([FringeSendField](AKS/Chvatal/FringeSendField.lean)); `KernelSetup` has `invariantReal` with `μ = (1−2^-10)·2^-30`, all (4.1)–(4.5) incl. the true (4.4), and `RealSpecs`) | ✔ |
| B8 | Induction: **✔** ([RealInduction](AKS/Chvatal/RealInduction.lean): `P_zero`, `P_one` (exceptional root separator), `P_all`, `real_purity`) and the combined statement `realNets_purity` ([RealPurity](AKS/Chvatal/RealPurity.lean)): for `d ≥ 14` and every input permutation `v`, after `t_f` stages of `realNets` every level-`(d−6)` bag has no order-2 strangers | ✔ |

### C. Assembly

| # | Piece | Status |
| --- | --- | --- |
| C1 | Monotone parallel final on rank-pure input (`FinalPurity`, superseded by C2–C3 below; archived in `../archive/chvatal-scaffolding`) | superseded |
| C2 | Rank-pure blocks at `t_f`: `finalS`, `finalS_card/disjoint/cover`, `finalS_image(_real)` — the keys on a level-`(d−7)` block's wires are exactly its address interval ([RealBlocks](AKS/Chvatal/RealBlocks.lean)) | ✔ |
| C3a | Full network: `stagesNet` (`stagesNet_exec = X`), `finalLayer` ([RealNetwork](AKS/Chvatal/RealNetwork.lean)) | ✔ |
| C3b | Final layer sorts into a fixed output order and untangles: `final_layer_sorts` ([FinalSorts](AKS/Chvatal/FinalSorts.lean)) | ✔ |
| C3c | Permutations ⇒ all inputs (`exists_sorting_perm`) and `Untangle.untangle`, inside `final_layer_sorts` | ✔ |
| C3d | Depth `≤ totalDepth d` (`fullNet_depth_le`; reproved inline in `chvatal_sorter_exists`) | ✔ |
| C3e | `Chvatal.chvatal_sorter_exists`: for every `d ≥ 14` a sorting network on `64^d` wires of depth `≤ totalDepth d` ([RealSorter](AKS/Chvatal/RealSorter.lean)); `SortingDepth.limsup_minimum_div_logb_le_1830` (unconditional, [Chvatal1830Final](AKS/Bounds/Chvatal1830Final.lean)). Axioms: propext, Classical.choice, Quot.sound only | ✔ |
| C4 | Pointwise bound: `SortingDepth.minimum_depth_le_1830_logb` (`D(n) ≤ 1830·log₂ n − 58657` for every `n ≥ 64^7`; Batcher for `clog 64 n ≤ 603`, `chvatal_sorter_exists` beyond, both restricted to `n` wires) and `eventually_minimum_depth_le_1830_logb` ([Chvatal1830Final](AKS/Bounds/Chvatal1830Final.lean)) | ✔ |

Dependency order: `A → B3/B5 → B6 → B7 → B8 → C2 → C3 → C4`.
