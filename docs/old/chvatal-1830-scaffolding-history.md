# Chvátal 1830: scaffolding-era history (archived 2026-10-07)

Moved verbatim from `docs/research-index.md` ("Current research directions"). It describes the
abstract route (`AbstractChildSendTrajectory`, `Sorting1830Obligation`, d = 7 Batcher assemblies,
paper depth-shell networks) that was superseded by the real execution-defined network. The files
it names are archived under `archive/chvatal-scaffolding/` or live in `chvatal-1830/`.

- Chvátal 1830 track (Phase 0 + Phase 1 §3 + §4 algebra + §5–§6 scaffolding;
  reference `docs/dcs-tr-294.pdf`, untracked Rutgers DCS-TR-294). **Kernel-checked
  unless noted.** [DepthSkeleton](../AKS/Chvatal/DepthSkeleton.lean): §7 depth
  accounting (`totalDepth`, padded `1830 log₂ n − 58657`), numeric (4.1)–(4.5),
  (7.1)–(7.2), `δF ≤ 1/25`; [SkeletonAxioms](../AKS/Chvatal/SkeletonAxioms.lean)
  standard axioms only. §3–§4 bag/scheduler/outsider chain through
  [ChildSend](../AKS/Chvatal/ChildSend.lean),
  [AbstractPlacement](../AKS/Chvatal/AbstractPlacement.lean) (`preferNon`
  children-send, **`ChildRegisterCapacityLower`** when child regs nonempty,
  `PreferNonStageChildrenData.fromParent_empty` / `rootStage_fromParent_empty`,
  support=abstract cover, `StageKernelWithChildren.ofAbstractChildSend`,
  root init `P`), [Schedule7](../AKS/Chvatal/Schedule7.lean) (`levelSchedule7`,
  purity envelope, Lemma 3.2 without snap), [Params](../AKS/Chvatal/Params.lean)
  `SeparatorConds` at `params7`. §5–§6: [PropertyBF](../AKS/Chvatal/PropertyBF.lean),
  [Theorem51](../AKS/Chvatal/Theorem51.lean) (statement + routing bridge),
  [Lemma61](../AKS/Chvatal/Lemma61.lean) / [Lemma63](../AKS/Chvatal/Lemma63.lean)
  (Chernoff cores; **paper** combinatorial B is `HasCombinatorialPropertyB` ∀ monotone `c`;
  **pipeline** B is `HasCombinatorialPropertyBOnPipeline` with `TotalColumnOnesLeLevel m n i c`
  (`totalColumnOnes c ≤ n·i`). Module A fail-bound for B uses
  `DecodeMatrixClassObligation` / `lemma61FailBound_onPipeline_of_decodeClass`, not global
  `TotalColumnOnesLeN`),
  [Lemma62](../AKS/Chvatal/Lemma62.lean) / [Lemma62Chernoff](../AKS/Chvatal/Lemma62Chernoff.lean):
  fringe MGF/Chernoff, `Lemma62FringeCellBound.of_hyp`; **cell counting for F is
  kernel-checked under** `FringeOnesDensityLeHalfWidth` (hence under global
  `TotalColumnOnesLeN` / `AvgRowOnesLeOne` via `FringeOnesDensityLeHalfWidth_of_totalColumnOnesLeN`) plus
  per-cell `hepsCell` and numeric `hclose` in
  `Lemma62CellCountingObligation` / `ModuleACombinatorialObligation`.
  [ModuleA](../AKS/Chvatal/ModuleA.lean) packages combinatorial B/F; at **`m = 100`, `n = 16`**
  kernel-checked **`ExistsCombinatorialPropertyBOnPipeline_of_decodeClass_m100`** /
  **`exists_combinatorialScrambleBF_onPipeline_of_ModuleA_m100`** (no `AvgRowOnesLeOne` on B).
  F-side cell counting still uses **`AvgRowOnesLeOne`** (fringe density).   [MatrixBridge](../AKS/Chvatal/MatrixBridge.lean): sort–scramble–sort
  skeleton, wire layout, combinatorial→matrix wiring into `Theorem51Obligation`;
  **B-side (kernel-checked, general `m`,`n`):** Thm 5.1 witnesses use
  `SemanticSeparator` / `ScrambleSeparatorWitness` with **semantic** matrix
  properties (`HasPackSemanticPropertyB` / `HasMatrixPropertyB_exec` on
  `pack.semanticExec`; `pack.net` still ignores `wirePerm`). Kernel-checked:
  `MiddleStageDecodeHyp.of_idealColumnSort_rowScramble`,
  `packSemanticIntrusionCountB_eq_onesAboveBottom` /
  `matrixIntrusionCountB_semantic_eq_onesAboveBottom` in
  [SortedColumnDecode](../AKS/Chvatal/SortedColumnDecode.lean); canonical pack
  `canonicalSortScrambleSortPack` (`columnSortNetwork` + `rowScrambleNetwork`) via
  `HasPackSemanticPropertyB_canonical_of_combinatorial` /
  `HasPackSemanticPropertyB_canonical_of_combinatorial_onPipeline` /
  `combinatorialPropertyB_onPipeline_implies_matrixB_exec_canonical`;
  `CombinatorialToMatrixObligationB.of_columnSortNetwork_rowScramble` when universal
  `IdealColumnSort` + `RowScrambleCorrect` hold;
  `MatrixBridgeBResidual.of_columnSortNetwork_rowScramble_discharged` packages the B-bridge.
  **F-side (kernel-checked, 2026-10-05):** `MiddleStageFringeDecodeHyp.of_idealColumnSort_rowScramble`,
  `packSemanticIntrusionCountF_eq_onesAboveBottom`,
  **`FringePropertyFClosingHyp.of_idealColumnSort_rowScramble`** (semantic `< ε_F·j` via top-`j`
  column totals and `j < f` from **`δ_F·n < 1`**, not a direct combinatorial-F Chernoff step),
  **`CombinatorialToMatrixObligationF.of_columnSortNetwork_rowScramble`**, and full
  **`CombinatorialToMatrixObligation.of_columnSortNetwork_rowScramble`** (B + F) when universal
  `IdealColumnSort` + `RowScrambleCorrect`, `0 < f`, `0 < ε_F`, and `δ_F·n < 1` hold
  (`deltaF_mul_n_lt_one_params7_n16` for §7 at `n = 16`).
  `ModuleACombinatorialObligation.of_params7_m100_n16` / **`of_params7Geometry_m100_n16`**
  (B/F counting bundle given `hepsB`, `havg`, `hepsWorst`; **`hf2` / `hmF` / `hjMax48`**
  discharged on any `params7Geometry` shape via [ModuleANumerics](../AKS/Chvatal/ModuleANumerics.lean);
  §7 `hclose` at `m=100`,`n=16` still via
  `lemma62_cellUnionFactor_le_failFactor_thirty_m100_n16` when `jMax ≤ 48`).
  §7 endpoint
  [Bound1830](../AKS/Chvatal/Bound1830.lean): `AbstractChildSendTrajectory` +
  outsider induction, `params7_purity_of_abstract`, `Sorting1830Obligation`
  bundle, **`network_depth_le_1830_of_sorting1830Obligation`** (hypothesis-dependent).
  **`FinalSorterDepthBudget.of_batcher42` discharged** (`bitonicSort 42`, depth
  `≤ 903`).   **`NetworkDepthAssemblyObligation`**: root++ordinary×`(tf−1)`++final
  with **`depth_le_totalDepth` kernel-checked** from append-depth lemmas +
  `StageDepthBudget`; **`assembledChvatalNetwork_sorts` /
  `of_stage_sorts`** discharge assembled `Sorts` once each stage net sorts.
  **[StageAssembly](../AKS/Chvatal/StageAssembly.lean) (2026-10-05):** executable
  `chvatalEmptyStageNet` / `chvatalFinalBatcherNet` on `64^d`; empty root+ordinary
  assembly lemmas; **`NetworkDepthAssemblyObligation.of_batcher903_emptySeparators_d7`**
  — kernel-checked **`Sorts`**, **`StageDepthBudget.ofPaper`**, and
  **`composed = chvatalFinalBatcherNet 7`** (honest separator placeholders; real
  **6320 / 3660** stage nets still open). Trajectory
  packaging: **`PreferNonStageChildrenData`** (kernel-checked preferNon
  children-send; **`fromParent_empty`**) + **`AbstractParentResidueRouting`**
  (Thm 5.1 bad-send/fringe Finset bounds; **`AbstractParentResidueRouting.of_residue`**
  / **`of_stageRoutingResidue`**, **`AbstractParentResidueRouting.of_emptyFromParent`**
  for zero parent send-up with explicit budget nonnegativity, **`PreferNonStageObligation.routing_of_residue`**) ⇒
  **`PreferNonStageObligation`** / **`Params7AbstractTrajectoryRoutingObligation`** /
  **`Params7AbstractTrajectory.of_routingObligation`** (with **`outsiderBoundLe_tf`**
  / **`purity_at_meet`** corollaries).
  **[Schedule7Trajectory](../AKS/Chvatal/Schedule7Trajectory.lean) (2026-10-06):**
  `capacity_le_nativeCard_params7`, `ChildRegisterCapacityLower.of_ladderNative_params7`,
  **`Params7PreferNonStageRoutingObligation.rootStage`** (any `d`; stationary empty
  `fromParent`) / **`rootStage7`**, **`Params7AbstractTrajectoryRoutingObligation.stationaryRoot`**
  for all `d ≥ 7`,
  **`AbstractParentResidueRouting.of_zeroStrangersFromParent`** (generalizes empty send-up),
  **`level1NativePlacement`** / **`nativeLevel1FromParent`** (nonempty for level-1 bags),
  **`Params7PreferNonStageRoutingObligation.nativeRootSplit`** (root→level-1 evolving stage;
  zero-stranger sends meet Thm 5.1 / paper-ordinary quality budgets),
  **`nativeLevel1Stay`**, full evolving
  **`Params7AbstractTrajectoryRoutingObligation.nativeLevel1`** for `d ≥ 7`
  (`d = 7` has `tf = 1`, so the split alone completes the schedule;
  **`nativeLevel1_d7`**),
  `ScrambleSeparatorBagLink` / `parentSeparatorQuality_params7` (hypothesis-level
  `ExistsScrambleSeparator` → bag `LocalSeparatorQuality`, not wire `fromParent` yet).
  **Schedule split:** `moduleA_invariantF16`, `ScrambleSeparatorModuleABagLink`,
  `not_scrambleSeparatorBagLink_invariant7_of_moduleA_f16` (Module A `P` cannot use
  `invariant7` scalars in `ScrambleSeparatorBagLink`).
  Open: wire-level separator→`fromParent` Finsets from scramble nets (native/identity
  sends are quality-compatible but not separator-net-derived); deeper ladder capacity
  on nonempty child bags beyond level 1; real root/ordinary separator nets (not only
  **`Sorting1830Obligation.of_routingAssembly_d7`**
  in [StageAssembly](../AKS/Chvatal/StageAssembly.lean): empty root/ordinary + Batcher,
  net **`= chvatalFinalBatcherNet 7`**, depth still hypothesis-dependent on trajectory).
  **`Sorting1830Obligation.d7_batcher_paperOrdinary_nativeLevel1`**: Batcher assembly +
  evolving native PreferNon + paper-ordinary residual (kernel-checked).
  **`Sorting1830Obligation.of_routingAssembly`** bundles routing trajectory + separator + assembly.
  Matrix bridge progress:
  wire/count lemmas, `RowScrambleCorrect`, Bool column-local region counts
  (`ColumnOnesRegion`), marking under `KeysAreWireIndices`; kernel-checked
  `IdealColumnSort` for `columnSortNetwork` and column wire/bitonic bridge in
  `MatrixBridge`.   **`SortedColumnDecode.lean`:** kernel-checked semantic B/F decode, F closing, and
  `CombinatorialToMatrixObligation.of_columnSortNetwork_rowScramble` (see F-side above).
  **`RowScramble.lean`:** `RowScrambleCorrect` kernel-checked for general `n` via
  `of_rowScrambleNetwork` (wired middle stage + ideal column sort).
  **§7 separator instantiation (2026-10-06):** [Theorem51Core](../AKS/Chvatal/Theorem51Core.lean)
  `params7Geometry` / `params7Geometry_f16` / `theorem51Params7`; [Lemma62](../AKS/Chvatal/Lemma62.lean)
  `fringeRowCount_eq`, **`fringeRowCount_m100_f16`** (`m−f/2 = 92`), **`lemma62_jMax_params7_f16_le_48`**;
  [ModuleANumerics](../AKS/Chvatal/ModuleANumerics.lean) shape lemmas and residual bundle
  **`ModuleAParams7_f16Residual`**. [ModuleA](../AKS/Chvatal/ModuleA.lean):
  **`ExistsScrambleSeparator_params7Geometry_m100_n16`** — same conclusion as
  **`ExistsScrambleSeparator_params7_m100_n16`** but **`hPeps`**, **`hf2`**, **`hmF`**,
  **`hjMax48`**, **`hfm`**, **`hfpos`** kernel-discharged when `P = theorem51Params7 …`;
  **`ExistsScrambleSeparator_params7Geometry_f16_residual`** packages the fixed `f = 16`
  witness. Legacy entry points **`ExistsScrambleSeparator_params7_m100_n16`** /
  **`ExistsScrambleSeparator_params7Geometry_f16`** / **`Theorem51Obligation_params7_m100_n16`**
  still list the full hypothesis list for callers that do not use the geometry lemma.
  All combine `ModuleACombinatorialObligation`, universal `rowScrambleNetwork_all`, and
  **`CombinatorialToMatrixObligation.of_params7_m100_n16_bridge`**
  ([SortedColumnDecode](../AKS/Chvatal/SortedColumnDecode.lean); **`deltaF_mul_n_lt_one_params7_n16`**
  kernel-checked).   Pipeline (decode class): combinatorial→matrix lemmas in **`MatrixBridge`** /
  **`SortedColumnDecode`**; §7 separator entry points in **`ModuleABridge`** (needs **`g.m = 100`**, **`g.n = 16`**).
  Global **`ExistsCombinatorialPropertyB`** still needs **`HasCombinatorialPropertyB.imp_onPipeline`**
  plus unrestricted B (legacy **`Lemma61FailBoundObligation`** + **`havg`**) if one insists on paper ∀`c`.

  **§7 paper-scale scramble (DCS-TR-294 §7, not `m = 100` minima):** [Theorem51Core](../AKS/Chvatal/Theorem51Core.lean)
  **`paperOrdinaryGeometry`** (`m = 2^60`, `n = 16`, `f = 2^58`, `k = 1`, `b = 2^59`), **`paperOrdinaryGeometry_m2p59p1`**
  (`m = 2^59+1`, `b = 1`), **`paperRootGeometry`** (`m = 2^79`, `f = 2^78`); paper **`ε_B`**
  via **`paperOrdinaryEpsB`** / **`paperRootEpsB`** (not **`invariant7.epsB`**). [PaperScrambleNumerics](../AKS/Chvatal/PaperScrambleNumerics.lean)
  (kernel-checked): Chernoff **`chernoff_hepsB paperOrdinaryM ≤ paperOrdinaryEpsB`**, root analogue,
  **`not_chernoff_hepsB_le_invariant7_at_paperOrdinaryM`**, **`paperOrdinary_hepsF_ge_4e`** at `f = 2^58`,
  **`paperRoot_hepsF_ge_4e`** at `f = 2^78`,
  **`PaperOrdinary_epsF_lemma62_Certificate`** / **`paperOrdinary_epsF_lemma62_lb_le_invariant7`**,
  **`PaperRoot_epsF_lemma62_Certificate`** / **`paperRoot_epsF_lemma62_lb_le_invariant7`**, and
  **`theorem51Params_paperOrdinaryGeometry_discharged`** / **`theorem51Params_paperRootGeometry_discharged`**
  (full Thm 5.1 `P` at paper ordinary/root geometry with `invariant7` `δ_F`/`ε_F`). Fringe Chernoff **`hepsWorst`**: **kernel-checked impossible** at
  `invariant7.epsF` — **`not_paperOrdinary_hepsWorst_le_invariant7_epsF`** (scale **`≳ 10^10 × epsF`**, i.e.
  **`paperOrdinary_hepsWorst > 125`** vs **`epsF = 1/80000000`**; numeric order **`≈ 7×10^10` vs `1.25×10^-8`**).
  **`paperOrdinary_lemma62_jMax_gt_48`**: `jMax` at `(f,n) = (2^58,16)` is **`≫ 48`** (not the `m=100` regime).
  **`PaperOrdinary_hclose_residual`**: cell-union **`hclose`** packaged as an open Prop (numerically false at paper scale).
  **`SortedColumnDecode`**: **`CombinatorialToMatrixObligation.of_invariant7_geometry_bridge`** for any
  **`ScrambleGeometry`** with `δ_F = invariant7.deltaF`; at paper ordinary geometry see
  **`paperOrdinary_combinatorialToMatrix_bridge`** in [ModuleABridge](../AKS/Chvatal/ModuleABridge.lean).
  **Module A** (partial): **`of_scrambleGeometry`** / **`Lemma62CellCountingObligation.of_geometry_jMax`** needs
  **`hepsWorst`** + **`hclose`** at paper `(m,jMax)`; **`not_TotalColumnOnesLeN_paperOrdinaryM`**.
  **Not closed at paper `m`:** pipeline B∧F existence / **`ModuleACombinedFailFraction`** at paper numerics,
  global **`AvgRowOnesLeOne`**, and **`ExistsScrambleSeparator`** (packaged residual
  **`PaperOrdinaryScrambleSeparatorResidual`** / **`ExistsScrambleSeparator_paperOrdinaryGeometry_residual`**).
  **`theorem51Params7`** is the wrong `P` at paper `m` (Chernoff ≫ **`invariant7.epsB`**).
  **Unconditional Thm 5.1 separators (pipeline B + `δ_F·n < 1` semantic F):**
  - **`ExistsScrambleSeparator_params7Geometry_f16_moduleA`** — Module A `P` (`ε_B = 1/2`, `ε_F = 300`); not §4-compatible.
  - **`ExistsScrambleSeparator_paperOrdinaryGeometry`** — paper ordinary `m = 2^60`, paper `ε_B`, **`invariant7` `δ_F`/`ε_F`** (DCS-TR-294 §7 ordinary).
  - **`ExistsScrambleSeparator_paperRootGeometry`** — paper root `m = 2^79`, paper root `ε_B`, **`invariant7` `δ_F`/`ε_F`**; Lemma 6.2 floor discharged by **`paperRoot_epsF_lemma62_lb_le_invariant7`** / **`PaperRoot_epsF_lemma62_Certificate`** (value ≪ `1/80000000`).
  - Generic: **`ExistsScrambleSeparator_of_pipelineB_deltaFn`**; B from **`ExistsCombinatorialPropertyBOnPipeline_of_decodeClass`**.
  Semantic F uses **`HasPackSemanticPropertyF.of_idealColumnSort_rowScramble_deltaFn`** (combinatorial F unused when `δ_F·n < 1`).
  **Pack depth (kernel-checked):** ordinary **`ExistsScrambleSeparator_paperOrdinaryGeometry_depth_le_ordinaryStage`** ≤ `3660`; root **`ExistsScrambleSeparator_paperRootGeometry_depth_le_rootSeparator`** ≤ `6320`.
  **§4 paper-ordinary invariants:** **`invariant7_paperOrdinary`** (`ε_B = ε_F = 1/8·10⁷`) with
  **`separatorConds_params7_paperOrdinary`** kernel-checked. Bag link:
  **`ScrambleSeparatorBagLinkPaperOrdinary`** / **`scrambleSeparatorBagLinkPaperOrdinary`**
  (unconditional nonempty) in [Schedule7Trajectory](../AKS/Chvatal/Schedule7Trajectory.lean).
  **`Sorting1830Obligation.d7_batcher_paperOrdinary`** ([StageAssembly](../AKS/Chvatal/StageAssembly.lean)):
  unconditional — stationary PreferNon + **`ScrambleSeparatorResidual.paperOrdinary`** +
  Batcher root/ordinary/final (sorts; `ordinaryRounds 7 = 0`).
  **`Sorting1830Obligation.d7_batcher_paperRoot`**: same assembly with
  **`ScrambleSeparatorResidual.paperRoot`** (unconditional; `ExistsScrambleSeparator_paperRootGeometry`
  discharged). **`network_depth_le_1830_of_d7_batcher_paperOrdinary`** /
  **`_paperRoot`**: for `Nat.clog 64 n = 7`, net depth `≤ 1830 log₂ n − 58657`
  (kernel-checked). Stages are full-wire Batcher, not paper scramble separators; still a
  true depth bound in the §7 padded form at this `d`.
  **Finite Batcher range (strongest unconditional 1830-form endpoint, 2026-10-06):**
  [BatcherAssembly](../AKS/Chvatal/BatcherAssembly.lean) /
  [DepthSkeleton](../AKS/Chvatal/DepthSkeleton.lean) **`batcherFitsTotalDepthMax = 603`**;
  **`bitonicDepthBudget_6d_le_totalDepth`** / **`chvatalFinalBatcherNet_depth_le_totalDepth`**
  for `7 ≤ d ≤ 603`; **`bitonicDepthBudget_6d_gt_totalDepth`** for `d > 603` (Batcher
  method fails past this cutoff). Stage-budget packaging in
  [StageAssembly](../AKS/Chvatal/StageAssembly.lean):
  Batcher all stages for `d ≤ 7`; Batcher-as-root for `d ≤ 18`
  (`batcherRoot_paperOrdinary` / `batcherRoot_paperRoot`); direct totalDepth compare
  for `d ≤ 603`. [Bounds/Chvatal1830Batcher](../AKS/Bounds/Chvatal1830Batcher.lean):
  **`minimum_depth_le_1830_logb_of_batcher_range`** — `D(n) ≤ 1830 log₂ n − 58657`
  for every `1 < n` with `7 ≤ clog 64 n ≤ 603`;
  **`eventually_minimum_depth_le_1830_logb_of_batcher_window`** (windowed, not all large `n`);
  **`limsup_minimum_div_logb_le_1830_of_forall_totalDepth`** (conditional);
  **`Limsup1830Residual`** + **`limsup_…_of_batcher_and_residual`** (honest limsup package;
  residual open for `d > 603`).
  **Paper depth shells (kernel-checked depth, 2026-10-06):**
  **`paperDepthShellNetwork`** in [StageAssembly](../AKS/Chvatal/StageAssembly.lean) —
  tiled root/ordinary packs + parallel final; **`paperDepthShellNetwork_depth_le`**
  `≤ totalDepth d` for every `d ≥ 14`. **`PaperDepthShellSortResidual`** packages
  the open `Sorts` obligation; **`exists_totalDepth_of_paperDepthShellSorts`** and
  **`limsup_minimum_div_logb_le_1830_of_paperDepthShellSorts`** reduce limsup `≤ 1830`
  to those residuals (not discharged).
  Budget lemmas: **`chvatalFinalBatcherNet_depth_le_ordinary`** (`d ≤ 14`),
  **`_le_root`** (`d ≤ 18`). Full-wire Batcher finals meet `903` only for `d ≤ 7`;
  for `d ≥ 7` parallel block finals meet paper final depth (depth only; see below).
  **Pack depth (kernel-checked, 2026-10-06):** [SeparatorDepth](../AKS/Chvatal/SeparatorDepth.lean)
  — columns are wire-disjoint, so `columnSortNetwork_depth_le` ≤ bitonic depth via
  `depth_flatMap_disjoint`; canonical packs (empty scramble comparators) satisfy
  `SortScrambleSortPack_canonical_depth_le_budget` ≤ `2 · bitonicDepthBudget(clog₂ m)`.
  Paper ordinary: `SortScrambleSortPack_paperOrdinary_depth_le_ordinaryStage` ≤ `3660`;
  paper root: `SortScrambleSortPack_paperRoot_depth_le_rootSeparator` ≤ `6320`.
  Also `ExistsScrambleSeparator_paperOrdinaryGeometry_depth_le_ordinaryStage` and
  `ExistsScrambleSeparator_paperRootGeometry_depth_le_rootSeparator` (witnesses with
  those pack-depth bounds). Pack accounting only until bag-routed `64^d` stages.
  **Parallel finals (kernel-checked depth only, 2026-10-06):**
  [ParallelFinalDepth](../AKS/Chvatal/ParallelFinalDepth.lean) /
  [ParallelFinal](../AKS/Chvatal/ParallelFinal.lean) (re-export) —
  `finalBlockSize_dvd_pow64`, `finalBlockEmbed_disjoint`,
  `chvatalParallelFinalNet` = wire-disjoint `flatMap` of `scatterEmbed`
  (`bitonicNetwork finalBlockSize` on contiguous `2^42` blocks),
  **`chvatalParallelFinalNet_depth_le` / `_paper` / `_budget`** ≤ `903` =
  `finalSorterPaperDepth` = `bitonicDepthBudget 42` for every `d ≥ 7`.
  Depth-only shell: **`ParallelFinalDepthObligation.of_parallelBlocks`**
  (also `parallelFinalDepth_ofPaper` in StageAssembly).
  **Does not claim `Sorts`** for `d > 7`; residual **`ParallelFinalPuritySortResidual`**.
  **Pack tiling into `64^d` (kernel-checked depth, 2026-10-06):**
  [StagePackEmbed](../AKS/Chvatal/StagePackEmbed.lean) — abstract
  `BagWireLayout` (`Fin numBags → (Fin bagSize ↪o Fin N)`, pairwise disjoint);
  `parallelScatterBags_depth_le` (packs of depth ≤ `D` ⇒ stage depth ≤ `D`);
  contiguous specialization `parallelPackStageNet_depth_le`. Preferred
  depth-only obligations (no `Sorts`, mirroring `ParallelFinalDepthObligation`):
  **`OrdinarySeparatorDepthObligation`** /
  **`RootSeparatorDepthObligation`**, with
  `of_paperOrdinaryCanonical` (`d ≥ 11`, pack `2^64`, ≤ `3660`) and
  `of_paperRootCanonical` (`d ≥ 14`, pack `2^83`, ≤ `6320`).
  [PackEmbed](../AKS/Chvatal/PackEmbed.lean) re-exports `StagePackEmbed`.
  [StageAssembly](../AKS/Chvatal/StageAssembly.lean):
  `ordinaryPackStage_of_canonical` / `rootPackStage_of_canonical` /
  `parallelFinalDepth_ofPaper`. Tree/Scheduler expose only abstract
  `Placement.regs` (Finsets), not paper-size bag layouts for these tilings.
  `OrdinarySeparatorStageObligation` / `RootSeparatorStageObligation` still
  require `Sorts` (overstrong for separators); prefer the depth-only shells.
  **Open for limsup / all large `n`:** wire depth shells into the §7 outsider
  schedule (not global `Sorts`); discharge purity⇒sort for parallel finals when
  `d > 7`. Root Lemma 6.2 / Thm 5.1 separator and pack depth ≤ `6320` are discharged.
  Unconditional `limsup D(n)/log₂ n ≤ 1830` remains open (`Limsup1830Residual` for
  `d > 603`); Batcher covers only `7 ≤ clog 64 n ≤ 603`.
  **Kernel-checked 1830-form (finite range, 2026-10-06):**
  `minimum_depth_le_1830_logb_of_batcher_range` — for every `1 < n` with
  `7 ≤ clog 64 n ≤ 603`, `D(n) ≤ 1830 log₂ n − 58657` (axioms: propext /
  Classical.choice / Quot.sound only; see `Chvatal1830Axioms`). Not limsup;
  stages are Batcher, not paper separators.

  **Build (2026-10-06):** **`lake build AKS`** green including **`PaperScrambleNumerics`** and **`ModuleABridge`**.
  Counting / decode-class track: **`AKS.Chvatal.ModuleA`**
  (pipeline Lemma 6.1 fail bound **`lemma61FailBound_onPipeline_of_decodeClass`**, Lemma 6.2 cell counting,
  **`ModuleACombinatorialObligation`**). Bridge / §7 API: **`AKS.Chvatal.ModuleABridge`**.
  **Fail-fraction / existence (2026-10-06, kernel-checked where noted):**
  **`not_ModuleACombinedFailFraction_m100_crude`**: nested-level pipeline factor **`lemma61_failFactor_pipeline`**
  plus F **`β`** at `(100,16,x=3/10)` is **not** `< 1` (proved lower bound **`α ≳ 4/5`**, **`β ≳ 43/100`**).
  **`ModuleACombinedFailFraction_m100`** is **kernel-checked** via **`moduleACombinedFailFraction_m100`**: pigeonhole
  uses **`lemma61_failFactor`** (one **`matrixOnesLevel`** cell per monotone matrix in
  **`lemma61FailBound_onPipeline_of_decodeClass`**, not **`m · lemma61_failFactor`**).
  **`moduleA_global_failFraction_add_lt_one`**: **`lemma61_failFactor + lemma62_failFactor` `< 1`** for all
  **`m ≥ 100`**, **`n ≥ 16`**; still needed for unrestricted global Lemma 6.1 with **`AvgRowOnesLeOne`** (false at
  **`m = 100`**).
  **`ExistsCombinatorialScrambleBF_onPipeline_of_ModuleA_m100`**: **unconditional** from
  **`ModuleACombinatorialObligation`** + **`hinner : F.inner = thirty`** (no separate **`hαβ`**).
  **`ModuleAPipelineBFImpliesScrambleSeparator_m100_discharged`**: given combinatorial pipeline B/F on one `σ` and
  **`CombinatorialToMatrixObligation`**, **`ExistsScrambleSeparator`** is kernel-checked (no separate `hRes`); compose
  with **`exists_combinatorialScrambleBF_onPipeline_of_ModuleA_m100`** at `(100,16)` when `g.m = 100` and `g.n = 16`.
  Legacy alias **`ModuleAPipelineBFImpliesScrambleSeparator_m100`** is still the Prop **`ExistsScrambleSeparator`**
  for older entry points that pass **`hRes`** explicitly.
  **Paper `m`:** crude **`lemma61_failFactor_pipeline (2^60) 16 < 1`** is false; F **`hclose`** at huge `jMax` remains
  open (**`PaperOrdinary_hclose_residual`**; see **`paperOrdinary_lemma62_jMax_gt_48`**).

  **Hypothesis ledger at `m = 100`, `n = 16`** (see [Params](../AKS/Chvatal/Params.lean),
  [ModuleANumerics](../AKS/Chvatal/ModuleANumerics.lean), [Lemma61](../AKS/Chvatal/Lemma61.lean)):

  | Item | Lean status |
  |------|-------------|
  | `hPeps` / geometry side (`hf2`, `hmF`, `hjMax48`, …) | **Discharged** on `params7Geometry` (`ModuleANumerics`, `ModuleA`) |
  | `invariant7` vs Lemma 6.1 Chernoff `hepsB` | **Impossible at `m=100`** — `not_invariant7_hepsB_m100`; **log-scale `m`** — `chernoff_loose_floor_le_eps`, `invariant7_chernoff_loose_m_gt_100` (`m ≳ 2·10^30` for loose `√(2/m) ≤ epsB`) |
  | `invariant7` vs worst-case fringe `hepsWorst` | **Impossible** — `not_invariant7_hepsWorst_f16` |
  | `invariant7` vs `(4e)/f`, `epsF_lemma62_lb` | **Impossible** — `not_invariant7_hepsF_ge_4e_f16` (+ numeric gap for `hepsF_ge_lemma62`) |
  | §4 `(4.2)` / `(4.5)` vs Chernoff-scale `ε` | **Incompatible** — `not_cond42_epsB_half_at_params7`, `not_cond45_epsF_three_hundred_at_params7` |
  | `htotal` / `havg` (global ∀ monotone `c`) | **Equivalent** and **false** — `not_TotalColumnOnesLeN_100_16`. **Not used** for pipeline B: **`DecodeMatrixClassObligation.standard`** + per-level `totalColumnOnesLeLevel_decodeColumnSums_atLevel` (`SortedColumnDecode`) |
  | Pipeline B at `(100,16)` | **`DecodeMatrixClassObligation`** → **`lemma61FailBound_onPipeline_of_decodeClass`** (union at **`matrixOnesLevel`**, factor **`lemma61_failFactor`**) → **`ExistsCombinatorialPropertyBOnPipeline`** |
  | `havg` for F | Still required for fringe cell Chernoff unless a narrower F-side class is packaged |
  | **Viable Thm 5.1 `P`** | **`theorem51Params_moduleA_f16`** — `εB = 1/2`, `εF = 300`, `δF = invariant7.deltaF`; Chernoff floors kernel-checked except **`ModuleA_epsF_lemma62_Certificate`** (`epsF_lemma62_lb ≤ 300`, value ≈ 3.81) |
  | `ExistsScrambleSeparator` at Module A `P` | **`ExistsScrambleSeparator_of_moduleA_and_bridge`** / **`_m100`** — needs **`hRes`** (residual separator) plus **`hExist`** (residual B∧F scramble) and **`hαβ`** (residual `α+β`); B-side counting is kernel-checked on decode class. **`ExistsScrambleSeparator_params7Geometry_f16_*`** updated accordingly |

  **1830 depth budget:** `SeparatorConds params7 invariant7` and `totalDepth` / `network_depth_le_1830_of_sorting1830Obligation` remain tied to **tiny** `invariant7` scalars (`chvatal71`-scale). Module A Chernoff `P` does **not** satisfy those §4 inequalities; plugging `theorem51Params_moduleA_f16` into `LocalSeparatorQuality.ofTheorem51 invariant7` would break outsider induction. Closing `Sorting1830Obligation` still needs either reconciled constants or a split between matrix-existence `P` and schedule `InvariantParams`.
  **Remaining for unconditional `D(n) ≤ 1830 log₂ n`:** (1) optional link `HasMatrixPropertyB pack.net` when
  `wirePerm = 1` (semantic = comparator exec),
  (2) per-stage `PreferNonStageObligation` / `Params7AbstractTrajectoryObligation` from
  Thm 5.1 routing, (3) real root/ordinary separator nets at paper depths for general
  `d ≥ 7` (partial: **`of_batcher903_emptySeparators_d7`** at `StageDepthBudget.ofPaper`).
  **Unconditional 1830 is still open** (`network_depth_le_1830_of_sorting1830Obligation`
  remains hypothesis-dependent).


