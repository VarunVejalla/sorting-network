# Archived Chvátal-1830 scaffolding (not built)

These files were part of the path to the Chvátal 1830 bound but are not used by the final
proof, which now lives in [`../../chvatal-1830`](../../chvatal-1830). They are kept (unbuilt,
module names unchanged) because some may be useful later.

* `Chvatal/Bound1830.lean`, `StageAssembly.lean`, `BatcherAssembly.lean`, `Schedule7Trajectory.lean`,
  `SkeletonAxioms.lean` — the earlier abstract route: `AbstractChildSendTrajectory`, the
  `Sorting1830Obligation` bundle, d = 7 Batcher stage assemblies, paper depth-shell networks
  (`PaperDepthShellSortResidual`) and the finite-range (`7 ≤ d ≤ 603`) full-wire Batcher endpoint.
  Superseded by the real execution-defined network (`chvatal-1830/AKS/Chvatal/Real*.lean`).
* `Chvatal/ParallelFinal.lean`, `FinalPurity.lean` — an earlier monotone-parallel final layer on
  rank-pure blocks (replaced by `FinalSorts`/`RealBlocks`).
* `Chvatal/ColumnOnesRegion.lean`, `PackEmbed.lean`, `StagePackEmbed.lean`,
  `GeneralNPropertyB.lean` — early Property B / pack-embedding helpers that the corrected
  separator route (`GeneralParams`, `FlipSpec`, `PhysicalPack`) no longer needs.
* `Bounds/Chvatal1830Batcher.lean`, `Chvatal1830Axioms.lean`, `Chvatal1830Final.lean` — the old
  finite-range Batcher endpoint, its axiom checks, and the first (main-repo) version of the final
  theorems; the standalone package contains the minimal replacement.
