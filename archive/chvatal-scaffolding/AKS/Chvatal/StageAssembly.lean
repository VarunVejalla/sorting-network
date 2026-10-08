module
/-
  # Chvátal §7 stage network assembly (residual packaging)

  Executable stage nets toward `Sorting1830Obligation.assembly` and
  `NetworkDepthAssemblyObligation`.

  **Kernel-checked:** empty root/ordinary placeholders (depth `0`, within paper
  budgets); composed network sorts when the final stage sorts and the ordinary
  template is empty (`appendRepeated` of an empty net); Batcher final
  `bitonicNetwork (64^d)` on wire count `64^d = 2^(6d)` with depth
  `≤ bitonicDepthBudget (6d)`; at `d ≤ 7` this meets the §7 `903` final budget;
  Batcher-as-root with empty ordinary/final meets paper root budget for
  `d ≤ 18`; full-wire Batcher depth is `≤ totalDepth d` for `7 ≤ d ≤ 603`.

  **Depth shells (kernel-checked, no `Sorts`):** parallel final
  (`ParallelFinalDepthObligation`, `d ≥ 7`); ordinary/root pack tilings
  (`OrdinarySeparatorDepthObligation` / `RootSeparatorDepthObligation` in
  `StagePackEmbed`, paper packs at `d ≥ 11` / `d ≥ 14`).

  **Open (honest residual):** scheduler `Placement.regs` matching paper bag
  sizes; stage nets that participate correctly in the §7 outsider schedule
  (not global `Sorts`); purity ⇒ `Sorts` for parallel finals when `d > 7`;
  linking stages to Thm 5.1 / trajectory data; limsup `≤ 1830` (Batcher only
  covers `d ≤ 603`; see `Limsup1830Residual` / `bitonicDepthBudget_6d_gt_totalDepth`).
-/

public import AKS.Chvatal.Bound1830
public import AKS.Chvatal.BatcherAssembly
public import AKS.Chvatal.Schedule7Trajectory
public import AKS.Chvatal.ParallelFinal
public import AKS.Chvatal.StagePackEmbed
public import AKS.Bitonic.Shrink
public import AKS.Bitonic.TightDepth
public import AKS.Sort.Shrink
public import AKS.Sort.Depth

@[expose] public section

namespace Chvatal

/-! ## Batcher nets and totalDepth comparison

Re-exported from `AKS.Chvatal.BatcherAssembly` (empty stage, full-wire Batcher,
`bitonicDepthBudget_6d_le_totalDepth` / `_gt_totalDepth`, padded 1830 forms).
-/

/-! ## Empty ordinary template -/

private theorem chvatalEmptyStageNet_appendRepeated_comparators (d k : Nat) :
    (ComparatorNetwork.appendRepeated k (chvatalEmptyStageNet d)).comparators = [] := by
  induction k with
  | zero => simp [ComparatorNetwork.appendRepeated_zero, chvatalEmptyStageNet]
  | succ k ih =>
    simp only [ComparatorNetwork.appendRepeated, chvatalEmptyStageNet, ComparatorNetwork.append]
    simpa [chvatalEmptyStageNet] using ih

theorem chvatalEmptyStageNet_appendRepeated (d k : Nat) :
    ComparatorNetwork.appendRepeated k (chvatalEmptyStageNet d) = chvatalEmptyStageNet d := by
  apply ComparatorNetwork.ext
  exact chvatalEmptyStageNet_appendRepeated_comparators d k

theorem assembledChvatalNetwork_emptyRootOrdinary {d : Nat}
    (finalNet : ComparatorNetwork (64 ^ d)) :
    assembledChvatalNetwork (chvatalEmptyStageNet d) (chvatalEmptyStageNet d) finalNet =
      (chvatalEmptyStageNet d).append finalNet := by
  unfold assembledChvatalNetwork
  rw [show (chvatalEmptyStageNet d).appendRepeated (ordinaryRounds d) = chvatalEmptyStageNet d from
    chvatalEmptyStageNet_appendRepeated d (ordinaryRounds d)]
  simp [chvatalEmptyStageNet, ComparatorNetwork.append]

/-- Empty root/ordinary stages: sorting of the §7 assembly reduces to the final net. -/
theorem assembledChvatalNetwork_sorts_emptyRootOrdinary {d : Nat}
    (finalNet : ComparatorNetwork (64 ^ d))
    (hfinal : ComparatorNetwork.Sorts.{0} finalNet) :
    ComparatorNetwork.Sorts.{0}
      (assembledChvatalNetwork (chvatalEmptyStageNet d) (chvatalEmptyStageNet d)
        finalNet) := by
  rw [assembledChvatalNetwork_emptyRootOrdinary]
  intro α inst v
  simp [ComparatorNetwork.append, ComparatorNetwork.exec_append]
  exact @hfinal α inst v

/-- Batcher as root with empty ordinary/final: assembly equals the Batcher net. -/
theorem assembledChvatalNetwork_batcherRoot_emptyOrdFinal (d : Nat) :
    assembledChvatalNetwork (chvatalFinalBatcherNet d) (chvatalEmptyStageNet d)
      (chvatalEmptyStageNet d) = chvatalFinalBatcherNet d := by
  unfold assembledChvatalNetwork
  rw [chvatalEmptyStageNet_appendRepeated]
  apply ComparatorNetwork.ext
  simp [chvatalEmptyStageNet, ComparatorNetwork.append, List.append_nil]

theorem assembledChvatalNetwork_sorts_batcherRoot_emptyOrdFinal (d : Nat) :
    ComparatorNetwork.Sorts.{0}
      (assembledChvatalNetwork (chvatalFinalBatcherNet d) (chvatalEmptyStageNet d)
        (chvatalEmptyStageNet d)) := by
  rw [assembledChvatalNetwork_batcherRoot_emptyOrdFinal]
  exact chvatalFinalBatcherNet_sorts d

/-! ## Residual separator stage obligations -/

/-- Depth-only root separator shell (prefer over `RootSeparatorStageObligation`
    when assembling stage budgets; separators need not sort). -/
abbrev RootSeparatorDepthShell (d : Nat) := RootSeparatorDepthObligation d

/-- Depth-only ordinary separator shell (prefer over `OrdinarySeparatorStageObligation`
    when assembling stage budgets; separators need not sort). -/
abbrev OrdinarySeparatorDepthShell (d : Nat) := OrdinarySeparatorDepthObligation d

/-- Executable root separator on `64^d` within the §7 root depth budget.
    **Overstrong for separators:** requires `Sorts`. Prefer
    `RootSeparatorDepthObligation` for depth accounting. -/
structure RootSeparatorStageObligation (d : Nat) where
  net : ComparatorNetwork (64 ^ d)
  hdepth : net.depth ≤ rootSeparatorPaperDepth
  hsorts : ComparatorNetwork.Sorts.{0} net

/-- One ordinary §7 round on `64^d` within the ordinary depth budget.
    **Overstrong for separators:** requires `Sorts`. Prefer
    `OrdinarySeparatorDepthObligation` for depth accounting. -/
structure OrdinarySeparatorStageObligation (d : Nat) where
  net : ComparatorNetwork (64 ^ d)
  hdepth : net.depth ≤ ordinaryStagePaperDepth
  hsorts : ComparatorNetwork.Sorts.{0} net

/-- Final sorter on `64^d` within the §7 final depth budget (`903`). -/
structure FinalSorterStageObligation (d : Nat) where
  net : ComparatorNetwork (64 ^ d)
  hdepth : net.depth ≤ finalSorterPaperDepth
  hsorts : ComparatorNetwork.Sorts.{0} net

def FinalSorterStageObligation.of_batcher903 (d : Nat)
    (hd : d ≤ 7) : FinalSorterStageObligation d where
  net := chvatalFinalBatcherNet d
  hdepth := chvatalFinalBatcherNet_depth_le_paper hd
  hsorts := chvatalFinalBatcherNet_sorts d

/-- Bundle root, ordinary, and final stage nets into `NetworkDepthAssemblyObligation`. -/
def NetworkDepthAssemblyObligation.of_separatorStages {d : Nat}
    (budget : StageDepthBudget d)
    (root : RootSeparatorStageObligation d)
    (ord : OrdinarySeparatorStageObligation d)
    (final : FinalSorterStageObligation d)
    (hroot : root.net.depth ≤ budget.rootSepDepth)
    (hord : ord.net.depth ≤ budget.ordinaryStageDepth)
    (hfinal : final.net.depth ≤ budget.finalSorterDepth) :
    NetworkDepthAssemblyObligation d :=
  NetworkDepthAssemblyObligation.of_stage_sorts budget root.net ord.net final.net
    hroot hord hfinal root.hsorts ord.hsorts final.hsorts

/-- Placeholder root/ordinary (empty) + a final sorter; honest until separators exist. -/
def NetworkDepthAssemblyObligation.of_emptyRootOrdinary_final {d : Nat}
    (budget : StageDepthBudget d)
    (final : FinalSorterStageObligation d)
    (hroot : (chvatalEmptyStageNet d).depth ≤ budget.rootSepDepth)
    (hord : (chvatalEmptyStageNet d).depth ≤ budget.ordinaryStageDepth)
    (hfinal : final.net.depth ≤ budget.finalSorterDepth) :
    NetworkDepthAssemblyObligation d where
  budget := budget
  rootNet := chvatalEmptyStageNet d
  ordinaryNet := chvatalEmptyStageNet d
  finalNet := final.net
  hroot := hroot
  hord := hord
  hfinal := hfinal
  sorts := assembledChvatalNetwork_sorts_emptyRootOrdinary final.net final.hsorts

def NetworkDepthAssemblyObligation.of_emptyRootOrdinary_final_paper {d : Nat}
    (final : FinalSorterStageObligation d)
    (hfinal : final.net.depth ≤ finalSorterPaperDepth) :
    NetworkDepthAssemblyObligation d :=
  NetworkDepthAssemblyObligation.of_emptyRootOrdinary_final
    (StageDepthBudget.ofPaper d) final
    (by rw [chvatalEmptyStageNet_depth]; omega)
    (by rw [chvatalEmptyStageNet_depth]; omega)
    (hfinal.trans (StageDepthBudget.ofPaper d).hfinal)

/-- Empty separators + Batcher final for every `d ≤ 7` (final paper budget `903`). -/
def NetworkDepthAssemblyObligation.of_batcher903_emptySeparators {d : Nat}
    (hd : d ≤ 7) : NetworkDepthAssemblyObligation d :=
  NetworkDepthAssemblyObligation.of_emptyRootOrdinary_final_paper
    (FinalSorterStageObligation.of_batcher903 d hd)
    (chvatalFinalBatcherNet_depth_le_paper hd)

def NetworkDepthAssemblyObligation.of_batcher903_emptySeparators_d7 :
    NetworkDepthAssemblyObligation 7 :=
  NetworkDepthAssemblyObligation.of_batcher903_emptySeparators (d := 7) le_rfl

/-- Full-wire Batcher in every stage slot for `d ≤ 7` (fits all three paper budgets). -/
def NetworkDepthAssemblyObligation.of_batcher_allStages {d : Nat}
    (_hd0 : 0 < d) (hd : d ≤ 7) : NetworkDepthAssemblyObligation d :=
  NetworkDepthAssemblyObligation.of_stage_sorts (StageDepthBudget.ofPaper d)
    (chvatalFinalBatcherNet d) (chvatalFinalBatcherNet d) (chvatalFinalBatcherNet d)
    (by
      have h := chvatalFinalBatcherNet_depth_le_paper hd
      exact h.trans (by decide : finalSorterPaperDepth ≤ rootSeparatorPaperDepth))
    (by
      have h := chvatalFinalBatcherNet_depth_le_paper hd
      exact h.trans (by decide : finalSorterPaperDepth ≤ ordinaryStagePaperDepth))
    (chvatalFinalBatcherNet_depth_le_paper hd)
    (chvatalFinalBatcherNet_sorts d) (chvatalFinalBatcherNet_sorts d)
    (chvatalFinalBatcherNet_sorts d)

def NetworkDepthAssemblyObligation.of_batcher_allStages_d7 :
    NetworkDepthAssemblyObligation 7 :=
  NetworkDepthAssemblyObligation.of_batcher_allStages (by decide : 0 < 7) le_rfl

/-- Batcher as root, empty ordinary/final: fits paper root budget for `d ≤ 18`.
    Composed net equals `chvatalFinalBatcherNet d` and sorts; separators are placeholders. -/
def NetworkDepthAssemblyObligation.of_batcherRoot_emptyOrdFinal {d : Nat}
    (hd0 : 0 < d) (hd18 : d ≤ 18) : NetworkDepthAssemblyObligation d where
  budget := StageDepthBudget.ofPaper d
  rootNet := chvatalFinalBatcherNet d
  ordinaryNet := chvatalEmptyStageNet d
  finalNet := chvatalEmptyStageNet d
  hroot := chvatalFinalBatcherNet_depth_le_root hd0 hd18
  hord := by rw [chvatalEmptyStageNet_depth]; omega
  hfinal := by rw [chvatalEmptyStageNet_depth]; omega
  sorts := assembledChvatalNetwork_sorts_batcherRoot_emptyOrdFinal d

theorem NetworkDepthAssemblyObligation.of_batcher903_emptySeparators_composed {d : Nat}
    (hd : d ≤ 7) :
    (NetworkDepthAssemblyObligation.of_batcher903_emptySeparators hd).composed =
      chvatalFinalBatcherNet d := by
  rw [NetworkDepthAssemblyObligation.composed]
  have hAsm :=
    assembledChvatalNetwork_emptyRootOrdinary (chvatalFinalBatcherNet d)
  simp only [NetworkDepthAssemblyObligation.of_batcher903_emptySeparators,
    NetworkDepthAssemblyObligation.of_emptyRootOrdinary_final_paper,
    NetworkDepthAssemblyObligation.of_emptyRootOrdinary_final,
    FinalSorterStageObligation.of_batcher903, chvatalEmptyStageNet] at hAsm ⊢
  rw [hAsm]
  apply ComparatorNetwork.ext
  simp [ComparatorNetwork.append]

theorem NetworkDepthAssemblyObligation.of_batcher903_emptySeparators_d7_composed :
    NetworkDepthAssemblyObligation.of_batcher903_emptySeparators_d7.composed =
      chvatalFinalBatcherNet 7 :=
  NetworkDepthAssemblyObligation.of_batcher903_emptySeparators_composed le_rfl

theorem NetworkDepthAssemblyObligation.of_batcherRoot_emptyOrdFinal_composed {d : Nat}
    (hd0 : 0 < d) (hd18 : d ≤ 18) :
    (NetworkDepthAssemblyObligation.of_batcherRoot_emptyOrdFinal hd0 hd18).composed =
      chvatalFinalBatcherNet d := by
  rw [NetworkDepthAssemblyObligation.composed]
  simp only [NetworkDepthAssemblyObligation.of_batcherRoot_emptyOrdFinal]
  exact assembledChvatalNetwork_batcherRoot_emptyOrdFinal d

theorem NetworkDepthAssemblyObligation.of_batcher903_emptySeparators_d7_depth :
    NetworkDepthAssemblyObligation.of_batcher903_emptySeparators_d7.composed.depth ≤
      totalDepth 7 :=
  NetworkDepthAssemblyObligation.depth_le_totalDepth
    NetworkDepthAssemblyObligation.of_batcher903_emptySeparators_d7

/-! ## Hypothesis-dependent §7 obligation (Batcher assemblies) -/

/-- Empty root/ordinary + Batcher final; trajectory and separator remain hypotheses. -/
def Sorting1830Obligation.of_routingAssembly_emptyBatcher {d : Nat} {hd : 7 ≤ d}
    (hd7 : d ≤ 7)
    (traj : Params7AbstractTrajectoryRoutingObligation d hd)
    (separator : ScrambleSeparatorResidual) :
    Sorting1830Obligation d hd :=
  Sorting1830Obligation.of_routingAssembly traj separator
    (NetworkDepthAssemblyObligation.of_batcher903_emptySeparators hd7) le_rfl

def Sorting1830Obligation.of_routingAssembly_d7
    (traj : Params7AbstractTrajectoryRoutingObligation 7 (by decide : 7 ≤ 7))
    (separator : ScrambleSeparatorResidual) :
    Sorting1830Obligation 7 (by decide : 7 ≤ 7) :=
  Sorting1830Obligation.of_routingAssembly_emptyBatcher (hd7 := le_rfl) traj separator

def Sorting1830Obligation.of_preferNonAssembly_d7
    (traj : Params7AbstractTrajectoryObligation 7 (by decide : 7 ≤ 7))
    (separator : ScrambleSeparatorResidual) :
    Sorting1830Obligation 7 (by decide : 7 ≤ 7) :=
  Sorting1830Obligation.of_preferNonAssembly traj separator
    NetworkDepthAssemblyObligation.of_batcher903_emptySeparators_d7 le_rfl

theorem Sorting1830Obligation.of_routingAssembly_d7_net_eq
    (traj : Params7AbstractTrajectoryRoutingObligation 7 (by decide : 7 ≤ 7))
    (separator : ScrambleSeparatorResidual) :
    (Sorting1830Obligation.of_routingAssembly_d7 traj separator).net =
      chvatalFinalBatcherNet 7 := by
  rw [Sorting1830Obligation.net, Sorting1830Obligation.of_routingAssembly_d7,
    Sorting1830Obligation.of_routingAssembly_emptyBatcher,
    NetworkDepthAssemblyObligation.composed]
  exact NetworkDepthAssemblyObligation.of_batcher903_emptySeparators_composed le_rfl

theorem network_depth_le_1830_pow_of_routingAssembly_d7
    (traj : Params7AbstractTrajectoryRoutingObligation 7 (by decide : 7 ≤ 7))
    (separator : ScrambleSeparatorResidual) :
    ((Sorting1830Obligation.of_routingAssembly_d7 traj separator).net.depth : ℝ) ≤
      1830 * Real.logb 2 ((64 ^ 7 : ℕ) : ℝ) - 58657 :=
  network_depth_le_1830_pow_of_sorting1830Obligation 7 (by decide : 7 ≤ 7)
    (Sorting1830Obligation.of_routingAssembly_d7 traj separator)
    (by
      have : 1 < 64 ^ 7 := by
        apply Nat.one_lt_pow
        · norm_num
        · omega
      exact this)

/-! ## Stationary-root + paper-ordinary separator packages -/

/-- All schedule stages: stationary `rootPlacement`, empty `fromParent`, identity perm. -/
def Params7AbstractTrajectoryRoutingObligation.stationaryRoot7 :
    Params7AbstractTrajectoryRoutingObligation 7 (by decide : 7 ≤ 7) :=
  Params7AbstractTrajectoryRoutingObligation.stationaryRoot 7 (by decide)

/-- `Sorting1830Obligation` at `d = 7`: stationary empty-send trajectory + unconditional
    paper-ordinary Thm 5.1 separator + Batcher-only assembly (empty stage nets).
    **Honest:** the composed net equals `chvatalFinalBatcherNet 7`, not a full Chvátal scheduler. -/
noncomputable def Sorting1830Obligation.d7_stationary_paperOrdinary :
    Sorting1830Obligation 7 (by decide : 7 ≤ 7) :=
  Sorting1830Obligation.of_routingAssembly_d7
    Params7AbstractTrajectoryRoutingObligation.stationaryRoot7
    ScrambleSeparatorResidual.paperOrdinary

theorem Sorting1830Obligation.d7_stationary_paperOrdinary_net :
    Sorting1830Obligation.d7_stationary_paperOrdinary.net = chvatalFinalBatcherNet 7 :=
  Sorting1830Obligation.of_routingAssembly_d7_net_eq
    Params7AbstractTrajectoryRoutingObligation.stationaryRoot7
    ScrambleSeparatorResidual.paperOrdinary

theorem network_depth_le_1830_pow_of_d7_stationary_paperOrdinary :
    (Sorting1830Obligation.d7_stationary_paperOrdinary.net.depth : ℝ) ≤
      1830 * Real.logb 2 ((64 ^ 7 : ℕ) : ℝ) - 58657 :=
  network_depth_le_1830_pow_of_routingAssembly_d7
    Params7AbstractTrajectoryRoutingObligation.stationaryRoot7
    ScrambleSeparatorResidual.paperOrdinary

/-- Unconditional `d = 7` package with Batcher root/ordinary/final (sorts) + paper-ordinary
    Thm 5.1 residual + stationary PreferNon. Depth `≤ totalDepth 7` hence padded 1830 form.
    **Honest:** stages are full-wire Batcher, not paper scramble separators. -/
noncomputable def Sorting1830Obligation.d7_batcher_paperOrdinary :
    Sorting1830Obligation 7 (by decide : 7 ≤ 7) :=
  Sorting1830Obligation.of_routingAssembly
    Params7AbstractTrajectoryRoutingObligation.stationaryRoot7
    ScrambleSeparatorResidual.paperOrdinary
    NetworkDepthAssemblyObligation.of_batcher_allStages_d7
    (StageDepthBudget.ofPaper_final_le_batcher42 7)

/-- Same Batcher assembly with evolving native level-1 PreferNon trajectory
    (nonempty zero-stranger `fromParent` at the unique `tf = 1` stage). -/
noncomputable def Sorting1830Obligation.d7_batcher_paperOrdinary_nativeLevel1 :
    Sorting1830Obligation 7 (by decide : 7 ≤ 7) :=
  Sorting1830Obligation.of_routingAssembly
    Params7AbstractTrajectoryRoutingObligation.nativeLevel1_d7
    ScrambleSeparatorResidual.paperOrdinary
    NetworkDepthAssemblyObligation.of_batcher_allStages_d7
    (StageDepthBudget.ofPaper_final_le_batcher42 7)

theorem network_depth_le_1830_pow_of_d7_batcher_paperOrdinary_nativeLevel1 :
    (Sorting1830Obligation.d7_batcher_paperOrdinary_nativeLevel1.net.depth : ℝ) ≤
      1830 * Real.logb 2 ((64 ^ 7 : ℕ) : ℝ) - 58657 :=
  network_depth_le_1830_pow_of_sorting1830Obligation 7 (by decide : 7 ≤ 7)
    Sorting1830Obligation.d7_batcher_paperOrdinary_nativeLevel1
    (by
      have : 1 < 64 ^ 7 := by
        apply Nat.one_lt_pow
        · norm_num
        · omega
      exact this)

theorem Sorting1830Obligation.d7_batcher_paperOrdinary_nativeLevel1_outsiderBoundLe_tf :
    OutsiderBoundLe params7 invariant7 7 (levelSchedule7 7 (by decide))
      (levelSchedule7 7 (by decide)).tf
      (Sorting1830Obligation.d7_batcher_paperOrdinary_nativeLevel1.abstract.pls
        (levelSchedule7 7 (by decide)).tf)
      (Sorting1830Obligation.d7_batcher_paperOrdinary_nativeLevel1.abstract.perms
        (levelSchedule7 7 (by decide)).tf) :=
  Sorting1830Obligation.d7_batcher_paperOrdinary_nativeLevel1.outsiderBoundLe_tf

/-- Same as `d7_batcher_paperOrdinary` with the unconditional paper-root residual. -/
noncomputable def Sorting1830Obligation.d7_batcher_paperRoot :
    Sorting1830Obligation 7 (by decide : 7 ≤ 7) :=
  Sorting1830Obligation.of_routingAssembly
    Params7AbstractTrajectoryRoutingObligation.stationaryRoot7
    ScrambleSeparatorResidual.paperRoot
    NetworkDepthAssemblyObligation.of_batcher_allStages_d7
    (StageDepthBudget.ofPaper_final_le_batcher42 7)

theorem network_depth_le_1830_pow_of_d7_batcher_paperOrdinary :
    (Sorting1830Obligation.d7_batcher_paperOrdinary.net.depth : ℝ) ≤
      1830 * Real.logb 2 ((64 ^ 7 : ℕ) : ℝ) - 58657 :=
  network_depth_le_1830_pow_of_sorting1830Obligation 7 (by decide : 7 ≤ 7)
    Sorting1830Obligation.d7_batcher_paperOrdinary
    (by
      have : 1 < 64 ^ 7 := by
        apply Nat.one_lt_pow
        · norm_num
        · omega
      exact this)

theorem network_depth_le_1830_pow_of_d7_batcher_paperRoot :
    (Sorting1830Obligation.d7_batcher_paperRoot.net.depth : ℝ) ≤
      1830 * Real.logb 2 ((64 ^ 7 : ℕ) : ℝ) - 58657 :=
  network_depth_le_1830_pow_of_sorting1830Obligation 7 (by decide : 7 ≤ 7)
    Sorting1830Obligation.d7_batcher_paperRoot
    (by
      have : 1 < 64 ^ 7 := by
        apply Nat.one_lt_pow
        · norm_num
        · omega
      exact this)

/-- For `n` with `Nat.clog 64 n = 7`, the `d = 7` Batcher assembly meets the padded §7 bound. -/
theorem network_depth_le_1830_of_d7_batcher_paperOrdinary {n : Nat}
    (hclog : Nat.clog 64 n = 7) (hn : 1 < n) :
    (Sorting1830Obligation.d7_batcher_paperOrdinary.net.depth : ℝ) ≤
      1830 * Real.logb 2 (n : ℝ) - 58657 :=
  network_depth_le_1830_of_sorting1830Obligation (by decide : 7 ≤ 7) hclog hn
    Sorting1830Obligation.d7_batcher_paperOrdinary

theorem network_depth_le_1830_of_d7_batcher_paperRoot {n : Nat}
    (hclog : Nat.clog 64 n = 7) (hn : 1 < n) :
    (Sorting1830Obligation.d7_batcher_paperRoot.net.depth : ℝ) ≤
      1830 * Real.logb 2 (n : ℝ) - 58657 :=
  network_depth_le_1830_of_sorting1830Obligation (by decide : 7 ≤ 7) hclog hn
    Sorting1830Obligation.d7_batcher_paperRoot

theorem Sorting1830Obligation.d7_batcher_paperOrdinary_sorts :
    ComparatorNetwork.Sorts.{0} Sorting1830Obligation.d7_batcher_paperOrdinary.net :=
  Sorting1830Obligation.d7_batcher_paperOrdinary.sorts

theorem Sorting1830Obligation.d7_batcher_paperOrdinary_outsiderBoundLe_tf :
    OutsiderBoundLe params7 invariant7 7 (levelSchedule7 7 (by decide))
      (levelSchedule7 7 (by decide)).tf
      (Sorting1830Obligation.d7_batcher_paperOrdinary.abstract.pls
        (levelSchedule7 7 (by decide)).tf)
      (Sorting1830Obligation.d7_batcher_paperOrdinary.abstract.perms
        (levelSchedule7 7 (by decide)).tf) :=
  Sorting1830Obligation.d7_batcher_paperOrdinary.outsiderBoundLe_tf

/-! ## Batcher-root assembly for `7 ≤ d ≤ 18` (paper root budget) -/

/-- Unconditional package: stationary PreferNon + paper-ordinary residual + Batcher root
    (empty ordinary/final). Fits `StageDepthBudget.ofPaper` for `d ≤ 18`.
    **Honest:** composed net is full-wire Batcher on `64^d`, not the paper schedule. -/
noncomputable def Sorting1830Obligation.batcherRoot_paperOrdinary
    (d : Nat) (hd : 7 ≤ d) (hd18 : d ≤ 18) :
    Sorting1830Obligation d hd :=
  Sorting1830Obligation.of_routingAssembly
    (Params7AbstractTrajectoryRoutingObligation.stationaryRoot d hd)
    ScrambleSeparatorResidual.paperOrdinary
    (NetworkDepthAssemblyObligation.of_batcherRoot_emptyOrdFinal
      (Nat.pos_of_ne_zero (by omega : d ≠ 0)) hd18)
    (StageDepthBudget.ofPaper_final_le_batcher42 d)

/-- Same Batcher-root package with the unconditional paper-root residual. -/
noncomputable def Sorting1830Obligation.batcherRoot_paperRoot
    (d : Nat) (hd : 7 ≤ d) (hd18 : d ≤ 18) :
    Sorting1830Obligation d hd :=
  Sorting1830Obligation.of_routingAssembly
    (Params7AbstractTrajectoryRoutingObligation.stationaryRoot d hd)
    ScrambleSeparatorResidual.paperRoot
    (NetworkDepthAssemblyObligation.of_batcherRoot_emptyOrdFinal
      (Nat.pos_of_ne_zero (by omega : d ≠ 0)) hd18)
    (StageDepthBudget.ofPaper_final_le_batcher42 d)

theorem Sorting1830Obligation.batcherRoot_paperOrdinary_net
    (d : Nat) (hd : 7 ≤ d) (hd18 : d ≤ 18) :
    (Sorting1830Obligation.batcherRoot_paperOrdinary d hd hd18).net =
      chvatalFinalBatcherNet d := by
  rw [Sorting1830Obligation.net, Sorting1830Obligation.batcherRoot_paperOrdinary,
    NetworkDepthAssemblyObligation.composed]
  exact NetworkDepthAssemblyObligation.of_batcherRoot_emptyOrdFinal_composed
    (Nat.pos_of_ne_zero (by omega : d ≠ 0)) hd18

theorem network_depth_le_1830_of_batcherRoot_paperOrdinary {n d : Nat}
    (hd : 7 ≤ d) (hd18 : d ≤ 18) (hclog : Nat.clog 64 n = d) (hn : 1 < n) :
    ((Sorting1830Obligation.batcherRoot_paperOrdinary d hd hd18).net.depth : ℝ) ≤
      1830 * Real.logb 2 (n : ℝ) - 58657 :=
  network_depth_le_1830_of_sorting1830Obligation hd hclog hn
    (Sorting1830Obligation.batcherRoot_paperOrdinary d hd hd18)

/-! ## Parallel final depth shells (`d ≥ 7`) and pack-tile stage shells -/

/-- For every `d ≥ 7`, the parallel `2^42`-block Batcher meets the paper final budget.
    Global `Sorts` remains `ParallelFinalPuritySortResidual` when `d > 7`. -/
def parallelFinalDepth_ofPaper (d : Nat) (hd : 7 ≤ d) : ParallelFinalDepthObligation d :=
  ParallelFinalDepthObligation.of_parallelBlocks d hd

theorem parallelFinalDepth_ofPaper_le (d : Nat) (hd : 7 ≤ d) :
    (parallelFinalDepth_ofPaper d hd).net.depth ≤ finalSorterPaperDepth :=
  (parallelFinalDepth_ofPaper d hd).hdepth

/-- Depth-only ordinary stage from tiled paper-ordinary packs (`d ≥ 11`).
    Not a sorter; bag-routing / Thm 5.1 placement remains open. -/
def ordinaryPackStage_of_canonical (d : Nat) (hd : 11 ≤ d)
    (σ : Scramble paperOrdinaryGeometry.m paperOrdinaryGeometry.n) :
    OrdinarySeparatorDepthObligation d :=
  OrdinarySeparatorDepthObligation.of_paperOrdinaryCanonical d hd σ

/-- Depth-only root stage from tiled paper-root packs (`d ≥ 14`). -/
def rootPackStage_of_canonical (d : Nat) (hd : 14 ≤ d)
    (σ : Scramble paperRootGeometry.m paperRootGeometry.n) :
    RootSeparatorDepthObligation d :=
  RootSeparatorDepthObligation.of_paperRootCanonical d hd σ

theorem ordinaryPackStage_of_canonical_le (d : Nat) (hd : 11 ≤ d)
    (σ : Scramble paperOrdinaryGeometry.m paperOrdinaryGeometry.n) :
    (ordinaryPackStage_of_canonical d hd σ).net.depth ≤ ordinaryStagePaperDepth :=
  (ordinaryPackStage_of_canonical d hd σ).hdepth

theorem rootPackStage_of_canonical_le (d : Nat) (hd : 14 ≤ d)
    (σ : Scramble paperRootGeometry.m paperRootGeometry.n) :
    (rootPackStage_of_canonical d hd σ).net.depth ≤ rootSeparatorPaperDepth :=
  (rootPackStage_of_canonical d hd σ).hdepth

/-! ## Paper depth-shell assembly (`d ≥ 14`): depth ≤ `totalDepth`, `Sorts` residual -/

/-- Assembled §7 paper depth shells: tiled root/ordinary packs + parallel final.
    Depth meets `totalDepth d` for every `d ≥ 14`.

    **Honest:** this net is a depth shell only. Pack stages are separators (not
    global sorters) and the parallel final sorts all inputs only under block
    purity produced by the §7 outsider schedule. `PaperDepthShellSortResidual`
    packages that open obligation; it is **not** claimed for arbitrary inputs. -/
def paperDepthShellNetwork (d : Nat) (hd : 14 ≤ d)
    (σr : Scramble paperRootGeometry.m paperRootGeometry.n)
    (σo : Scramble paperOrdinaryGeometry.m paperOrdinaryGeometry.n) :
    ComparatorNetwork (64 ^ d) :=
  assembledChvatalNetwork
    (rootPackStage_of_canonical d hd σr).net
    (ordinaryPackStage_of_canonical d (by omega : 11 ≤ d) σo).net
    (parallelFinalDepth_ofPaper d (by omega : 7 ≤ d)).net

theorem paperDepthShellNetwork_depth_le (d : Nat) (hd : 14 ≤ d)
    (σr : Scramble paperRootGeometry.m paperRootGeometry.n)
    (σo : Scramble paperOrdinaryGeometry.m paperOrdinaryGeometry.n) :
    (paperDepthShellNetwork d hd σr σo).depth ≤ totalDepth d := by
  unfold paperDepthShellNetwork
  have h := assembledChvatalNetwork_depth_le (StageDepthBudget.ofPaper d)
    (rootPackStage_of_canonical d hd σr).net
    (ordinaryPackStage_of_canonical d (by omega : 11 ≤ d) σo).net
    (parallelFinalDepth_ofPaper d (by omega : 7 ≤ d)).net
    (rootPackStage_of_canonical_le d hd σr)
    (ordinaryPackStage_of_canonical_le d (by omega : 11 ≤ d) σo)
    (parallelFinalDepth_ofPaper_le d (by omega : 7 ≤ d))
  exact h.trans (StageDepthBudget.depth_sum_le d (StageDepthBudget.ofPaper d))

/-- Open obligation: the depth-shell assembly actually sorts (requires the §7
    outsider/purity schedule, not merely stacking separator packs + parallel
    finals on arbitrary inputs). -/
def PaperDepthShellSortResidual (d : Nat) (hd : 14 ≤ d)
    (σr : Scramble paperRootGeometry.m paperRootGeometry.n)
    (σo : Scramble paperOrdinaryGeometry.m paperOrdinaryGeometry.n) : Prop :=
  ComparatorNetwork.Sorts.{0} (paperDepthShellNetwork d hd σr σo)

/-- If paper depth shells sort for every `d > 603`, then those nets witness
    `Limsup1830Residual`. Discharging `PaperDepthShellSortResidual` needs the
    full §7 schedule, not depth shells alone. -/
theorem exists_totalDepth_of_paperDepthShellSorts {d : Nat}
    (_hd : batcherFitsTotalDepthMax < d) (hd14 : 14 ≤ d)
    (σr : Scramble paperRootGeometry.m paperRootGeometry.n)
    (σo : Scramble paperOrdinaryGeometry.m paperOrdinaryGeometry.n)
    (hs : PaperDepthShellSortResidual d hd14 σr σo) :
    ∃ net : ComparatorNetwork (64 ^ d),
      ComparatorNetwork.Sorts.{0} net ∧ net.depth ≤ totalDepth d :=
  ⟨paperDepthShellNetwork d hd14 σr σo, hs,
    paperDepthShellNetwork_depth_le d hd14 σr σo⟩

end Chvatal
