module
/-
  # Full-wire Batcher on `64^d` vs §7 `totalDepth`

  Isolates Batcher nets and the finite-range padded-1830 depth comparison so
  `Bounds/Chvatal1830Batcher` does not depend on PreferNon trajectory WIP.

  **Kernel-checked:** `chvatalFinalBatcherNet` sorts; depth `≤ bitonicDepthBudget (6d)`;
  `≤ totalDepth d` for `7 ≤ d ≤ 603`; strict excess for `d > 603`.

  **Honest:** this is Batcher, not the paper scramble schedule. Limsup `≤ 1830`
  for all large `n` remains open (`Limsup1830Residual`).
-/

public import AKS.Chvatal.DepthSkeleton
public import AKS.Chvatal.Bound1830
public import AKS.Bitonic.Shrink
public import AKS.Bitonic.TightDepth
public import AKS.Sort.Depth

@[expose] public section

namespace Chvatal

/-! ## Placeholder and Batcher nets on `64^d` -/

/-- Zero-comparator stage on `N = 64^d`. -/
def chvatalEmptyStageNet (d : Nat) : ComparatorNetwork (64 ^ d) :=
  ⟨[]⟩

theorem chvatalEmptyStageNet_depth (d : Nat) :
    (chvatalEmptyStageNet d).depth = 0 :=
  depth_nil

theorem chvatalEmptyStageNet_depth_le_root (d : Nat) :
    (chvatalEmptyStageNet d).depth ≤ rootSeparatorPaperDepth := by
  rw [chvatalEmptyStageNet_depth]
  omega

theorem chvatalEmptyStageNet_depth_le_ordinary (d : Nat) :
    (chvatalEmptyStageNet d).depth ≤ ordinaryStagePaperDepth := by
  rw [chvatalEmptyStageNet_depth]
  omega

/-- §7 final sorter candidate: Batcher bitonic on all `64^d` wires. -/
def chvatalFinalBatcherNet (d : Nat) : ComparatorNetwork (64 ^ d) :=
  bitonicNetwork (64 ^ d)

theorem chvatalFinalBatcherNet_sorts (d : Nat) :
    ComparatorNetwork.Sorts.{0} (chvatalFinalBatcherNet d) :=
  bitonicNetwork_sorts (64 ^ d)

theorem clog2_pow64 (d : Nat) (_hd : 0 < d) : Nat.clog 2 (64 ^ d) = 6 * d := by
  have h64 : (64 : Nat) = 2 ^ 6 := by decide
  calc Nat.clog 2 (64 ^ d)
      = Nat.clog 2 ((2 ^ 6) ^ d) := by rw [h64]
    _ = Nat.clog 2 (2 ^ (6 * d)) := by rw [Nat.pow_mul]
    _ = 6 * d := Nat.clog_pow 2 (6 * d) (by decide : 1 < 2)

theorem chvatalFinalBatcherNet_depth_le (d : Nat) :
    (chvatalFinalBatcherNet d).depth ≤ bitonicDepthBudget (6 * d) := by
  unfold chvatalFinalBatcherNet
  by_cases hd : d = 0
  · subst hd
    have : (bitonicNetwork 1).depth ≤ bitonicDepthBudget (Nat.clog 2 1) :=
      bitonicNetwork_depth_le_budget 1
    simpa [chvatalFinalBatcherNet, pow_zero, show Nat.clog 2 1 = 0 by decide] using this
  · have hpos : 0 < d := Nat.pos_of_ne_zero hd
    calc (bitonicNetwork (64 ^ d)).depth
        ≤ bitonicDepthBudget (Nat.clog 2 (64 ^ d)) :=
          bitonicNetwork_depth_le_budget (64 ^ d)
      _ = bitonicDepthBudget (6 * d) := by rw [clog2_pow64 d hpos]

theorem chvatalFinalBatcherNet_depth_le_903 {d : Nat} (hd : d ≤ 7) :
    (chvatalFinalBatcherNet d).depth ≤ 903 := by
  have h6d : 6 * d ≤ 42 := by omega
  calc (chvatalFinalBatcherNet d).depth
      ≤ bitonicDepthBudget (6 * d) := chvatalFinalBatcherNet_depth_le d
    _ ≤ bitonicDepthBudget 42 := bitonicDepthBudget_mono h6d
    _ = 903 := bitonicDepthBudget_42

theorem chvatalFinalBatcherNet_depth_le_paper {d : Nat} (hd : d ≤ 7) :
    (chvatalFinalBatcherNet d).depth ≤ finalSorterPaperDepth :=
  chvatalFinalBatcherNet_depth_le_903 hd

/-- Full-wire Batcher fits the ordinary-stage paper budget through `d = 14`. -/
theorem bitonicDepthBudget_6d_le_ordinary {d : Nat} (hd : d ≤ 14) :
    bitonicDepthBudget (6 * d) ≤ ordinaryStagePaperDepth := by
  have h6 : 6 * d ≤ 84 := by omega
  have hbud : bitonicDepthBudget (6 * d) ≤ bitonicDepthBudget 84 :=
    bitonicDepthBudget_mono h6
  have h84 : bitonicDepthBudget 84 = 84 * 85 / 2 := by
    unfold bitonicDepthBudget; rfl
  have hval : (84 * 85 / 2 : Nat) = 3570 := by decide
  have hle : (3570 : Nat) ≤ ordinaryStagePaperDepth := by
    unfold ordinaryStagePaperDepth; decide
  calc bitonicDepthBudget (6 * d)
      ≤ bitonicDepthBudget 84 := hbud
    _ = 3570 := by rw [h84, hval]
    _ ≤ ordinaryStagePaperDepth := hle

theorem chvatalFinalBatcherNet_depth_le_ordinary {d : Nat} (_hd : 0 < d) (hd14 : d ≤ 14) :
    (chvatalFinalBatcherNet d).depth ≤ ordinaryStagePaperDepth :=
  (chvatalFinalBatcherNet_depth_le d).trans (bitonicDepthBudget_6d_le_ordinary hd14)

/-- Full-wire Batcher fits the root-stage paper budget through `d = 18`. -/
theorem bitonicDepthBudget_6d_le_root {d : Nat} (hd : d ≤ 18) :
    bitonicDepthBudget (6 * d) ≤ rootSeparatorPaperDepth := by
  have h6 : 6 * d ≤ 108 := by omega
  have hbud : bitonicDepthBudget (6 * d) ≤ bitonicDepthBudget 108 :=
    bitonicDepthBudget_mono h6
  have h108 : bitonicDepthBudget 108 = 108 * 109 / 2 := by
    unfold bitonicDepthBudget; rfl
  have hval : (108 * 109 / 2 : Nat) = 5886 := by decide
  have hle : (5886 : Nat) ≤ rootSeparatorPaperDepth := by
    unfold rootSeparatorPaperDepth; decide
  calc bitonicDepthBudget (6 * d)
      ≤ bitonicDepthBudget 108 := hbud
    _ = 5886 := by rw [h108, hval]
    _ ≤ rootSeparatorPaperDepth := hle

theorem chvatalFinalBatcherNet_depth_le_root {d : Nat} (_hd : 0 < d) (hd18 : d ≤ 18) :
    (chvatalFinalBatcherNet d).depth ≤ rootSeparatorPaperDepth :=
  (chvatalFinalBatcherNet_depth_le d).trans (bitonicDepthBudget_6d_le_root hd18)

/-! ## Full-wire Batcher vs §7 `totalDepth` (finite `d` range) -/

/-- On `7 ≤ d ≤ 603`, the bitonic budget on `6d` bits is at most `totalDepth d`. -/
theorem bitonicDepthBudget_6d_le_totalDepth {d : Nat} (hd : 7 ≤ d)
    (hmax : d ≤ batcherFitsTotalDepthMax) :
    bitonicDepthBudget (6 * d) ≤ totalDepth d := by
  unfold batcherFitsTotalDepthMax at hmax
  have htot := totalDepth_eq d hd
  have hge : 69637 ≤ 10980 * d := by omega
  rw [htot]
  have h2eq := bitonicDepthBudget_double (6 * d)
  have hmul : (6 * d) * (6 * d + 1) ≤ 2 * (10980 * d - 69637) := by
    have h36_ok : 36 * d ≤ 21954 := by
      have : 36 * d ≤ 36 * 603 := Nat.mul_le_mul_left 36 hmax
      exact this.trans (by decide)
    have h246le : 246 ≤ 36 * d := by
      have : 36 * 7 ≤ 36 * d := Nat.mul_le_mul_left 36 hd
      exact (by decide : 246 ≤ 36 * 7).trans this
    have hg : d * (21954 - 36 * d) =
        603 * 246 + (603 - d) * (36 * d - 246) := by
      zify [h36_ok, h246le, hmax]
      ring
    have h603 : (603 * 246 : Nat) = 148338 := by decide
    have hge' : 139274 ≤ d * (21954 - 36 * d) := by
      rw [hg, h603]
      exact (by decide : 139274 ≤ 148338).trans (Nat.le_add_right 148338 _)
    have hrew : d * (21954 - 36 * d) = 21954 * d - 36 * d * d := by
      have h1 : d * (21954 - 36 * d) = d * 21954 - d * (36 * d) :=
        Nat.mul_sub_left_distrib _ _ _
      have h2 : d * 21954 = 21954 * d := Nat.mul_comm _ _
      have h3 : d * (36 * d) = 36 * d * d := by
        calc d * (36 * d) = (d * 36) * d := by rw [Nat.mul_assoc]
          _ = (36 * d) * d := by rw [Nat.mul_comm d 36]
          _ = 36 * d * d := by rw [Nat.mul_assoc]
      calc d * (21954 - 36 * d)
          = d * 21954 - d * (36 * d) := h1
        _ = 21954 * d - d * (36 * d) := by rw [h2]
        _ = 21954 * d - 36 * d * d := by rw [h3]
    have hA : 36 * d * d + 139274 ≤ 21954 * d := by
      have := hge'
      rw [hrew] at this
      omega
    have hL : (6 * d) * (6 * d + 1) = 36 * d * d + 6 * d := by ring
    have hR : 2 * (10980 * d - 69637) = 21960 * d - 139274 := by omega
    rw [hL, hR]
    omega
  have : 2 * bitonicDepthBudget (6 * d) ≤ 2 * (10980 * d - 69637) := by
    rwa [h2eq]
  omega

theorem chvatalFinalBatcherNet_depth_le_totalDepth {d : Nat} (hd : 7 ≤ d)
    (hmax : d ≤ batcherFitsTotalDepthMax) :
    (chvatalFinalBatcherNet d).depth ≤ totalDepth d :=
  (chvatalFinalBatcherNet_depth_le d).trans (bitonicDepthBudget_6d_le_totalDepth hd hmax)

/-- Past `d = 603`, the bitonic budget on `6d` bits strictly exceeds `totalDepth d`. -/
theorem bitonicDepthBudget_6d_gt_totalDepth {d : Nat}
    (hd : batcherFitsTotalDepthMax < d) :
    totalDepth d < bitonicDepthBudget (6 * d) := by
  unfold batcherFitsTotalDepthMax at hd
  have h604le : 604 ≤ d := Nat.succ_le_of_lt hd
  have hbase : totalDepth 604 < bitonicDepthBudget (6 * 604) := by
    have htot : totalDepth 604 = 10980 * 604 - 69637 :=
      totalDepth_eq 604 (by decide)
    have hbit : bitonicDepthBudget (6 * 604) = (6 * 604) * (6 * 604 + 1) / 2 :=
      bitonicDepthBudget_eq (6 * 604)
    rw [htot, hbit]
    decide
  have hstep : ∀ k, 604 ≤ k → totalDepth k < bitonicDepthBudget (6 * k) →
      totalDepth (k + 1) < bitonicDepthBudget (6 * (k + 1)) := by
    intro k hk ih
    have hk7 : 7 ≤ k := (by decide : 7 ≤ 604).trans hk
    have hk7' : 7 ≤ k + 1 := le_trans hk7 (Nat.le_succ k)
    have htot_step : totalDepth (k + 1) = totalDepth k + 10980 := by
      rw [totalDepth_eq (k + 1) hk7', totalDepth_eq k hk7]
      omega
    have hbit_step :
        bitonicDepthBudget (6 * (k + 1)) =
          bitonicDepthBudget (6 * k) + (36 * k + 21) := by
      have h2a := bitonicDepthBudget_double (6 * (k + 1))
      have h2b := bitonicDepthBudget_double (6 * k)
      have hR : (6 * (k + 1)) * (6 * (k + 1) + 1) =
          (6 * k) * (6 * k + 1) + 2 * (36 * k + 21) := by ring
      have : 2 * bitonicDepthBudget (6 * (k + 1)) =
          2 * (bitonicDepthBudget (6 * k) + (36 * k + 21)) := by
        calc 2 * bitonicDepthBudget (6 * (k + 1))
            = (6 * (k + 1)) * (6 * (k + 1) + 1) := h2a
          _ = (6 * k) * (6 * k + 1) + 2 * (36 * k + 21) := hR
          _ = 2 * bitonicDepthBudget (6 * k) + 2 * (36 * k + 21) := by rw [h2b]
          _ = 2 * (bitonicDepthBudget (6 * k) + (36 * k + 21)) := by ring
      omega
    have hinc : 10980 ≤ 36 * k + 21 := by
      have hmul : 36 * 604 + 21 ≤ 36 * k + 21 :=
        Nat.add_le_add_right (Nat.mul_le_mul_left 36 hk) 21
      exact (by decide : 10980 ≤ 36 * 604 + 21).trans hmul
    calc totalDepth (k + 1)
        = totalDepth k + 10980 := htot_step
      _ < bitonicDepthBudget (6 * k) + 10980 := Nat.add_lt_add_right ih 10980
      _ ≤ bitonicDepthBudget (6 * k) + (36 * k + 21) := Nat.add_le_add_left hinc _
      _ = bitonicDepthBudget (6 * (k + 1)) := hbit_step.symm
  have helper : ∀ n, totalDepth (604 + n) < bitonicDepthBudget (6 * (604 + n)) := by
    intro n
    induction n with
    | zero =>
      change totalDepth (604 + 0) < bitonicDepthBudget (6 * (604 + 0))
      simpa only [Nat.add_zero] using hbase
    | succ n ih =>
      have h := hstep (604 + n) (Nat.le_add_right 604 n) ih
      exact (Nat.add_assoc 604 n 1 ▸ h)
  have hdecomp : d = 604 + (d - 604) := (Nat.add_sub_of_le h604le).symm
  rw [hdecomp]
  exact helper (d - 604)

theorem not_bitonicDepthBudget_6d_le_totalDepth_of_gt_max {d : Nat}
    (hd : batcherFitsTotalDepthMax < d) :
    ¬ bitonicDepthBudget (6 * d) ≤ totalDepth d :=
  not_le_of_gt (bitonicDepthBudget_6d_gt_totalDepth hd)

/-! ## Direct Batcher padded bound for `7 ≤ d ≤ 603` -/

theorem network_depth_le_1830_pow_of_batcher {d : Nat} (hd : 7 ≤ d)
    (hmax : d ≤ batcherFitsTotalDepthMax) :
    ((chvatalFinalBatcherNet d).depth : ℝ) ≤
      1830 * Real.logb 2 ((64 ^ d : ℕ) : ℝ) - 58657 :=
  network_depth_le_1830_logb_of_totalDepth hd (clog64_pow_eq d)
    (Nat.one_lt_pow (by omega : d ≠ 0) (by norm_num : 1 < 64))
    (chvatalFinalBatcherNet d)
    (chvatalFinalBatcherNet_sorts d : ComparatorNetwork.Sorts.{0} _)
    (chvatalFinalBatcherNet_depth_le_totalDepth hd hmax)

theorem network_depth_le_1830_of_batcher {n d : Nat} (hd : 7 ≤ d)
    (hmax : d ≤ batcherFitsTotalDepthMax) (hclog : Nat.clog 64 n = d) (hn : 1 < n) :
    ((chvatalFinalBatcherNet d).depth : ℝ) ≤
      1830 * Real.logb 2 (n : ℝ) - 58657 :=
  network_depth_le_1830_logb_of_totalDepth hd hclog hn
    (chvatalFinalBatcherNet d)
    (chvatalFinalBatcherNet_sorts d : ComparatorNetwork.Sorts.{0} _)
    (chvatalFinalBatcherNet_depth_le_totalDepth hd hmax)

end Chvatal
