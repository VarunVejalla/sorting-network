import RaggedResetGeometry
import RaggedFlowContract
import Mathlib.Tactic

set_option maxHeartbeats 800000

namespace Tapered945

/-- Rows allocated at the root's second round to address `x`. The scale is
chosen so that the actual wire count agrees with the first-round up-flow. -/
def rootStage2Rows (x : Nat) : Nat := 1024 * bootstrapUpRows x

theorem root_stage2_rows_pos (x : Nat) : 0 < rootStage2Rows x := by
  unfold rootStage2Rows bootstrapUpRows
  split_ifs <;> norm_num

theorem root_stage2_row_wire_exact (d x : Nat) (hd : 14 ≤ d) :
    rootStage2Rows x * (2 ^ (6 * d - 59)) =
      bootstrapUpRows x * bootstrapColumns d := by
  unfold rootStage2Rows bootstrapColumns
  rw [show 6 * d - 49 = 10 + (6 * d - 59) by omega, pow_add]
  norm_num
  ring

/-- The 64 root row widths exactly fill the fixed root matrix. -/
theorem root_stage2_rows_sum :
    (∑ x ∈ Finset.range 64, rootStage2Rows x) = bootstrapRows := by
  norm_num [rootStage2Rows, bootstrapRows, bootstrapUpRows,
    isEndAddress, Finset.sum_range_succ]

/-- The root's 64 address-dependent stage-two blocks form a full ragged
profile. Its first cut is positive because the first block has positive width;
later cut bounds follow from monotonicity of prefix sums. -/
def rootStage2RaggedProfile : RaggedFlowContract bootstrapRows where
  start := 0
  rightFringe := 0
  width := rootStage2Rows
  widths_pos := by
    intro x _
    exact root_stage2_rows_pos x
  conservation := by
    simp only [zero_add, add_zero]
    exact root_stage2_rows_sum
  cut_pos := by
    intro j hj
    have hmem : 0 ∈ Finset.range j := Finset.mem_range.mpr hj
    have hfirst := Finset.single_le_sum
      (f := rootStage2Rows) (fun i hi => Nat.zero_le _) hmem
    simpa [raggedPrefixRows] using
      le_trans (Nat.succ_le_of_lt (root_stage2_rows_pos 0)) hfirst
  prefix_bound := by
    intro j hj
    simp only [zero_add, Nat.sub_zero]
    calc
      (∑ i ∈ Finset.range j, rootStage2Rows i) ≤
          ∑ i ∈ Finset.range 64, rootStage2Rows i := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hj)
        intro i hi hnot
        exact Nat.zero_le _
      _ = bootstrapRows := root_stage2_rows_sum

/-- The first-round level-one up-flow is exactly the root's assigned block
width measured in stage-one columns. -/
theorem root_stage2_block_exact (d x : Nat) (hd : 14 ≤ d) :
    rootStage2Rows x * (2 ^ (6 * d - 59)) =
      bootstrapUpRows x * bootstrapColumns d :=
  root_stage2_row_wire_exact d x hd

/-- Summed reset up-flow plus the root block equals the stage-three top size.
The proof uses exact conservation in each of the 64 stage-two senders. -/
theorem reset_ups_plus_root_block_eq_stage_three_top
    (d x : Nat) (hd : 14 ≤ d) :
    (∑ j ∈ Finset.range 64, resetUpCount d x j) +
      bootstrapUpRows x * bootstrapColumns d = seedStageThreeTopSize d := by
  have hslot := bootstrap_slots_sum x
  have hmass : resetDownCount d = 1020 * resetUnit d := rfl
  have hsumInputs :
      (∑ j ∈ Finset.range 64, resetSenderInput d x j) =
        (64 * bootstrapAverageDownRows x) * bootstrapColumns d := by
    have hslots :
        (∑ j ∈ Finset.range 64, bootstrapSlotRows x j) =
          64 * bootstrapAverageDownRows x := by
      rw [← Fin.sum_univ_eq_sum_range (fun j : Nat => bootstrapSlotRows x j)]
      exact bootstrap_slots_sum x
    simp only [resetSenderInput]
    rw [← Finset.sum_mul, hslots]
  have hsumConstant :
      (∑ j ∈ Finset.range 64, 64 * resetDownCount d) =
        64 * (64 * resetDownCount d) := by
    simp
  have hsumUps :
      (∑ j ∈ Finset.range 64, resetUpCount d x j) +
        64 * (64 * resetDownCount d) =
        (64 * bootstrapAverageDownRows x) * bootstrapColumns d := by
    calc
      _ = (∑ j ∈ Finset.range 64, resetUpCount d x j) +
          (∑ j ∈ Finset.range 64, 64 * resetDownCount d) := by rw [hsumConstant]
      _ = ∑ j ∈ Finset.range 64, resetSenderInput d x j := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        exact (reset_sender_conserves d x j hd).symm
      _ = _ := hsumInputs
  have havg : bootstrapRows = bootstrapUpRows x +
      64 * bootstrapAverageDownRows x := by
    have h := bootstrap_avg_split x
    rw [← bootstrap_fringe_rows_exact] at h
    omega
  have hcols : bootstrapRows * bootstrapColumns d = seedRootDown d := by
    exact (bootstrap_input_factorization d hd).symm
  have htarget : seedRootDown d - 64 * (64 * resetDownCount d) =
      seedStageThreeTopSize d := by
    rw [hmass]
    unfold seedRootDown seedStageThreeTopSize
    have hp1 : 2 ^ (6 * d - 6) = 2 ^ 22 * resetUnit d := by
      unfold resetUnit
      rw [show 6 * d - 6 = 22 + (6 * d - 28) by omega, pow_add]
    have hp2 : 2 ^ (6 * d - 14) = 2 ^ 14 * resetUnit d := by
      unfold resetUnit
      rw [show 6 * d - 14 = 14 + (6 * d - 28) by omega, pow_add]
    rw [hp1, hp2]
    norm_num
    omega
  have hwhole :
      ((∑ j ∈ Finset.range 64, resetUpCount d x j) +
        bootstrapUpRows x * bootstrapColumns d) +
          64 * (64 * resetDownCount d) = seedRootDown d := by
    calc
      _ = ((∑ j ∈ Finset.range 64, resetUpCount d x j) +
          64 * (64 * resetDownCount d)) +
            bootstrapUpRows x * bootstrapColumns d := by omega
      _ = (64 * bootstrapAverageDownRows x) * bootstrapColumns d +
            bootstrapUpRows x * bootstrapColumns d := by rw [hsumUps]
      _ = (64 * bootstrapAverageDownRows x + bootstrapUpRows x) *
            bootstrapColumns d := by rw [← Nat.add_mul]
      _ = bootstrapRows * bootstrapColumns d := by
        rw [Nat.add_comm, ← havg]
      _ = seedRootDown d := hcols
  omega

/-- The canonical stage-three bottom count is the common reset down-count. -/
theorem reset_down_eq_stage_three_bottom (d : Nat) (hd : 14 ≤ d) :
    resetDownCount d = seedStageThreeBottomSize d := by
  unfold resetDownCount resetUnit seedStageThreeBottomSize seedBottomDown2
  rw [show 6 * d - 18 = 10 + (6 * d - 28) by omega,
    show 6 * d - 26 = 2 + (6 * d - 28) by omega, pow_add, pow_add]
  norm_num
  omega

end Tapered945
