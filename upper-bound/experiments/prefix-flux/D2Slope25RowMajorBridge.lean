import D2Slope25LiftArea
import D2RowMajorMismatch

open scoped BigOperators
open Chvatal.D2Slope25LiftArea
open Chvatal.D2RowMajorMismatch
open Chvatal.D2RankAlignment

set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

namespace Chvatal.D2Slope25RowMajorBridge

abbrev Col := Fin 64

private theorem boundary_le_later (boundary : Nat → Nat)
    (hmono : ∀ i, boundary i ≤ boundary (i + 1)) :
    ∀ i j, i ≤ j → boundary i ≤ boundary j := by
  intro i j hij
  induction j with
  | zero =>
      have : i = 0 := by omega
      subst i
      exact le_rfl
  | succ j ih =>
      by_cases hle : i ≤ j
      · exact le_trans (ih hle) (by simpa using hmono j)
      · have : i = j + 1 := by omega
        subst i
        exact le_rfl

def exactRankPortError {ports : Nat} (actual : Col → Nat) (boundary : Nat → Nat)
    (H : Nat) (p : Fin ports) : Rat :=
  abs ((Finset.univ.sum fun c : Col =>
      (Chvatal.D2RankAlignment.prefixIntervalMass (actual c)
        (Chvatal.D2RankAlignment.flatBoundaryColumnCut 4096 64 (boundary p.val) c.val)
        (Chvatal.D2RankAlignment.flatBoundaryColumnCut 4096 64 (boundary (p.val + 1)) c.val) : Rat)) -
    (Chvatal.D2RankAlignment.prefixIntervalMass H (boundary p.val)
      (boundary (p.val + 1)) : Rat))

def exactRankPortActualCount {ports : Nat} (actual : Col → Nat)
    (boundary : Nat → Nat) (p : Fin ports) : Nat :=
  Finset.univ.sum fun c : Col =>
    prefixIntervalMass (actual c)
      (flatBoundaryColumnCut 4096 64 (boundary p.val) c.val)
      (flatBoundaryColumnCut 4096 64 (boundary (p.val + 1)) c.val)

def exactRankPortTargetCount {ports : Nat} (boundary : Nat → Nat)
    (H : Nat) (p : Fin ports) : Nat :=
  prefixIntervalMass H (boundary p.val) (boundary (p.val + 1))

private theorem rat_countDistance_eq_abs (a b : Nat) :
    (countDistance a b : Rat) = abs ((a : Rat) - (b : Rat)) := by
  unfold countDistance
  by_cases hab : a ≤ b
  · have hz : a - b = 0 := Nat.sub_eq_zero_of_le hab
    have hsub : ((b - a : Nat) : Rat) = (b : Rat) - (a : Rat) :=
      Nat.cast_sub hab
    push_cast
    rw [hz, hsub]
    rw [abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast hab))]
    ring
  · have hba : b ≤ a := Nat.le_of_not_ge hab
    have hz : b - a = 0 := Nat.sub_eq_zero_of_le hba
    have hsub : ((a - b : Nat) : Rat) = (a : Rat) - (b : Rat) :=
      Nat.cast_sub hba
    push_cast
    rw [hz, hsub]
    rw [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hba))]
    ring

/-- If each cut's column-uniform reference agrees with the row-major
piecewise-linear reference, the checked local 416 allowance and the checked
rank-layout variation 32 combine into an exact-rank port error of 448. -/
theorem fullHeightTwoShuffle_exact_rank_port_l1_le_448
    (sourceHeight : Col → Nat) (boundary : Nat → Nat) (ports H : Nat)
    (hzero : boundary 0 = 0)
    (hend : boundary ports = 64 * 4096)
    (hmono : ∀ i, boundary i ≤ boundary (i + 1))
    (hH : H ≤ 64 * 4096)
    (hHsum : H = Finset.univ.sum fun c : Col => fullHeightTwoShuffle sourceHeight c)
    (hinput : ∀ c, sourceHeight c ≤ 4096) :
    (Finset.univ.sum fun p : Fin ports => exactRankPortError
      (fun c => fullHeightTwoShuffle sourceHeight c) boundary H p) ≤ 448 := by
  let actual : Col → Nat := fun c => fullHeightTwoShuffle sourceHeight c
  let cuts : Col → Nat → Nat := fun c i =>
    flatBoundaryColumnCut 4096 64 (boundary i) c.val
  have hzeroCuts : ∀ c, cuts c 0 = 0 := by
    intro c
    change flatBoundaryColumnCut 4096 64 (boundary 0) c.val = 0
    rw [hzero]
    exact flatBoundaryColumnCut_zero 4096 64 c.val
  have hendCuts : ∀ c, cuts c ports = 4096 := by
    intro c
    change flatBoundaryColumnCut 4096 64 (boundary ports) c.val = 4096
    rw [hend]
    exact flatBoundaryColumnCut_full 4096 64 c.val c.isLt
  have hmonoCuts : ∀ c i, i < ports → cuts c i ≤ cuts c (i + 1) := by
    intro c i hi
    exact flatBoundaryColumnCut_mono 4096 64
      (boundary i) (boundary (i + 1)) c.val (hmono i)
  have hlocal := fullHeightTwoShuffle_ragged_port_l1_le_416
    sourceHeight cuts ports hzeroCuts hendCuts (by
      intro c i hi
      exact hmonoCuts c i hi) hinput

  have hrank := rowMajor_complete_port_rank_correction_le_32 H 4096 ports
    boundary hH hzero hend hmono

  have hboundaryBound : ∀ i, i ≤ ports → boundary i ≤ 64 * 4096 := by
    intro i hi
    calc
      boundary i ≤ boundary ports := boundary_le_later boundary hmono i ports hi
      _ = 64 * 4096 := hend

  have hpoint (p : Fin ports) :
      exactRankPortError actual boundary H p ≤
        rectangularPortError actual cuts p +
          |rowMajorBoundaryDiscrepancy H (boundary (p.val + 1)) -
            rowMajorBoundaryDiscrepancy H (boundary p.val)| := by
    let b0 := boundary p.val
    let b1 := boundary (p.val + 1)
    have hb0 : b0 ≤ 64 * 4096 := by
      dsimp [b0]
      exact hboundaryBound p.val (Nat.le_of_lt p.isLt)
    have hb1 : b1 ≤ 64 * 4096 := by
      dsimp [b1]
      exact hboundaryBound (p.val + 1) (Nat.succ_le_of_lt p.isLt)
    have hcutmono : ∀ c, cuts c p.val ≤ cuts c (p.val + 1) := by
      intro c
      exact hmonoCuts c p.val p.isLt
    have hlocalRef :
        (Finset.univ.sum fun c : Col =>
          Chvatal.D2RankAlignment.ratPrefixIntervalMass
            (rectangularUniformDensity actual * 4096)
            (cuts c p.val : Rat) (cuts c (p.val + 1) : Rat)) =
          rowMajorUniformPrefix H b1 - rowMajorUniformPrefix H b0 := by
      have hden : rectangularUniformDensity actual * 4096 = (H : Rat) / 64 := by
        dsimp [rectangularUniformDensity, actual]
        have hHsumR : (H : Rat) =
            Finset.univ.sum fun c : Col => (fullHeightTwoShuffle sourceHeight c : Rat) := by
          exact_mod_cast hHsum
        rw [← hHsumR]
        field_simp
      rw [hden]
      have hcum (b : Nat) (hb : b ≤ 64 * 4096) :
          Finset.univ.sum (fun c : Col =>
            Chvatal.D2RankAlignment.ratPrefixIntervalMass ((H : Rat) / 64) 0
              (flatBoundaryColumnCut 4096 64 b c.val : Rat)) =
            rowMajorUniformPrefix H b :=
          rowMajorUniformPrefix_eq_flat_column_sum H 4096 b hb
      have hinterval (c : Col) :
          ratPrefixIntervalMass ((H : Rat) / 64)
              (flatBoundaryColumnCut 4096 64 b0 c.val : Rat)
              (flatBoundaryColumnCut 4096 64 b1 c.val : Rat) =
            ratPrefixIntervalMass ((H : Rat) / 64) 0
                (flatBoundaryColumnCut 4096 64 b1 c.val : Rat) -
              ratPrefixIntervalMass ((H : Rat) / 64) 0
                (flatBoundaryColumnCut 4096 64 b0 c.val : Rat) := by
        have hmono' : flatBoundaryColumnCut 4096 64 b0 c.val ≤
            flatBoundaryColumnCut 4096 64 b1 c.val := by
          exact flatBoundaryColumnCut_mono 4096 64 b0 b1 c.val (hmono p.val)
        rw [ratPrefixIntervalMass_eq_cumulative_diff _ _ _ (by exact_mod_cast hmono')]
        have hheight : 0 ≤ (H : Rat) / 64 :=
          div_nonneg (Nat.cast_nonneg H) (by norm_num)
        have hzero0 : ratPrefixIntervalMass ((H : Rat) / 64) 0
            (flatBoundaryColumnCut 4096 64 b0 c.val : Rat) =
            min ((H : Rat) / 64) (flatBoundaryColumnCut 4096 64 b0 c.val : Rat) := by
          rw [ratPrefixIntervalMass_eq_cumulative_diff]
          · rw [min_eq_right hheight]
            ring
          · exact_mod_cast Nat.zero_le (flatBoundaryColumnCut 4096 64 b0 c.val)
        have hzero1 : ratPrefixIntervalMass ((H : Rat) / 64) 0
            (flatBoundaryColumnCut 4096 64 b1 c.val : Rat) =
            min ((H : Rat) / 64) (flatBoundaryColumnCut 4096 64 b1 c.val : Rat) := by
          rw [ratPrefixIntervalMass_eq_cumulative_diff]
          · rw [min_eq_right hheight]
            ring
          · exact_mod_cast Nat.zero_le (flatBoundaryColumnCut 4096 64 b1 c.val)
        rw [hzero0, hzero1]
      dsimp [cuts, b0, b1]
      have hsumInterval :
          (Finset.univ.sum fun c : Col =>
            ratPrefixIntervalMass ((H : Rat) / 64)
              (flatBoundaryColumnCut 4096 64 (boundary p.val) c.val : Rat)
              (flatBoundaryColumnCut 4096 64 (boundary (p.val + 1)) c.val : Rat)) =
            Finset.univ.sum (fun c : Col =>
              ratPrefixIntervalMass ((H : Rat) / 64) 0
                (flatBoundaryColumnCut 4096 64 (boundary (p.val + 1)) c.val : Rat) -
              ratPrefixIntervalMass ((H : Rat) / 64) 0
                (flatBoundaryColumnCut 4096 64 (boundary p.val) c.val : Rat)) := by
        apply Finset.sum_congr rfl
        intro c hc
        exact hinterval c
      rw [hsumInterval, Finset.sum_sub_distrib,
        hcum (boundary (p.val + 1)) hb1, hcum (boundary p.val) hb0]
    have hexactCum :=
      Chvatal.D2RankAlignment.prefixIntervalMass_eq_cumulative_diff_nat
        H b0 b1 (hmono p.val)
    have hlocalErr : rectangularPortError actual cuts p =
        abs ((Finset.univ.sum fun c : Col =>
          (Chvatal.D2RankAlignment.prefixIntervalMass (actual c)
            (cuts c p.val) (cuts c (p.val + 1)) : Rat)) -
          (rowMajorUniformPrefix H b1 - rowMajorUniformPrefix H b0)) := by
      simp [rectangularPortError, hlocalRef]
    have hdiscrepancy :
        ((Chvatal.D2RankAlignment.prefixIntervalMass H b0 b1 : Rat) -
          (rowMajorUniformPrefix H b1 - rowMajorUniformPrefix H b0)) =
          rowMajorBoundaryDiscrepancy H b1 - rowMajorBoundaryDiscrepancy H b0 := by
      have hnat := prefixIntervalMass_eq_cumulative_diff_nat H b0 b1 (hmono p.val)
      have hmin : min H b0 ≤ min H b1 := min_le_min_left H (hmono p.val)
      have hcast : ((min H b1 - min H b0 : Nat) : Rat) =
          (min (H : Rat) b1 - min (H : Rat) b0) := by
        rw [Nat.cast_sub hmin, Nat.cast_min, Nat.cast_min]
      rw [hnat, hcast]
      simp [rowMajorBoundaryDiscrepancy]
      ring
    rw [show exactRankPortError actual boundary H p =
      abs ((Finset.univ.sum fun c : Col =>
        (Chvatal.D2RankAlignment.prefixIntervalMass (actual c)
          (cuts c p.val) (cuts c (p.val + 1)) : Rat)) -
        (Chvatal.D2RankAlignment.prefixIntervalMass H b0 b1 : Rat)) by
      simp [exactRankPortError, actual, cuts, b0, b1]]
    rw [hlocalErr]
    let A := Finset.univ.sum fun c : Col =>
        (Chvatal.D2RankAlignment.prefixIntervalMass (actual c)
          (cuts c p.val) (cuts c (p.val + 1)) : Rat)
    have hdecomp :
        (A - (Chvatal.D2RankAlignment.prefixIntervalMass H b0 b1 : Rat)) =
          (A - (rowMajorUniformPrefix H b1 - rowMajorUniformPrefix H b0)) -
            (rowMajorBoundaryDiscrepancy H b1 - rowMajorBoundaryDiscrepancy H b0) := by
      calc
        _ = (A - (rowMajorUniformPrefix H b1 - rowMajorUniformPrefix H b0)) -
              ((Chvatal.D2RankAlignment.prefixIntervalMass H b0 b1 : Rat) -
                (rowMajorUniformPrefix H b1 - rowMajorUniformPrefix H b0)) := by ring
        _ = _ := by rw [hdiscrepancy]
    rw [hdecomp]
    change |(A - (rowMajorUniformPrefix H b1 - rowMajorUniformPrefix H b0)) -
      (rowMajorBoundaryDiscrepancy H b1 - rowMajorBoundaryDiscrepancy H b0)| ≤ _
    have htri := abs_sub_le
      (A - (rowMajorUniformPrefix H b1 - rowMajorUniformPrefix H b0))
      (0 : Rat)
      (rowMajorBoundaryDiscrepancy H b1 - rowMajorBoundaryDiscrepancy H b0)
    simpa [abs_sub_comm] using htri

  calc
    (Finset.univ.sum fun p : Fin ports => exactRankPortError actual boundary H p) ≤
        (Finset.univ.sum fun p : Fin ports => rectangularPortError actual cuts p) +
          Finset.univ.sum (fun p : Fin ports =>
            |rowMajorBoundaryDiscrepancy H (boundary (p.val + 1)) -
              rowMajorBoundaryDiscrepancy H (boundary p.val)|) := by
      calc
        _ ≤ Finset.univ.sum (fun p : Fin ports =>
              rectangularPortError actual cuts p +
                |rowMajorBoundaryDiscrepancy H (boundary (p.val + 1)) -
                  rowMajorBoundaryDiscrepancy H (boundary p.val)|) :=
          Finset.sum_le_sum fun p hp => hpoint p
        _ = _ := Finset.sum_add_distrib
    _ ≤ 416 + 32 := add_le_add hlocal (by
      rw [Fin.sum_univ_eq_sum_range (fun i : Nat =>
        |rowMajorBoundaryDiscrepancy H (boundary (i + 1)) -
          rowMajorBoundaryDiscrepancy H (boundary i)|) ports]
      exact hrank)
    _ = 448 := by norm_num

/-- The exact-rank port errors conserve total mass, so each direction of
leakage is at most half the 448 l1 allowance: 224 wires per 4096-by-64 core. -/
theorem fullHeightTwoShuffle_directional_leakage_le_224
    (sourceHeight : Col → Nat) (boundary : Nat → Nat) (ports H : Nat)
    (hzero : boundary 0 = 0)
    (hend : boundary ports = 64 * 4096)
    (hmono : ∀ i, boundary i ≤ boundary (i + 1))
    (hH : H ≤ 64 * 4096)
    (hHsum : H = Finset.univ.sum fun c : Col => fullHeightTwoShuffle sourceHeight c)
    (hinput : ∀ c, sourceHeight c ≤ 4096) :
    (Finset.univ.sum fun p : Fin ports =>
      exactRankPortActualCount (fun c => fullHeightTwoShuffle sourceHeight c) boundary p -
        exactRankPortTargetCount boundary H p) ≤ 224 ∧
    (Finset.univ.sum fun p : Fin ports =>
      exactRankPortTargetCount boundary H p -
        exactRankPortActualCount (fun c => fullHeightTwoShuffle sourceHeight c) boundary p) ≤ 224 := by
  let actual : Col → Nat := fun c => fullHeightTwoShuffle sourceHeight c
  let cuts : Col → Nat → Nat := fun c i =>
    flatBoundaryColumnCut 4096 64 (boundary i) c.val
  have hmonoBounded : ∀ i < ports, boundary i ≤ boundary (i + 1) := by
    intro i hi
    exact hmono i
  have hcolumnPartition := flat_boundary_column_cuts_partition
    4096 64 ports boundary hzero hend hmonoBounded
  have hactualTotal :
      (Finset.univ.sum fun p : Fin ports => exactRankPortActualCount actual boundary p) = H := by
    simp only [exactRankPortActualCount]
    rw [Fin.sum_univ_eq_sum_range (fun i : Nat =>
      Finset.univ.sum fun c : Col =>
        prefixIntervalMass (actual c) (cuts c i) (cuts c (i + 1)))]
    rw [Finset.sum_comm]
    calc
      (Finset.univ.sum fun c : Col =>
        Finset.sum (Finset.range ports) fun i =>
          prefixIntervalMass (actual c) (cuts c i) (cuts c (i + 1))) =
        Finset.univ.sum fun c : Col => actual c := by
          apply Finset.sum_congr rfl
          intro c hc
          have hpart := prefixIntervalMass_partition (actual c) (cuts c) ports 4096
            (hcolumnPartition c c.isLt).1
            (hcolumnPartition c c.isLt).2.1
            (by intro i hi; exact (hcolumnPartition c c.isLt).2.2 i hi)
          have hfull : prefixIntervalMass (actual c) 0 4096 = actual c := by
            unfold prefixIntervalMass
            have ha := fullHeightTwoShuffle_le_4096 sourceHeight hinput c
            have ha' : actual c ≤ 4096 := by simpa [actual] using ha
            omega
          rw [hfull] at hpart
          exact hpart
      _ = H := hHsum.symm
  have htargetTotal :
      (Finset.univ.sum fun p : Fin ports => exactRankPortTargetCount boundary H p) = H := by
    simp only [exactRankPortTargetCount]
    rw [Fin.sum_univ_eq_sum_range (fun i : Nat =>
      prefixIntervalMass H (boundary i) (boundary (i + 1)))]
    have hpart := prefixIntervalMass_partition H boundary ports (64 * 4096)
      hzero hend hmonoBounded
    have hfull : prefixIntervalMass H 0 (64 * 4096) = H := by
      unfold prefixIntervalMass
      omega
    rw [hfull] at hpart
    exact hpart
  have hL1Rat := fullHeightTwoShuffle_exact_rank_port_l1_le_448
    sourceHeight boundary ports H hzero hend hmono hH hHsum hinput
  have hL1Cast :
      ((Finset.univ.sum fun p : Fin ports =>
        countDistance (exactRankPortActualCount actual boundary p)
          (exactRankPortTargetCount boundary H p) : Nat) : Rat) ≤ 448 := by
    rw [Nat.cast_sum]
    calc
      Finset.univ.sum (fun p : Fin ports =>
          (countDistance (exactRankPortActualCount actual boundary p)
            (exactRankPortTargetCount boundary H p) : Rat)) =
        Finset.univ.sum fun p : Fin ports => exactRankPortError actual boundary H p := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [rat_countDistance_eq_abs]
          simp [exactRankPortError, exactRankPortActualCount,
            exactRankPortTargetCount, actual, Nat.cast_sum]
      _ ≤ 448 := hL1Rat
  have hL1Nat :
      (Finset.univ.sum fun p : Fin ports =>
        countDistance (exactRankPortActualCount actual boundary p)
          (exactRankPortTargetCount boundary H p)) ≤ 448 := by
    exact_mod_cast hL1Cast
  have hleak := balanced_port_directional_leakage
    (exactRankPortActualCount actual boundary)
    (exactRankPortTargetCount boundary H) 448
    (by rw [hactualTotal, htargetTotal])
    hL1Nat
  rcases hleak with ⟨hforward, hbackward⟩
  have hforwardBound :
      (Finset.univ.sum fun p : Fin ports =>
        exactRankPortActualCount actual boundary p - exactRankPortTargetCount boundary H p) ≤ 224 := by
    omega
  have hbackwardBound :
      (Finset.univ.sum fun p : Fin ports =>
        exactRankPortTargetCount boundary H p - exactRankPortActualCount actual boundary p) ≤ 224 := by
    omega
  constructor
  · simpa [actual] using hforwardBound
  · simpa [actual] using hbackwardBound

/-- After the D2 scale factor 8192, the 224-wire directional mismatch fits
inside the existing `G <= capacity/512` sender-deficit allowance, provided a
sender is tiled by complete 4096-by-64 cores. -/
theorem scaled_directional_mismatch_fits_d2_deficit_cap
    (tiles leakage : Nat) (hleakage : leakage ≤ 224 * tiles) :
    512 * (8192 * leakage) ≤ 8192 * (262144 * tiles) := by
  omega

/-- The checked local core's two directed rank leaks, after multiplying by
the flow scale, both fit below the D2 `capacity/512` deficit cap for one
4096-by-64 tile. This is budget compatibility; the identification of this
leak with a reachable flow-tree deficit is still a separate bridge. -/
theorem fullHeightTwoShuffle_directional_leaks_fit_scaled_d2_cap
    (sourceHeight : Col → Nat) (boundary : Nat → Nat) (ports H : Nat)
    (hzero : boundary 0 = 0)
    (hend : boundary ports = 64 * 4096)
    (hmono : ∀ i, boundary i ≤ boundary (i + 1))
    (hH : H ≤ 64 * 4096)
    (hHsum : H = Finset.univ.sum fun c : Col => fullHeightTwoShuffle sourceHeight c)
    (hinput : ∀ c, sourceHeight c ≤ 4096) :
    512 * (8192 * (Finset.univ.sum fun p : Fin ports =>
      exactRankPortActualCount (fun c => fullHeightTwoShuffle sourceHeight c) boundary p -
        exactRankPortTargetCount boundary H p)) ≤ 8192 * 262144 ∧
    512 * (8192 * (Finset.univ.sum fun p : Fin ports =>
      exactRankPortTargetCount boundary H p -
        exactRankPortActualCount (fun c => fullHeightTwoShuffle sourceHeight c) boundary p)) ≤
      8192 * 262144 := by
  have hdir := fullHeightTwoShuffle_directional_leakage_le_224
    sourceHeight boundary ports H hzero hend hmono hH hHsum hinput
  constructor
  · exact scaled_directional_mismatch_fits_d2_deficit_cap 1 _ (by omega)
  · exact scaled_directional_mismatch_fits_d2_deficit_cap 1 _ (by omega)

end Chvatal.D2Slope25RowMajorBridge
