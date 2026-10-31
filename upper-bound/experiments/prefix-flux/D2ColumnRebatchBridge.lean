import D2RankRebatch
import D2Slope25LiftArea
import D2RowMajorMismatch
import D2LiftedShuffleBridge

open scoped BigOperators

set_option maxRecDepth 4096
set_option maxHeartbeats 3000000

namespace Chvatal.D2ColumnRebatchBridge

open Chvatal.D2RankAlignment
open Chvatal.D2LiftedShuffleBridge
open Chvatal.D2Slope25LiftArea
open Chvatal.D2Slope25Physical
open Chvatal.D2RowMajorMismatch

abbrev Col := Fin 64

/-- A global row-major rank prefix of size `H` has this many keys in each
column: full rows, plus one key in the first `H % 64` columns. -/
def exactRankColumnHeight (H : Nat) (c : Col) : Nat :=
  H / 64 + if c.val < H % 64 then 1 else 0

/-- The exact rank column profile differs from its uniform rational profile by
at most32 in l1. This is the same triangular row-major discrepancy whose
variation is already bounded in `D2RowMajorMismatch`. -/
theorem exactRankColumnHeight_uniform_l1_le_32 (H : Nat) :
    (Finset.univ.sum fun c : Col =>
      abs ((exactRankColumnHeight H c : Rat) - (H : Rat) / 64)) <= 32 := by
  let r := H % 64
  have hr : r < 64 := by dsimp [r]; exact Nat.mod_lt H (by decide)
  have hnat : H = r + 64 * (H / 64) := by dsimp [r]; omega
  have hcast : (H : Rat) = (r : Rat) + 64 * ((H / 64 : Nat) : Rat) := by
    exact_mod_cast hnat
  have hdiv : (H : Rat) / 64 = ((H / 64 : Nat) : Rat) + (r : Rat) / 64 := by
    rw [hcast]
    field_simp
    ring
  have hstep (c : Col) :
      abs ((exactRankColumnHeight H c : Rat) - (H : Rat) / 64) =
        abs (rowMajorBump r (c.val + 1) - rowMajorBump r c.val) := by
    rw [rowMajorBump_abs_step r c.val (Nat.le_of_lt hr)]
    unfold exactRankColumnHeight
    by_cases hc : c.val < r
    case pos =>
      have hcH : c.val < H % 64 := by simpa [r] using hc
      simp only [if_pos hcH, if_pos hc]
      rw [hdiv]
      push_cast
      have harg :
          (((H / 64 : Nat) : Rat) + 1 - (((H / 64 : Nat) : Rat) + (r : Rat) / 64)) =
            1 - (r : Rat) / 64 := by ring
      have hnonneg : 0 <= 1 - (r : Rat) / 64 := by
        have hrRat : (r : Rat) < 64 := by exact_mod_cast hr
        nlinarith
      rw [harg, abs_of_nonneg hnonneg]
    case neg =>
      have hcH : Not (c.val < H % 64) := by simpa [r] using hc
      simp only [if_neg hcH, if_neg hc]
      rw [hdiv]
      push_cast
      have harg :
          (((H / 64 : Nat) : Rat) + 0 - (((H / 64 : Nat) : Rat) + (r : Rat) / 64)) =
            -(r : Rat) / 64 := by ring
      have hnonpos : -(r : Rat) / 64 <= 0 := by
        have hr0 : 0 <= (r : Rat) := Nat.cast_nonneg r
        nlinarith
      rw [harg, abs_of_nonpos hnonpos]
      ring
  calc
    _ = Finset.univ.sum fun c : Col =>
        abs (rowMajorBump r (c.val + 1) - rowMajorBump r c.val) := by
      apply Finset.sum_congr rfl
      intro c hc
      exact hstep c
    _ = Finset.sum (Finset.range 64) fun s =>
        abs (rowMajorBump r (s + 1) - rowMajorBump r s) := by
      rw [Fin.sum_univ_eq_sum_range
        (fun s : Nat => abs (rowMajorBump r (s + 1) - rowMajorBump r s))]
    _ <= 32 := rowMajorBump_total_variation_le_32 r hr

private def cellError (sourceHeight : Col -> Nat) (cuts : Col -> Nat -> Nat)
    (ports : Nat) (cell : Col × Fin ports) : Rat :=
  (prefixIntervalMass (fullHeightTwoShuffle sourceHeight cell.1)
      (cuts cell.1 cell.2.val) (cuts cell.1 (cell.2.val + 1)) : Rat) -
    ratPrefixIntervalMass
      (rectangularUniformDensity (fun c => fullHeightTwoShuffle sourceHeight c) * 4096)
      (cuts cell.1 cell.2.val) (cuts cell.1 (cell.2.val + 1))

/-- The fixed-core 416 deviation allowance survives splitting each D2 port
at every output-column boundary and then regrouping the resulting pieces by
an arbitrary next-stage cell map (for example, `(next tile, column)`). The
remaining schedule obligation is to exhibit the actual complete per-column
cuts and map from the D2 wire addresses. -/
theorem rebinned_column_profile_error_le_416
    {J : Type*} [Fintype J] [DecidableEq J]
    (sourceHeight : Col -> Nat) (cuts : Col -> Nat -> Nat) (ports : Nat)
    (group : Col × Fin ports -> J)
    (hzero : forall c, cuts c 0 = 0)
    (hend : forall c, cuts c ports = 4096)
    (hmono : forall c i, i < ports -> cuts c i <= cuts c (i + 1))
    (hinput : forall c, sourceHeight c <= 4096) :
    (Finset.univ.sum fun j : J =>
      abs ((Finset.univ.filter fun cell : Col × Fin ports => group cell = j).sum
        (cellError sourceHeight cuts ports))) <= 416 := by
  have hgroup := grouped_rational_abs_sum_le_refined_abs_sum
    (I := Col × Fin ports) group (cellError sourceHeight cuts ports)
  have hfine :
      (Finset.univ.sum fun cell : Col × Fin ports =>
        abs (cellError sourceHeight cuts ports cell)) <= 416 := by
    rw [Fintype.sum_prod_type'
      (fun c p => abs (cellError sourceHeight cuts ports (c, p)))]
    simpa [cellError] using
      fullHeightTwoShuffle_column_refined_port_l1_le_416
        sourceHeight cuts ports hzero hend hmono hinput
  exact le_trans hgroup (by simpa using hfine)

private def exactRankCellError (sourceHeight : Col -> Nat)
    (cuts : Col -> Nat -> Nat) (ports H : Nat)
    (cell : Col × Fin ports) : Rat :=
  (prefixIntervalMass (fullHeightTwoShuffle sourceHeight cell.1)
      (cuts cell.1 cell.2.val) (cuts cell.1 (cell.2.val + 1)) : Rat) -
    (prefixIntervalMass (exactRankColumnHeight H cell.1)
      (cuts cell.1 cell.2.val) (cuts cell.1 (cell.2.val + 1)) : Rat)

/-- Once the total marked count is `H`, the variance-controlled local core
error transfers to the exact row-major rank profile on refined
column-port cells with allowance416+32=448. The extra32 is the exact-rank
versus uniform-profile correction. -/
theorem fullHeightTwoShuffle_exact_rank_column_port_l1_le_448
    (sourceHeight : Col -> Nat) (cuts : Col -> Nat -> Nat) (ports H : Nat)
    (hzero : forall c, cuts c 0 = 0)
    (hend : forall c, cuts c ports = 4096)
    (hmono : forall c i, i < ports -> cuts c i <= cuts c (i + 1))
    (hinput : forall c, sourceHeight c <= 4096)
    (hHsum : H = Finset.univ.sum fun c : Col =>
      fullHeightTwoShuffle sourceHeight c) :
    (Finset.univ.sum fun cell : Prod Col (Fin ports) =>
      abs (exactRankCellError sourceHeight cuts ports H cell)) <= 448 := by
  let actual : Col -> Nat := fun c => fullHeightTwoShuffle sourceHeight c
  have hH : H <= 64 * 4096 := by
    rw [hHsum]
    calc
      (Finset.univ.sum fun c : Col => fullHeightTwoShuffle sourceHeight c) <=
          Finset.univ.sum fun _ : Col => 4096 := by
        apply Finset.sum_le_sum
        intro c hc
        exact fullHeightTwoShuffle_le_4096 sourceHeight hinput c
      _ = 64 * 4096 := by simp
  have hsumRat : (Finset.univ.sum fun c : Col => (actual c : Rat)) = (H : Rat) := by
    exact_mod_cast hHsum.symm
  have hmean : rectangularUniformDensity actual * 4096 = (H : Rat) / 64 := by
    dsimp [rectangularUniformDensity]
    rw [hsumRat]
    field_simp
  have hlocal := fullHeightTwoShuffle_column_refined_port_l1_le_416
    sourceHeight cuts ports hzero hend hmono hinput
  have hlocal' :
      (Finset.univ.sum fun c : Col =>
        Finset.univ.sum fun p : Fin ports =>
          abs ((prefixIntervalMass (actual c) (cuts c p.val)
              (cuts c (p.val + 1)) : Rat) -
            ratPrefixIntervalMass ((H : Rat) / 64)
              (cuts c p.val) (cuts c (p.val + 1)))) <= 416 := by
    simpa [actual, hmean] using hlocal
  have htargetColumn (c : Col) :
      (Finset.univ.sum fun p : Fin ports =>
        abs ((prefixIntervalMass (exactRankColumnHeight H c)
            (cuts c p.val) (cuts c (p.val + 1)) : Rat) -
          ratPrefixIntervalMass ((H : Rat) / 64)
            (cuts c p.val) (cuts c (p.val + 1)))) =
        abs ((exactRankColumnHeight H c : Rat) - (H : Rat) / 64) := by
    rw [Fin.sum_univ_eq_sum_range (fun i : Nat =>
      abs ((prefixIntervalMass (exactRankColumnHeight H c)
          (cuts c i) (cuts c (i + 1)) : Rat) -
        ratPrefixIntervalMass ((H : Rat) / 64) (cuts c i) (cuts c (i + 1))))]
    have hmod : H % 64 < 64 := Nat.mod_lt H (by decide)
    have hdecomp : H = 64 * (H / 64) + H % 64 := by omega
    have hq : H / 64 <= 4096 := by omega
    have hcol : exactRankColumnHeight H c <= 4096 := by
      unfold exactRankColumnHeight
      by_cases hc : c.val < H % 64
      case pos =>
        simp [hc]
        by_cases hqfull : H / 64 = 4096 <;> omega
      case neg =>
        simp [hc]
        exact hq
    have hrefNonneg : 0 <= (H : Rat) / 64 :=
      div_nonneg (Nat.cast_nonneg H) (by norm_num)
    have hHrat : (H : Rat) <= (64 : Rat) * 4096 := by exact_mod_cast hH
    have hrefLe : (H : Rat) / 64 <= 4096 := by
      calc
        (H : Rat) / 64 <= ((64 : Rat) * 4096) / 64 :=
          div_le_div_of_nonneg_right hHrat (by norm_num)
        _ = 4096 := by norm_num
    exact nat_actual_rational_reference_port_partition
      (exactRankColumnHeight H c) ((H : Rat) / 64) (cuts c) ports
      (hzero c) 4096 (hend c) (by intro i hi; exact hmono c i hi)
      hcol hrefLe hrefNonneg
  have htarget :
      (Finset.univ.sum fun c : Col =>
        Finset.univ.sum fun p : Fin ports =>
          abs ((prefixIntervalMass (exactRankColumnHeight H c)
              (cuts c p.val) (cuts c (p.val + 1)) : Rat) -
            ratPrefixIntervalMass ((H : Rat) / 64)
              (cuts c p.val) (cuts c (p.val + 1)))) <= 32 := by
    calc
      _ = Finset.univ.sum fun c : Col =>
          abs ((exactRankColumnHeight H c : Rat) - (H : Rat) / 64) := by
        apply Finset.sum_congr rfl
        intro c hc
        exact htargetColumn c
      _ <= 32 := exactRankColumnHeight_uniform_l1_le_32 H
  let actualCell : Prod Col (Fin ports) -> Rat := fun cell =>
    (prefixIntervalMass (actual cell.1)
      (cuts cell.1 cell.2.val) (cuts cell.1 (cell.2.val + 1)) : Rat)
  let uniformCell : Prod Col (Fin ports) -> Rat := fun cell =>
    ratPrefixIntervalMass ((H : Rat) / 64)
      (cuts cell.1 cell.2.val) (cuts cell.1 (cell.2.val + 1))
  let idealCell : Prod Col (Fin ports) -> Rat := fun cell =>
    (prefixIntervalMass (exactRankColumnHeight H cell.1)
      (cuts cell.1 cell.2.val) (cuts cell.1 (cell.2.val + 1)) : Rat)
  have htriangle :
      (Finset.univ.sum fun cell : Prod Col (Fin ports) =>
        abs (actualCell cell - idealCell cell)) <=
      (Finset.univ.sum fun cell : Prod Col (Fin ports) =>
        abs (actualCell cell - uniformCell cell)) +
      (Finset.univ.sum fun cell : Prod Col (Fin ports) =>
        abs (uniformCell cell - idealCell cell)) := by
    calc
      _ <= Finset.univ.sum fun cell : Prod Col (Fin ports) =>
          abs (actualCell cell - uniformCell cell) +
            abs (uniformCell cell - idealCell cell) := by
        apply Finset.sum_le_sum
        intro cell hc
        exact abs_sub_le (actualCell cell) (uniformCell cell) (idealCell cell)
      _ = _ := by rw [Finset.sum_add_distrib]
  have hlocalProd :
      (Finset.univ.sum fun cell : Prod Col (Fin ports) =>
        abs (actualCell cell - uniformCell cell)) <= 416 := by
    rw [Fintype.sum_prod_type'
      (fun c p => abs (actualCell (c, p) - uniformCell (c, p)))]
    simpa [actualCell, uniformCell] using hlocal'
  have htargetProd :
      (Finset.univ.sum fun cell : Prod Col (Fin ports) =>
        abs (uniformCell cell - idealCell cell)) <= 32 := by
    rw [Fintype.sum_prod_type'
      (fun c p => abs (uniformCell (c, p) - idealCell (c, p)))]
    simpa [uniformCell, idealCell, abs_sub_comm] using htarget
  have hsum := le_trans htriangle (add_le_add hlocalProd htargetProd)
  calc
    _ <= (416 : Rat) + 32 := by
      simpa [actualCell, idealCell, exactRankCellError, actual] using hsum
    _ = 448 := by norm_num

private def extendLastPortToFullRows (cuts : Col -> Nat -> Nat)
    (ports : Nat) (c : Col) (i : Nat) : Nat :=
  if i = ports then 4096 else cuts c i

private theorem exactRankColumnHeight_le_of_total_le
    (H m : Nat) (hH : H <= 64 * m) (c : Col) :
    exactRankColumnHeight H c <= m := by
  have hdecomp : H = 64 * (H / 64) + H % 64 := by omega
  have hqle : H / 64 <= m := by omega
  by_cases hq : H / 64 = m
  · have hr : H % 64 = 0 := by omega
    simp [exactRankColumnHeight, hq, hr]
  · have hq' : H / 64 + 1 <= m := by omega
    unfold exactRankColumnHeight
    split_ifs <;> omega

/-- The exact-rank 448 bound also holds when the local fixed-core tile has
only `m` complete live rows: extending the last live port through the
all-one padding rows changes neither its actual nor ideal false count. -/
theorem fullHeightTwoShuffle_partial_rows_rebinned_l1_le_448
    {J : Type*} [Fintype J] [DecidableEq J]
    (sourceHeight : Col -> Nat) (cuts : Col -> Nat -> Nat) (ports m H : Nat)
    (group : Prod Col (Fin ports) -> J)
    (hports : 0 < ports) (hm : m <= 4096)
    (hzero : forall c, cuts c 0 = 0)
    (hend : forall c, cuts c ports = m)
    (hmono : forall c i, i < ports -> cuts c i <= cuts c (i + 1))
    (hinput : forall c, sourceHeight c <= m)
    (hHsum : H = Finset.univ.sum fun c : Col =>
      fullHeightTwoShuffle sourceHeight c) :
    (Finset.univ.sum fun j : J =>
      abs ((Finset.univ.filter fun cell : Prod Col (Fin ports) =>
        group cell = j).sum
          (exactRankCellError sourceHeight cuts ports H))) <= 448 := by
  have hH : H <= 64 * m := by
    rw [hHsum]
    calc
      (Finset.univ.sum fun c : Col => fullHeightTwoShuffle sourceHeight c) <=
          Finset.univ.sum fun _ : Col => m := by
        apply Finset.sum_le_sum
        intro c hc
        exact fullHeightTwoShuffle_le_of_height_le sourceHeight m hm hinput c
      _ = 64 * m := by simp
  let paddedCuts : Col -> Nat -> Nat := extendLastPortToFullRows cuts ports
  have hpzero (c : Col) : paddedCuts c 0 = 0 := by
    have hne : 0 ≠ ports := by omega
    simp [paddedCuts, extendLastPortToFullRows, hne, hzero c]
  have hpend (c : Col) : paddedCuts c ports = 4096 := by
    simp [paddedCuts, extendLastPortToFullRows]
  have hmono' (c : Col) (i : Nat) (hi : i < ports) :
      paddedCuts c i <= paddedCuts c (i + 1) := by
    by_cases hlast : i + 1 = ports
    · have hbefore := hmono c i hi
      rw [hlast, hend c] at hbefore
      have hne : i ≠ ports := by omega
      simp [paddedCuts, extendLastPortToFullRows, hlast, hne]
      exact hbefore.trans (by omega : m <= 4096)
    · have hnext : i + 1 < ports := by omega
      have hne : i ≠ ports := by omega
      have hneNext : i + 1 ≠ ports := by omega
      simp [paddedCuts, extendLastPortToFullRows, hne, hneNext]
      exact hmono c i hi
  have hactual (c : Col) : fullHeightTwoShuffle sourceHeight c <= m :=
    fullHeightTwoShuffle_le_of_height_le sourceHeight m hm hinput c
  have hideal (c : Col) : exactRankColumnHeight H c <= m :=
    exactRankColumnHeight_le_of_total_le H m hH c
  have herror (cell : Prod Col (Fin ports)) :
      exactRankCellError sourceHeight cuts ports H cell =
        exactRankCellError sourceHeight paddedCuts ports H cell := by
    rcases cell with ⟨c, p⟩
    by_cases hlast : p.val + 1 = ports
    · have hlo : cuts c p.val <= m := by
        calc
          cuts c p.val <= cuts c (p.val + 1) := hmono c p.val p.isLt
          _ = m := by rw [hlast, hend c]
      have hmass (x : Nat) (hx : x <= m) :
          prefixIntervalMass x (cuts c p.val) m =
            prefixIntervalMass x (cuts c p.val) 4096 := by
        unfold prefixIntervalMass
        have hsub : x - cuts c p.val <= m - cuts c p.val := Nat.sub_le_sub_right hx _
        have hsub' : m - cuts c p.val <= 4096 - cuts c p.val := Nat.sub_le_sub_right hm _
        simp [Nat.min_eq_left (le_trans hsub hsub'), Nat.min_eq_left hsub]
      unfold exactRankCellError
      rw [hlast, hend c]
      have hne : p.val ≠ ports := by omega
      simp only [paddedCuts, extendLastPortToFullRows, hne, if_false]
      rw [hmass _ (hactual c), hmass _ (hideal c)]
      simp
    · have hnext : p.val + 1 < ports := by omega
      have hne : p.val ≠ ports := by omega
      have hneNext : p.val + 1 ≠ ports := by omega
      simp [exactRankCellError, paddedCuts, extendLastPortToFullRows,
        hne, hneNext]
  have hfull := fullHeightTwoShuffle_exact_rank_column_port_l1_le_448
    sourceHeight paddedCuts ports H hpzero hpend hmono'
    (fun c => (hinput c).trans hm) hHsum
  have hsame :
      (Finset.univ.sum fun cell : Prod Col (Fin ports) =>
        abs (exactRankCellError sourceHeight cuts ports H cell)) =
      (Finset.univ.sum fun cell : Prod Col (Fin ports) =>
        abs (exactRankCellError sourceHeight paddedCuts ports H cell)) := by
    apply Finset.sum_congr rfl
    intro cell hc
    rw [herror cell]
  have hgrouped := grouped_rational_abs_sum_le_refined_abs_sum group
    (exactRankCellError sourceHeight cuts ports H)
  exact (le_trans hgrouped (by rw [hsame]; exact hfull))

/-- The fixed tile's exact-rank error bound remains 448 after its refined
column-port cells are assigned to arbitrary next-stage receiver groups. This
is the local composition needed before identifying those groups with the
actual ragged D2 addresses. -/
theorem fullHeightTwoShuffle_exact_rank_rebinned_l1_le_448
    {J : Type*} [Fintype J] [DecidableEq J]
    (sourceHeight : Col -> Nat) (cuts : Col -> Nat -> Nat) (ports H : Nat)
    (group : Prod Col (Fin ports) -> J)
    (hzero : forall c, cuts c 0 = 0)
    (hend : forall c, cuts c ports = 4096)
    (hmono : forall c i, i < ports -> cuts c i <= cuts c (i + 1))
    (hinput : forall c, sourceHeight c <= 4096)
    (hHsum : H = Finset.univ.sum fun c : Col =>
      fullHeightTwoShuffle sourceHeight c) :
    (Finset.univ.sum fun j : J =>
      abs ((Finset.univ.filter fun cell : Prod Col (Fin ports) =>
        group cell = j).sum
          (exactRankCellError sourceHeight cuts ports H))) <= 448 := by
  calc
    _ <= Finset.univ.sum fun cell : Prod Col (Fin ports) =>
        abs (exactRankCellError sourceHeight cuts ports H cell) :=
      grouped_rational_abs_sum_le_refined_abs_sum group
        (exactRankCellError sourceHeight cuts ports H)
    _ <= 448 := fullHeightTwoShuffle_exact_rank_column_port_l1_le_448
      sourceHeight cuts ports H hzero hend hmono hinput hHsum

/-- Numerically, the complete tile's 448-key allowance still fits the
candidate D2 `1/512` normalized transfer budget after the worst scheduled
allocation factor `279/256`. -/
theorem d2_full_tile_448_transfer_budget :
    ((448 : Rat) / (4096 * 64)) * ((279 : Rat) / 256) < 1 / 512 := by
  norm_num

end Chvatal.D2ColumnRebatchBridge
