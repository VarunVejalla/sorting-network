import D2PhysicalProfileRangeArea
import D2Range13PortError

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace Chvatal.D2PhysicalProfilePortError

open Chvatal.D2BandRepair4096Network
open Chvatal.D2TwoGridPhysicalBand
open Chvatal.D2TwoGridBandInterface

abbrev Col := Fin 64
abbrev Row := Fin 4096

/-- The actual row-scrambled, two-grid-repaired 4096-row core obeys the
448 exact-rank port-error gate whenever its input profile is valid. -/
theorem physical_profile_exact_rank_port_error_le_448
    (h : Col -> Nat) (perm : Row -> Equiv.Perm Col)
    (hbound : forall c, h c <= 4096) (H ports : Nat)
    (hH : H = Finset.univ.sum fun c : Col => physicalTwoGridRepairHeight h perm c)
    (cuts : Col -> Nat -> Nat)
    (hzero : forall c, cuts c 0 = 0)
    (hend : forall c, cuts c ports = 4096)
    (hmono : forall c i, i < ports -> cuts c i <= cuts c (i + 1)) :
    (Finset.univ.sum fun cell : Prod Col (Fin ports) =>
      abs ((Chvatal.D2RankAlignment.prefixIntervalMass
          (physicalTwoGridRepairHeight h perm cell.1)
          (cuts cell.1 cell.2.val) (cuts cell.1 (cell.2.val + 1)) : Rat) -
        (Chvatal.D2RankAlignment.prefixIntervalMass
          (Chvatal.D2ColumnRebatchBridge.exactRankColumnHeight H cell.1)
          (cuts cell.1 cell.2.val) (cuts cell.1 (cell.2.val + 1)) : Rat))) <= 448 := by
  let actual : Col -> Nat := physicalTwoGridRepairHeight h perm
  let lo : Nat := 4096 - highBoundary h
  let hi : Nat := 4096 - lowBoundary h
  have hhighBound : highBoundary h <= 4096 := highBoundary_le_4096 h
  have hlowBound : lowBoundary h <= 4096 :=
    (lowBoundary_le_highBoundary h).trans hhighBound
  have hactual : forall c, actual c <= 4096 := by
    intro c
    dsimp [actual]
    rw [physical_twoGridRepairHeight_eq_scrambled_column_count]
    exact Chvatal.matrixColumnTrueCount_le c
      (twoGridRepair.exec (fullHeightAfterRowPermutation h perm))
  have hlo : forall c, lo <= actual c := by
    intro c
    change 4096 - highBoundary h <=
      (Finset.univ.filter fun r : Row =>
        fullHeightAfterRowPermutation h perm (matrixWire 4096 64 r c) = true).card
    have hsubset : Finset.univ.filter (fun r : Row => highBoundary h <= r.val) ⊆
        Finset.univ.filter (fun r : Row =>
          fullHeightAfterRowPermutation h perm (matrixWire 4096 64 r c) = true) := by
      intro r hr
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
      exact fullHeightAfterRowPermutation_true_above_band h perm r hr c
    have hcard := Finset.card_le_card hsubset
    rw [card_filter_val_ge 4096 (highBoundary h) hhighBound] at hcard
    exact hcard
  have hhi : forall c, actual c <= hi := by
    intro c
    change (Finset.univ.filter (fun r : Row =>
        fullHeightAfterRowPermutation h perm (matrixWire 4096 64 r c) = true)).card <=
      4096 - lowBoundary h
    have hsubset : (Finset.univ.filter (fun r : Row =>
        fullHeightAfterRowPermutation h perm (matrixWire 4096 64 r c) = true)) ⊆
        Finset.univ.filter (fun r : Row => lowBoundary h <= r.val) := by
      intro r hr
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
      by_contra hnot
      have hb := fullHeightAfterRowPermutation_false_below_band h perm r (by omega) c
      rw [hb] at hr
      cases hr
    have hcard := Finset.card_le_card hsubset
    rw [card_filter_val_ge 4096 (lowBoundary h) hlowBound] at hcard
    exact hcard
  have hwidth : hi - lo <= 13 := by
    have hb := band_width_le_thirteen h hbound
    dsimp [hi, lo]
    omega
  have hresult := Chvatal.D2Range13PortError.exact_rank_port_error_le_448
    actual cuts ports H hzero hend hmono hactual hH lo hi hlo hhi hwidth
  simpa [actual] using hresult

end Chvatal.D2PhysicalProfilePortError
