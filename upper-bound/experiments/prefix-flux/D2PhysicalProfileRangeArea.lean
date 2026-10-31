import D2BandRepair4096Network
import D2Range13Area

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace Chvatal.D2PhysicalProfileRangeArea

open Chvatal.D2BandRepair4096Network
open Chvatal.D2TwoGridPhysicalBand
open Chvatal.D2TwoGridBandInterface

abbrev Col := Fin 64
abbrev Row := Fin 4096

/-- The post-permutation, repaired physical profile inherits the same
range-13 area estimate as the semantic shuffle profile. -/
theorem physical_profile_area_le_169_over_eight
    (h : Col -> Nat) (perm : Row -> Equiv.Perm Col)
    (hbound : forall c, h c <= 4096) :
    (1 / 2 : Rat) *
      (Finset.univ.sum fun c : Col =>
        ((physicalTwoGridRepairHeight h perm c : Rat) -
          (Finset.univ.sum fun j : Col =>
            (physicalTwoGridRepairHeight h perm j : Rat)) / 64) ^ 2) / 64
        <= 169 / 8 := by
  let actual : Col -> Nat := physicalTwoGridRepairHeight h perm
  let lo : Nat := 4096 - highBoundary h
  let hi : Nat := 4096 - lowBoundary h
  have hhighBound : highBoundary h <= 4096 := highBoundary_le_4096 h
  have hlowBound : lowBoundary h <= 4096 :=
    (lowBoundary_le_highBoundary h).trans hhighBound
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
    change (Finset.univ.filter fun r : Row =>
        fullHeightAfterRowPermutation h perm (matrixWire 4096 64 r c) = true).card <=
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
  change (1 / 2 : Rat) *
      (Finset.univ.sum fun c : Col =>
        ((actual c : Rat) -
          (Finset.univ.sum fun j : Col => (actual j : Rat)) / 64) ^ 2) / 64
      <= 169 / 8
  exact Chvatal.D2Range13Area.area_le_169_over_eight actual lo hi hlo hhi hwidth

end Chvatal.D2PhysicalProfileRangeArea
