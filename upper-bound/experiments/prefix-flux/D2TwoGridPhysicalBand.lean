import D2Slope35Physical4096
import D2TwoGridBandInterface

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

namespace Chvatal.D2TwoGridPhysicalBand

open Chvatal.D2Slope35Physical4096
open Chvatal.D2TwoGridBandInterface

abbrev Col := Fin 64
abbrev Row := Fin 4096

def fullHeightAfterRowPermutation (h : Col -> Nat)
    (perm : Row -> Equiv.Perm Col) : Fin (4096 * 64) -> Bool :=
  Function.comp (bottomUnaryProfile (fullHeightTwoShuffle h))
    (rowScrambleWirePerm 4096 64 (by omega) (fun r => (perm r).symm)).symm

theorem fullHeightAfterRowPermutation_matrixWire (h : Col -> Nat)
    (perm : Row -> Equiv.Perm Col) (r : Row) (c : Col) :
    fullHeightAfterRowPermutation h perm (matrixWire 4096 64 r c) =
      rowScrambledUnary h perm r c := by
  simp only [fullHeightAfterRowPermutation, Function.comp_apply]
  rw [rowScrambleWirePerm_symm_apply]
  simp [rowScrambledUnary, bottomUnaryProfile, bottomUnary, matrixWire_row_col,
    threshold, outputHeight]

theorem fullHeightAfterRowPermutation_false_below_band (h : Col -> Nat)
    (perm : Row -> Equiv.Perm Col)
    (r : Row) (hr : r.val < lowBoundary h) (c : Col) :
    fullHeightAfterRowPermutation h perm (matrixWire 4096 64 r c) = false := by
  rw [fullHeightAfterRowPermutation_matrixWire]
  exact rowScramble_false_below_band h perm r hr c

theorem fullHeightAfterRowPermutation_true_above_band (h : Col -> Nat)
    (perm : Row -> Equiv.Perm Col)
    (r : Row) (hr : highBoundary h <= r.val) (c : Col) :
    fullHeightAfterRowPermutation h perm (matrixWire 4096 64 r c) = true := by
  rw [fullHeightAfterRowPermutation_matrixWire]
  exact rowScramble_true_above_band h perm r hr c

theorem fullHeight_band_width_le_thirteen (h : Col -> Nat)
    (hbound : forall c, h c <= 4096) :
    highBoundary h - lowBoundary h <= 13 :=
  band_width_le_thirteen h hbound

end Chvatal.D2TwoGridPhysicalBand
