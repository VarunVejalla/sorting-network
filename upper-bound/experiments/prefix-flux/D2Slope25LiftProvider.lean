import D2Slope25Provider
import D2Slope25Lift
import D2Slope25LiftRange

open Chvatal.D2RankAlignment
open Chvatal.D2Slope25Physical
open Chvatal.D2Slope25Provider

set_option maxHeartbeats 1000000

namespace Chvatal.D2Slope25LiftProvider

abbrev Col := Fin 64
abbrev Height := Chvatal.D2Slope25Abstract.Height

def residualProfile (h : Col -> Nat) : Col -> Height :=
  fun c => Fin.mk (h c % 64) (Nat.lt_succ_of_lt (Nat.mod_lt (h c) (by decide)))

theorem residualTwoShuffle_eq_provider (h : Col -> Nat) (d : Col) :
    residualTwoShuffle h d =
      slope35Then25PhysicalOutputHeight (residualProfile h) d := by
  rfl

theorem fullHeightTwoShuffle_range_le_thirteen (h : Col -> Nat) :
    forall (origin target : Col),
      fullHeightTwoShuffle h origin <=
        fullHeightTwoShuffle h target + 13 := by
  apply Chvatal.D2Slope25LiftRange.fullHeightTwoShuffle_range_of_residual_range h
  intro origin target
  rw [residualTwoShuffle_eq_provider]
  exact slope35_then_slope25_output_range_le_thirteen
    (residualProfile h) origin target

end Chvatal.D2Slope25LiftProvider
