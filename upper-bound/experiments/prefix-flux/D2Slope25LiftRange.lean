import D2Slope25Lift

set_option maxHeartbeats 2000000

open Chvatal.D2Slope25Physical

namespace Chvatal.D2Slope25LiftRange

theorem fullHeightTwoShuffle_range_of_residual_range
    (h : Fin 64 -> Nat)
    (hrange : forall origin target : Fin 64,
      residualTwoShuffle h origin <= residualTwoShuffle h target + 13) :
    forall origin target : Fin 64,
      fullHeightTwoShuffle h origin <= fullHeightTwoShuffle h target + 13 := by
  intro origin target
  let q := Finset.univ.sum fun c : Fin 64 => h c / 64
  rw [fullHeightTwoShuffle_eq_quotient_residual,
    fullHeightTwoShuffle_eq_quotient_residual]
  change q + residualTwoShuffle h (shiftedDest q origin) <=
    q + residualTwoShuffle h (shiftedDest q target) + 13
  calc
    q + residualTwoShuffle h (shiftedDest q origin) <=
        q + (residualTwoShuffle h (shiftedDest q target) + 13) :=
      Nat.add_le_add_left
        (hrange (shiftedDest q origin) (shiftedDest q target)) q
    _ = q + residualTwoShuffle h (shiftedDest q target) + 13 := by omega

end Chvatal.D2Slope25LiftRange
