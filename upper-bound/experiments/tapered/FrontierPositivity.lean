import FrontierDebtFlow

namespace Tapered945

/-! Positivity of static-debt frontier flows. These are real-flow checks,
not an integer scheduler or a rank invariant. -/

theorem frontier_top_coeff_positive (e : Rat)
    (he : -eAbs ≤ e) : 0 < 1 + boundaryDebtCoeff * e := by
  unfold boundaryDebtCoeff eAbs at *
  linarith

theorem frontier_top_retreat_coeff_positive (e : Rat)
    (he : -eAbs ≤ e) : 0 < 1 / 65536 + e / 15 := by
  unfold eAbs at *
  linarith

theorem frontier_top_advance_coeff_positive (e : Rat) (j : Fin 64)
    (he : -eAbs ≤ e) :
    0 < 1 / 64 + boundaryDebtCoeff * (addressQ j.val + e / 64) := by
  have hq := (addressQ_bounds j.val).1
  unfold boundaryDebtCoeff qEnd eAbs at *
  linarith

theorem frontier_bottom_coeff_positive (e : Rat)
    (he : e ≤ ePos) : 0 < 1 - 1 / cap - boundaryDebtCoeff * e := by
  unfold cap boundaryDebtCoeff ePos at *
  norm_num at *
  linarith

theorem frontier_bottom_mass_positive (B C e : Rat)
    (hC : 0 < C) (hBC : C ≤ B) (he : e ≤ ePos) :
    0 < frontierBottomMass B C e := by
  have hp := frontier_bottom_coeff_positive e he
  have hm := mul_pos hp hC
  calc
    0 < (1 - 1 / cap - boundaryDebtCoeff * e) * C := hm
    _ = frontierBottomMass C C e := by unfold frontierBottomMass; ring
    _ ≤ frontierBottomMass B C e := by unfold frontierBottomMass; linarith

theorem frontier_meeting_mass (C e : Rat) :
    frontierTopMass C e + frontierBottomMass C C e =
      (2 - 1 / cap) * C := by
  unfold frontierTopMass frontierBottomMass
  ring

end Tapered945
