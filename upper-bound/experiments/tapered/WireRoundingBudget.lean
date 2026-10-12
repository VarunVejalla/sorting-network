import SignedReserve
import AKS.Chvatal.RealInduction
import Mathlib.Tactic

namespace Tapered945

/-- Conservative revised ordinary-stage surcharge. This is a scalar screen;
the scheduler must still prove that its complete wire and padding charge
fits this allowance. -/
def wireAndPaddingAllowance : Rat := 200 / 2 ^ 34

def paddedScreenedMargin : Rat :=
  screenedMargin + activeRounding - wireAndPaddingAllowance

theorem padded_screened_margin_positive : 0 < paddedScreenedMargin := by
  norm_num [paddedScreenedMargin, screenedMargin, activeRounding,
    wireAndPaddingAllowance, siblingFactor, delta, mu, epsB, reserve,
    reserveEndpoint, cap, eAbs]

theorem padded_screened_margin_lower : 1 / 100000000 < paddedScreenedMargin := by
  norm_num [paddedScreenedMargin, screenedMargin, activeRounding,
    wireAndPaddingAllowance, siblingFactor, delta, mu, epsB, reserve,
    reserveEndpoint, cap, eAbs]

/-- A per-block error plus half an up-rounding wire, charged across all
63 non-current slots, still fits the conservative 200-wire screen. -/
theorem cumulative_wire_error_budget :
    63 * (1 + 70 / 64 + (1 / 2 : Rat)) + 2 + 1 ≤ 200 := by norm_num

/-- The two first-stage root-tail bounds are much smaller than the candidate
mu bound. Keeping this stronger root estimate leaves room for the candidate
bulk error at stage two. -/
theorem bootstrap_error_coeff_le :
    2 * Chvatal.paperRootEpsB * 64 + (reserve : Real) + (epsB : Real) ≤
      4 * (mu : Real) := by
  have hroot := Chvatal.paperRootEpsB_le_epsStar
  have hscalar : 2 * (Chvatal.invMu : Real) + (reserve : Real) + (epsB : Real) ≤
      4 * (mu : Real) := by
    norm_num [Chvatal.invMu, reserve, reserveEndpoint, cap, eAbs, epsB, mu]
  linarith

/-- Scale the first ragged separator's price to its next reference capacity.
This is the budget comparison, not a global outsider transition. -/
theorem bootstrap_output_budget_le (C : Real) (hC : 0 ≤ C) :
    (2 * Chvatal.paperRootEpsB * 64 + (reserve : Real) + (epsB : Real)) * C ≤
      (mu : Real) * (4 * C) := by
  have h := mul_le_mul_of_nonneg_right bootstrap_error_coeff_le hC
  nlinarith

end Tapered945
