import WireRoundingBudget
import CandidateBulkExistence
import Mathlib.Tactic

namespace Tapered945

/-! A conservative alternative scalar screen. These results do not supply
the frontier invariant or a separator existence theorem. -/

def fallbackBulkError : Rat := 3 / 10000000
def fallbackFrontierCharge : Rat := (16 / 15) * eAbs
def fallbackMargin : Rat := screenedMargin + epsB + activeRounding -
  fallbackBulkError - 200 / 2 ^ 35 - fallbackFrontierCharge

theorem fallback_margin_positive : 0 < fallbackMargin := by
  norm_num [fallbackMargin, screenedMargin, activeRounding, siblingFactor,
    delta, mu, epsB, reserve, reserveEndpoint, cap, eAbs,
    fallbackBulkError, fallbackFrontierCharge]

theorem fallback_margin_lower : 7 / 100000000 < fallbackMargin := by
  norm_num [fallbackMargin, screenedMargin, activeRounding, siblingFactor,
    delta, mu, epsB, reserve, reserveEndpoint, cap, eAbs,
    fallbackBulkError, fallbackFrontierCharge]

theorem fallback_round_one_gap (m : Nat) (hm : 2 ^ 35 ≤ m) :
    Real.log (2 * ((m : Real) + 1)) + 1 / 2 ≤
      (m : Real) * (275 / 10 ^ 7 : Real) ^ 2 := by
  have hb := candidate_union_log_bound m (by omega)
  have hl := Real.log_two_lt_d9
  have hM : (2 : Real) ^ 35 ≤ m := by exact_mod_cast hm
  have hg := mul_le_mul_of_nonneg_right hM
    (show (0 : Real) ≤ (275 / 10 ^ 7 : Real) ^ 2 - 1 / 2 ^ 34 by norm_num)
  norm_num at hb hl hg ⊢
  nlinarith

theorem fallback_round_two_gap (m : Nat) (hm : 2 ^ 35 ≤ m) :
    Real.log (2 * ((m : Real) + 1)) + 1 / 2 ≤ (m : Real) *
      ((1 / 90 : Real) * (3 / 10 ^ 7) / 2 -
        (1 / 90 : Real) ^ 2 * (1 / 2 + 2 * (1 / 90 : Real) / 9) *
          (275 / 10 ^ 7) / 2) := by
  have hb := candidate_union_log_bound m (by omega)
  have hl := Real.log_two_lt_d9
  have hM : (2 : Real) ^ 35 ≤ m := by exact_mod_cast hm
  have hg := mul_le_mul_of_nonneg_right hM
    (show (0 : Real) ≤ ((1 / 90 : Real) * (3 / 10 ^ 7) / 2 -
      (1 / 90 : Real) ^ 2 * (1 / 2 + 2 * (1 / 90 : Real) / 9) *
        (275 / 10 ^ 7) / 2) - 1 / 2 ^ 34 by norm_num)
  norm_num at hb hl hg ⊢
  nlinarith

/-- Three 1998-layer stages per six input bits give coefficient 999.
The stage-count recurrence is still a global construction obligation. -/
theorem fallback_leading_price : (3 * (3 * (36 * 37 / 2 : Rat))) / 6 = 999 := by
  norm_num

end Tapered945
