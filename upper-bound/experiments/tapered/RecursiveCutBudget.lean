import SignedReserve
import Mathlib.Algebra.Order.Field.GeomSum

namespace Tapered945

def radixCutRatio : Rat := 64 * delta

/-- Uniform normalized cost of the at-most 63 completed sibling blocks at
each level of a radix-64 partial-cut chain. The first sibling layer is at
stranger order one, hence the series starts at exponent one. -/
def radixSiblingFactor : Rat := 63 * radixCutRatio / (1 - radixCutRatio)

theorem radixCutRatio_bounds : 0 ≤ radixCutRatio ∧ radixCutRatio < 1 := by
  norm_num [radixCutRatio, delta]

/-- The sum of all sibling-register errors along any finite partial-child
chain is bounded by a single scale-independent geometric budget. This is the
analytic half of recursive cut cancellation; the schedule must still prove
the 63-sibling count and the stranger-order assignment at each level. -/
theorem radix_sibling_error_sum_le (depth : Nat) :
    (∑ r ∈ Finset.range depth,
      63 * mu * radixCutRatio ^ (r + 1)) ≤ mu * radixSiblingFactor := by
  have hx := radixCutRatio_bounds
  have hgeom :
      (∑ r ∈ Finset.range depth, radixCutRatio ^ (r + 1)) ≤
        radixCutRatio / (1 - radixCutRatio) := by
    have h := geom_sum_Ico_le_of_lt_one hx.1 hx.2
      (m := 1) (n := depth + 1)
    have h' :
        (∑ r ∈ Finset.range depth, radixCutRatio ^ (r + 1)) =
          ∑ r ∈ Finset.Ico 1 (depth + 1), radixCutRatio ^ r := by
      rw [Finset.sum_Ico_eq_sum_range]
      simp [Nat.add_comm]
    rw [h']
    simpa using h
  have hmu : 0 ≤ mu := by norm_num [mu]
  calc
    _ = (63 * mu) *
        (∑ r ∈ Finset.range depth, radixCutRatio ^ (r + 1)) := by
          rw [Finset.mul_sum]
    _ ≤ (63 * mu) * (radixCutRatio / (1 - radixCutRatio)) :=
      mul_le_mul_of_nonneg_left hgeom (by positivity)
    _ = mu * radixSiblingFactor := by
      simp [radixSiblingFactor]
      ring

/-- The finite-chain factor fits inside the candidate's conservative
sibling spill factor. -/
theorem radixSiblingFactor_le_candidate : radixSiblingFactor ≤ siblingFactor := by
  norm_num [radixSiblingFactor, radixCutRatio, siblingFactor, delta]

/-- The nominal share of one two-level descendant block in a one-level
ancestor register fits the reserve scale. This is only a numeric check; the
proof still needs a separator estimate to justify that localized share. -/
theorem ancestor_uniform_share_below_reserve :
    (1 / (4096 * 4096 : Rat)) < reserve := by
  norm_num [reserve, reserveEndpoint, cap, eAbs, ePos]

/-- The ancestor's total cardinality allowance alone is too large for the
reserve, so an actual rank-distribution estimate is necessary. -/
theorem ancestor_total_capacity_exceeds_reserve :
    reserve < (1 / 4096 : Rat) := by
  norm_num [reserve, reserveEndpoint, cap, eAbs, ePos]

/-- At the concrete `(d,t,l)=(14,10,2)` scale, an ideal one-step ancestor
localization plus the width-16 output-crossing allowance fits the reserve.
This is a numerical feasibility certificate only: the ideal `1/4096` rank
share is precisely the missing input-distribution theorem. -/
theorem one_ancestor_localization_screen :
    (1 / (4096 * 4096 : Rat)) + epsB / 4096 +
      (epsB * 16 + 32) / 2 ^ 48 < reserve := by
  norm_num [epsB, reserve, reserveEndpoint, cap, eAbs, ePos]

end Tapered945
