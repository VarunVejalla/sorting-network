import Mathlib.Tactic.Linarith

namespace Chvatal.D2Reserve

/-- Arithmetic interface for the difficult `(2,-1)` top-descending history.
`carried` is the sum of child deficits inherited from the preceding mid
update; `childQuota` is the total of the eight intervening mid quotas; the
current top-descending parent has nonnegative deficit. The D2 allocation
identity then gives the stated factor relative to the scheduled endpoint
allocation `c`. -/
theorem topDesc_two_minus_one_allocation_bound
    {c g carried childQuota parent allocation : Rat}
    (hg : g ≤ (23 : Rat) / 256 * c)
    (hcarry : carried ≤ g + (15 : Rat) / 256 * c)
    (hquota : childQuota ≤ (15 : Rat) / 16 * c)
    (hparent : 0 ≤ parent)
    (halloc : allocation = carried + childQuota - parent) :
    allocation ≤ (139 : Rat) / 128 * c := by
  rw [halloc]
  linarith

/-- The local factor above is below the proposed `35/32` envelope. -/
theorem topDesc_two_minus_one_factor_le_35_32
    {c : Rat} (hc : 0 ≤ c) :
    (139 : Rat) / 128 * c ≤ (35 : Rat) / 32 * c := by
  nlinarith

/-- The `(0,-1)` frontier history has a slightly larger but compatible
factor: a top-rise carry contributes `c/16`, the eight intermediate mid
quotas contribute `15c/16`, and the old deficit contributes at most
`23c/256`. -/
theorem topDesc_zero_minus_one_allocation_bound
    {c g carried childQuota parent allocation : Rat}
    (hg : g ≤ (23 : Rat) / 256 * c)
    (hcarry : carried ≤ g + (1 : Rat) / 16 * c)
    (hquota : childQuota ≤ (15 : Rat) / 16 * c)
    (hparent : 0 ≤ parent)
    (halloc : allocation = carried + childQuota - parent) :
    allocation ≤ (279 : Rat) / 256 * c := by
  rw [halloc]
  linarith

/-- The difficult `(2,-1)` case fits under the common factor required by
the other descending history. -/
theorem topDesc_two_minus_one_factor_le_279_256
    {c : Rat} (hc : 0 ≤ c) :
    (139 : Rat) / 128 * c ≤ (279 : Rat) / 256 * c := by
  nlinarith

end Chvatal.D2Reserve
