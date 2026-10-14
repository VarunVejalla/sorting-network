import TaperedSubtreeMass
import SignedReserve
import Mathlib.Tactic

namespace Tapered945

/-! Exact scale accounting for a two-level gap in the active bag tree.
Here one parent bag has reference size `C`, there are `64^2` grandchildren,
and each grandchild has reference size `4096*C`. -/

/-- The two active levels leave a nominal subtree deficit of `C/cap`, before
integer rounding. This isolates the mass term that must become the `D` input
to `ambient_register_native_bound_of_subtree_mass`. -/
theorem two_level_subtree_defect_bound (C : Rat) (a0 a2 : Nat)
    (h0 : |(a0 : Rat) - (1 - 1 / cap) * C| ≤ 69)
    (h2 : |(a2 : Rat) - (1 - 1 / cap) * (4096 * C)| ≤ 69) :
    |cap * C - (a0 + 4096 * a2 : Nat) - C / cap| ≤ 69 * 4097 := by
  have h0' := abs_le.mp h0
  have h2' := abs_le.mp h2
  have hbase :
      cap * C - ((1 - 1 / cap) * C +
        4096 * ((1 - 1 / cap) * (4096 * C))) - C / cap = 0 := by
    unfold cap
    norm_num
    ring
  have hcalc :
      cap * C - (a0 + 4096 * a2 : Nat) - C / cap =
        -((a0 : Rat) - (1 - 1 / cap) * C) -
          4096 * ((a2 : Rat) - (1 - 1 / cap) * (4096 * C)) := by
    push_cast
    nlinarith [hbase]
  rw [hcalc]
  have h0lo := h0'.1
  have h0hi := h0'.2
  have h2lo := h2'.1
  have h2hi := h2'.2
  rw [abs_le]
  constructor <;> nlinarith

/-- At the proposed starting scale, the ordinary order-one stranger allowance
is already larger than the signed reserve. Therefore the generic subtree-bad
sum cannot alone prove the needed localized mass bound; the current bag's
order-one error must be canceled/refined in the rank-cut recurrence. -/
theorem coarse_order_one_spill_exceeds_reserve : reserve < mu := by
  norm_num [reserve, reserveEndpoint, cap, eAbs, mu]

/-- The nominal defect `C/cap` plus 69-wire error from the parent and all 4096
grandchild registers fits the reserve at `C = 2^48`. This certifies the raw
subtree cardinality is viable; it is specifically the coarse order-one spill
above that prevents the current ambient estimate from closing. -/
theorem two_level_rounding_defect_fits_reserve :
    1 / cap + (69 * 4097 : Rat) / 2 ^ 48 < reserve := by
  norm_num [reserve, reserveEndpoint, cap, eAbs]

/-- Aggregate strict-descendant spill has a much smaller scale than the
order-one allowance. At distance `h`, there are `64^h` bags, each with
capacity `64^h * C`, and the taper contributes `delta^h`; hence the normalized
geometric ratio is `64^2 * delta`. This certifies the infinite tail budget,
provided the active schedule supplies those per-level capacity bounds. -/
theorem strict_descendant_spill_fits_reserve :
    mu * (4096 * delta) / (1 - 4096 * delta) < reserve := by
  norm_num [mu, delta, reserve, reserveEndpoint, cap, eAbs]

end Tapered945
