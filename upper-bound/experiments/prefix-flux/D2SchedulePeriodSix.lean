import D2ScheduleReserve

namespace Chvatal.D2Reserve

/-! Exact six-stage arithmetic for the tapered `(3,3,2)` schedule.

The lower frontier and capacities repeat under `(t,i) ↦ (t+6,i+4)`. The
upper frontier advances by only two tree levels, so this translation omits
one parity-compatible active sender at the upper edge. This is the schedule
symmetry needed for a bulk induction with a separately handled moving
boundary.
-/

private theorem ceilParity_add_four (m t : Nat) :
    ceilParity (m + 4) (t + 6) = ceilParity m t + 4 := by
  unfold ceilParity
  by_cases h : m % 2 = t % 2 <;>
    simp [h, Nat.add_mod]

private theorem ceilParity_add_two (m t : Nat) :
    ceilParity (m + 2) (t + 6) = ceilParity m t + 2 := by
  unfold ceilParity
  by_cases h : m % 2 = t % 2 <;>
    simp [h, Nat.add_mod]

theorem alphaStar_add_six {d t : Nat} (hpositive : 3 * d < 2 * t + 11) :
    alphaStar d (t + 6) = alphaStar d t + 4 := by
  unfold alphaStar
  have hpositive' : 3 * d < 2 * (t + 6) + 11 := by omega
  simp only [if_neg (by omega : ¬ 2 * t + 11 ≤ 3 * d),
    if_neg (by omega : ¬ 2 * (t + 6) + 11 ≤ 3 * d)]
  omega

theorem alpha_add_six {d t : Nat} (ht : 2 ≤ t)
    (hpositive : 3 * d < 2 * t + 11) :
    alpha d (t + 6) = alpha d t + 4 := by
  have hstar := alphaStar_add_six hpositive
  have ht0 : t ≠ 0 := by omega
  have ht1 : t ≠ 1 := by omega
  have ht60 : t + 6 ≠ 0 := by omega
  have ht61 : t + 6 ≠ 1 := by omega
  simp only [alpha, if_neg ht0, if_neg ht1, if_neg ht60, if_neg ht61,
    hstar]
  exact ceilParity_add_four (alphaStar d t) t

theorem omega_add_six {t : Nat} (ht : 2 ≤ t) :
    omega (t + 6) = omega t + 2 := by
  have ht0 : t ≠ 0 := by omega
  have ht1 : t ≠ 1 := by omega
  have ht60 : t + 6 ≠ 0 := by omega
  have ht61 : t + 6 ≠ 1 := by omega
  have hdiv : (t + 10) / 3 = (t + 4) / 3 + 2 := by omega
  simp only [omega, if_neg ht0, if_neg ht1, if_neg ht60, if_neg ht61, hdiv]
  exact ceilParity_add_two ((t + 4) / 3) t

theorem d2FlowCandidateCapacityExponent_add_six_four (d i t : Nat) :
    d2FlowCandidateCapacityExponent d (i + 4) (t + 6) =
      d2FlowCandidateCapacityExponent d i t := by
  simp [d2FlowCandidateCapacityExponent]
  omega

theorem d2FlowCandidateCapacity_add_six_four (d i t : Nat) :
    d2FlowCandidateCapacity d (i + 4) (t + 6) =
      d2FlowCandidateCapacity d i t := by
  simp [d2FlowCandidateCapacity,
    d2FlowCandidateCapacityExponent_add_six_four]

theorem active_add_six_four_iff {d tf i t : Nat}
    (ht : 2 ≤ t) (htf : t + 6 ≤ tf) :
    active d tf (i + 4) (t + 6) ↔
      active d tf i t ∧ 3 * i < t + 2 := by
  have ht1 : t ≠ 1 := by omega
  have ht61 : t + 6 ≠ 1 := by omega
  unfold active
  simp only [if_neg ht1, if_neg ht61]
  omega

theorem d2FlowCandidateQuota_add_six_four (d i t : Nat) (r : D2Role) :
    d2FlowCandidateQuota d (t + 6) (i + 4) r =
      d2FlowCandidateQuota d t i r := by
  simp [d2FlowCandidateQuota,
    d2FlowCandidateCapacityExponent_add_six_four]

/-- The six-stage coordinate shift preserves the role of a sender away from
the exceptional two-level strip at the lower (bottom) frontier. The strip is
exactly where a translated interior sender can land on the bottom boundary. -/
theorem d2ScheduleRole_add_six_four_of_away_from_bottom
    {d i t : Nat} (ht : 2 ≤ t)
    (hpositive : 3 * d < 2 * t + 11)
    (hi : i < omega t)
    (hnotEdge : i + 2 ≠ omega t) :
    d2ScheduleRole d (i + 4) (t + 6) = d2ScheduleRole d i t := by
  have hpositiveNext : 3 * d < 2 * (t + 1) + 11 := by omega
  have hα := alpha_add_six (d := d) (t := t) ht hpositive
  have hαnext := alpha_add_six (d := d) (t := t + 1) (by omega)
    hpositiveNext
  have hω := omega_add_six ht
  have hωnext := omega_add_six (t := t + 1) (by omega)
  unfold d2ScheduleRole
  rw [show alpha d (t + 6) = alpha d t + 4 by exact hα,
    show alpha d (t + 7) = alpha d (t + 1) + 4 by
      simpa [Nat.add_assoc] using hαnext,
    show omega (t + 6) = omega t + 2 by exact hω,
    show omega (t + 7) = omega (t + 1) + 2 by
      simpa [Nat.add_assoc] using hωnext]
  have hnotBottom : i ≠ omega t := by omega
  have hnotBottomNext : i + 4 ≠ omega t + 2 := by omega
  simp [hnotBottom, hnotBottomNext]

end Chvatal.D2Reserve
