import D2CandidateQuotaLower
import D2PhysicalBagState

namespace Chvatal.D2Reserve

open Chvatal.D2PhysicalBagState

/-! The cut front of an ordinary sender is much smaller than the quota at an
active ordinary grandchild. This is the arithmetic core of nested endpoint
containment: the ancestor's cut cannot pass the descendant's updated front. -/

theorem d2FlowCandidate_front_le_grandchild_half_quota
    {d i t G front : Nat}
    (hd : 7 <= d) (ht : 2 <= t)
    (hparentActive : d2FlowCandidateActive d t i = true)
    (hgrandchildActive : d2FlowCandidateActive d t (i + 2) = true)
    (hgrandchildRole : d2FlowCandidateRole d t (i + 2) = .topRise ∨
      d2FlowCandidateRole d t (i + 2) = .mid ∨
      d2FlowCandidateRole d t (i + 2) = .botDesc)
    (hfrontBound : front <= G)
    (hG : 512 * G <= d2FlowCandidateCapacity d i t)
    (hquota : 256 * d2FlowCandidateQuota d t i
      (d2FlowCandidateRole d t i) <= d2FlowCandidateCapacity d i t) :
    front + d2FlowCandidateQuota d t i (d2FlowCandidateRole d t i) / 2 <=
      d2FlowCandidateQuota d t (i + 2)
        (d2FlowCandidateRole d t (i + 2)) / 2 := by
  classical
  have hparentSchedule : active d (tfD2 d) i t := by
    rw [d2FlowCandidateActive_matches_schedule (by omega)] at hparentActive
    exact of_decide_eq_true hparentActive
  have hgrandchildSchedule : active d (tfD2 d) (i + 2) t := by
    rw [d2FlowCandidateActive_matches_schedule (by omega)] at hgrandchildActive
    exact of_decide_eq_true hgrandchildActive
  have hexpParent : 20 <= d2FlowCandidateCapacityExponent d i t :=
    d2FlowCandidateCapacityExponent_ge_twenty hd hparentSchedule
  have hexpShift : d2FlowCandidateCapacityExponent d (i + 2) t =
      d2FlowCandidateCapacityExponent d i t + 6 := by
    unfold d2FlowCandidateCapacityExponent
    unfold d2FlowCandidateCapacityExponent at hexpParent
    omega
  have hcapacityShift : d2FlowCandidateCapacity d (i + 2) t =
      64 * d2FlowCandidateCapacity d i t := by
    simp only [d2FlowCandidateCapacity, hexpShift, pow_add]
    norm_num
    ring
  have hgrandchildRoleSchedule : d2ScheduleRole d (i + 2) t = .topRise ∨
      d2ScheduleRole d (i + 2) t = .mid ∨
      d2ScheduleRole d (i + 2) t = .botDesc := by
    simpa [d2FlowCandidateRole_matches_schedule (t := t) (i := i + 2)
      (by omega)] using hgrandchildRole
  have hquotaLower := d2FlowCandidateQuota_lower_ordinary
    hd hgrandchildSchedule hgrandchildRoleSchedule
  have hroleMatch := d2FlowCandidateRole_matches_schedule
    (d := d) (t := t) (i := i + 2) (by omega)
  rw [← hroleMatch] at hquotaLower
  have hquotaLower' : 960 * d2FlowCandidateCapacity d i t <=
      4096 * d2FlowCandidateQuota d t (i + 2)
        (d2FlowCandidateRole d t (i + 2)) := by
    rw [hcapacityShift] at hquotaLower
    nlinarith [hquotaLower]
  have hfront : 256 * (front +
      d2FlowCandidateQuota d t i (d2FlowCandidateRole d t i) / 2) <=
        d2FlowCandidateCapacity d i t := by
    have hlow : 512 * front <= d2FlowCandidateCapacity d i t := by
      nlinarith
    have hhalf : 512 *
        (d2FlowCandidateQuota d t i (d2FlowCandidateRole d t i) / 2) <=
          d2FlowCandidateCapacity d i t := by
      omega
    omega
  have htwice : 2 * (front +
      d2FlowCandidateQuota d t i (d2FlowCandidateRole d t i) / 2) <=
        d2FlowCandidateQuota d t (i + 2)
          (d2FlowCandidateRole d t (i + 2)) := by
    nlinarith [hfront, hquotaLower']
  omega

theorem d2FlowCandidate_parent_left_front_le_grandchild_half_quota
    {d i t G low high : Nat}
    (hd : 7 <= d) (ht : 2 <= t)
    (hparentActive : d2FlowCandidateActive d t i = true)
    (hgrandchildActive : d2FlowCandidateActive d t (i + 2) = true)
    (hgrandchildRole : d2FlowCandidateRole d t (i + 2) = .topRise ∨
      d2FlowCandidateRole d t (i + 2) = .mid ∨
      d2FlowCandidateRole d t (i + 2) = .botDesc)
    (hbalance : low + high = G)
    (hG : 512 * G <= d2FlowCandidateCapacity d i t)
    (hquota : 256 * d2FlowCandidateQuota d t i
      (d2FlowCandidateRole d t i) <= d2FlowCandidateCapacity d i t) :
    low + d2FlowCandidateQuota d t i (d2FlowCandidateRole d t i) / 2 <=
      d2FlowCandidateQuota d t (i + 2)
        (d2FlowCandidateRole d t (i + 2)) / 2 := by
  exact d2FlowCandidate_front_le_grandchild_half_quota
    hd ht hparentActive hgrandchildActive hgrandchildRole
    (by omega) hG hquota

theorem d2FlowCandidate_parent_right_front_le_grandchild_half_quota
    {d i t G low high : Nat}
    (hd : 7 <= d) (ht : 2 <= t)
    (hparentActive : d2FlowCandidateActive d t i = true)
    (hgrandchildActive : d2FlowCandidateActive d t (i + 2) = true)
    (hgrandchildRole : d2FlowCandidateRole d t (i + 2) = .topRise ∨
      d2FlowCandidateRole d t (i + 2) = .mid ∨
      d2FlowCandidateRole d t (i + 2) = .botDesc)
    (hbalance : low + high = G)
    (hG : 512 * G <= d2FlowCandidateCapacity d i t)
    (hquota : 256 * d2FlowCandidateQuota d t i
      (d2FlowCandidateRole d t i) <= d2FlowCandidateCapacity d i t) :
    high + d2FlowCandidateQuota d t i (d2FlowCandidateRole d t i) / 2 <=
      d2FlowCandidateQuota d t (i + 2)
        (d2FlowCandidateRole d t (i + 2)) / 2 := by
  exact d2FlowCandidate_front_le_grandchild_half_quota
    hd ht hparentActive hgrandchildActive hgrandchildRole
    (by omega) hG hquota

theorem d2FlowCandidateActive_adjacent_false_of_active
    {d i t : Nat} (hactive : d2FlowCandidateActive d t i = true) :
    d2FlowCandidateActive d t (i + 1) = false := by
  classical
  by_cases ht0 : t = 0
  · subst t
    simp [d2FlowCandidateActive] at hactive ⊢
  · by_cases ht1 : t = 1
    · subst t
      simp [d2FlowCandidateActive] at hactive ⊢
      omega
    · have ht : 0 < t := by omega
      have hparentSchedule : active d (tfD2 d) i t := by
        rw [d2FlowCandidateActive_matches_schedule ht] at hactive
        exact of_decide_eq_true hactive
      cases hnextBool : d2FlowCandidateActive d t (i + 1) with
      | false => rfl
      | true =>
          have hnextSchedule : active d (tfD2 d) (i + 1) t := by
            rw [d2FlowCandidateActive_matches_schedule ht] at hnextBool
            exact of_decide_eq_true hnextBool
          have hp :=
            (active_iff_frontiers (tf := tfD2 d) (by omega)).1 hparentSchedule
          have hn :=
            (active_iff_frontiers (tf := tfD2 d) (by omega)).1 hnextSchedule
          omega

theorem d2FlowCutChild_first_left_le_parent_front
    {size left right : Nat} :
    (d2FlowCutChild 0 size left right).2.1 <= left := by
  simp [d2FlowCutChild, d2LeftCut]

theorem d2FlowCutChild_last_right_le_parent_front
    {sizes : Fin 8 -> Nat} {right front : Nat}
    (hfront : front <= d2FlowTotal sizes)
    (hright : right = d2FlowTotal sizes - front) :
    (d2FlowCutChild (d2FlowPosition sizes 7) (sizes 7) 0 right).2.2 <=
      front := by
  have hlast := d2FlowPosition_last_end sizes
  have hlast' : d2FlowPosition sizes 7 + sizes 7 = d2FlowTotal sizes := by
    simpa using hlast
  change d2RightCut (d2FlowPosition sizes 7) (sizes 7) right <= front
  unfold d2RightCut
  rw [hlast', hright]
  omega

theorem d2FlowStage_active_ordinary_root_left_front
    {active : Nat -> Bool} {role : Nat -> D2Role}
    {quota : Nat -> D2Role -> Nat}
    {h i G low high : Nat} (children : Fin 8 -> D2FlowTree h)
    (ha : active i = true)
    (hr : role i = .topRise ∨ role i = .mid ∨ role i = .botDesc) :
    (d2FlowTreeRootData (d2FlowStage active role quota (h + 1) i
      (.node G low high children))).2.1 = low + quota i (role i) / 2 := by
  rcases hr with htop | hmid | hbot
  · simp [d2FlowStage, ha, htop, d2FlowTreeRootData]
  · simp [d2FlowStage, ha, hmid, d2FlowTreeRootData]
  · simp [d2FlowStage, ha, hbot, d2FlowTreeRootData]

theorem d2FlowStage_active_ordinary_root_right_front
    {active : Nat -> Bool} {role : Nat -> D2Role}
    {quota : Nat -> D2Role -> Nat}
    {h i G low high : Nat} (children : Fin 8 -> D2FlowTree h)
    (ha : active i = true)
    (heven : quota i (role i) % 2 = 0)
    (hr : role i = .topRise ∨ role i = .mid ∨ role i = .botDesc) :
    (d2FlowTreeRootData (d2FlowStage active role quota (h + 1) i
      (.node G low high children))).2.2 = high + quota i (role i) / 2 := by
  rcases hr with htop | hmid | hbot
  · have heven' : quota i .topRise % 2 = 0 := by simpa [htop] using heven
    simp [d2FlowStage, ha, htop, d2FlowTreeRootData]
    omega
  · have heven' : quota i .mid % 2 = 0 := by simpa [hmid] using heven
    simp [d2FlowStage, ha, hmid, d2FlowTreeRootData]
    omega
  · have heven' : quota i .botDesc % 2 = 0 := by simpa [hbot] using heven
    simp [d2FlowStage, ha, hbot, d2FlowTreeRootData]
    omega

theorem d2FlowStage_active_ordinary_tree_root_left_front
    {active : Nat -> Bool} {role : Nat -> D2Role}
    {quota : Nat -> D2Role -> Nat} {h i : Nat}
    (tree : D2FlowTree (h + 1))
    (ha : active i = true)
    (hr : role i = .topRise ∨ role i = .mid ∨ role i = .botDesc) :
    (d2FlowTreeRootData (d2FlowStage active role quota (h + 1) i tree)).2.1 =
      (d2FlowTreeRootData tree).2.1 + quota i (role i) / 2 := by
  cases tree with
  | node G low high children =>
      simpa [d2FlowTreeRootData] using
        d2FlowStage_active_ordinary_root_left_front children ha hr

theorem d2FlowStage_active_ordinary_tree_root_right_front
    {active : Nat -> Bool} {role : Nat -> D2Role}
    {quota : Nat -> D2Role -> Nat} {h i : Nat}
    (tree : D2FlowTree (h + 1))
    (ha : active i = true)
    (heven : quota i (role i) % 2 = 0)
    (hr : role i = .topRise ∨ role i = .mid ∨ role i = .botDesc) :
    (d2FlowTreeRootData (d2FlowStage active role quota (h + 1) i tree)).2.2 =
      (d2FlowTreeRootData tree).2.2 + quota i (role i) / 2 := by
  cases tree with
  | node G low high children =>
      simpa [d2FlowTreeRootData] using
        d2FlowStage_active_ordinary_root_right_front children ha heven hr

/-! If an intermediate child is inactive, the grandchild runs at its own
schedule level before the parent overwrites the intermediate root. Combining
the cut arithmetic above with its updated root front gives the exact endpoint
containment needed by the recursive static-fit proof. -/

theorem d2FlowStage_regular_first_cut_le_grandchild_left_front
    {active : Nat -> Bool} {role : Nat -> D2Role}
    {quota : Nat -> D2Role -> Nat}
    {h i G low high : Nat} (children : Fin 8 -> D2FlowTree (h + 2))
    (ha : active i = true)
    (hr : role i = .topRise ∨ role i = .mid ∨ role i = .botDesc)
    (hnext : active (i + 1) = false)
    (hgrandchild : active (i + 2) = true)
    (hgrandchildRole : role (i + 2) = .topRise ∨
      role (i + 2) = .mid ∨ role (i + 2) = .botDesc)
    (hfront : low + quota i (role i) / 2 <= quota (i + 2)
      (role (i + 2)) / 2) :
    (d2FlowCutChild (d2FlowPosition
      (fun j => d2FlowTreeRootDeficit (children j)) 0)
      (d2FlowTreeRootDeficit (children 0))
      (low + quota i (role i) / 2)
      (d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) -
        high - quota i (role i) / 2)).2.1 <=
    (d2FlowTreeRootData
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowStage active role quota (h + 3) i
            (.node G low high children)) 0) 0)).2.1 := by
  have hgrandchildStage := d2FlowStage_regular_child_grandchild_stage
    (active := active) (role := role) (quota := quota)
    (h := h + 1) (i := i) (G := G) (low := low) (high := high)
    children ha hr hnext (0 : Fin 8) (0 : Fin 8)
  have hupdated : (d2FlowTreeRootData
      (d2FlowStage active role quota (h + 1) (i + 2)
        (d2FlowTreeChild (children 0) 0))).2.1 =
      (d2FlowTreeRootData (d2FlowTreeChild (children 0) 0)).2.1 +
        quota (i + 2) (role (i + 2)) / 2 :=
    d2FlowStage_active_ordinary_tree_root_left_front
      (d2FlowTreeChild (children 0) 0) hgrandchild hgrandchildRole
  have hposition : d2FlowPosition
      (fun j => d2FlowTreeRootDeficit (children j)) 0 = 0 :=
    d2FlowPosition_zero _
  have hcutle : (d2FlowCutChild 0
      (d2FlowTreeRootDeficit (children 0))
      (low + quota i (role i) / 2)
      (d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) -
        high - quota i (role i) / 2)).2.1 <=
      low + quota i (role i) / 2 := by
    simpa [hposition] using d2FlowCutChild_first_left_le_parent_front
  rw [hgrandchildStage, hupdated]
  exact le_trans (by simpa [hposition] using hcutle) (by omega)

theorem d2FlowStage_regular_last_cut_le_grandchild_right_front
    {active : Nat -> Bool} {role : Nat -> D2Role}
    {quota : Nat -> D2Role -> Nat}
    {h i G low high : Nat} (children : Fin 8 -> D2FlowTree (h + 2))
    (ha : active i = true)
    (hr : role i = .topRise ∨ role i = .mid ∨ role i = .botDesc)
    (hnext : active (i + 1) = false)
    (hgrandchild : active (i + 2) = true)
    (hgrandchildRole : role (i + 2) = .topRise ∨
      role (i + 2) = .mid ∨ role (i + 2) = .botDesc)
    (hgrandchildEven : quota (i + 2) (role (i + 2)) % 2 = 0)
    (hbalance : low + high = G)
    (hcover : G <= d2FlowTotal
      (fun j => d2FlowTreeRootDeficit (children j)))
    (hallocation : quota i (role i) <=
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G)
    (hfront : high + quota i (role i) / 2 <= quota (i + 2)
      (role (i + 2)) / 2) :
    (d2FlowCutChild
      (d2FlowPosition (fun j => d2FlowTreeRootDeficit (children j)) 7)
      (d2FlowTreeRootDeficit (children 7))
      (low + quota i (role i) / 2)
      (d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) -
        high - quota i (role i) / 2)).2.2 <=
    (d2FlowTreeRootData
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowStage active role quota (h + 3) i
            (.node G low high children)) 7) 7)).2.2 := by
  let sizes : Fin 8 -> Nat := fun j => d2FlowTreeRootDeficit (children j)
  have hfrontTotal : high + quota i (role i) / 2 <=
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) := by
    have hhalf : quota i (role i) / 2 <= quota i (role i) := Nat.div_le_self _ _
    have htotal : G + quota i (role i) <=
        d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) := by
      omega
    omega
  have hrightEq : d2FlowTotal
      (fun j => d2FlowTreeRootDeficit (children j)) - high -
        quota i (role i) / 2 =
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) -
        (high + quota i (role i) / 2) := by omega
  have hparentFront := d2FlowCutChild_last_right_le_parent_front
    (sizes := sizes) (by simpa [sizes] using hfrontTotal) (by rfl)
  have hcutle : (d2FlowCutChild
      (d2FlowPosition sizes 7) (sizes 7)
      (low + quota i (role i) / 2)
      (d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) -
        high - quota i (role i) / 2)).2.2 <=
      high + quota i (role i) / 2 := by
    simpa [d2FlowCutChild, d2RightCut, sizes, hrightEq] using hparentFront
  have hgrandchildStage := d2FlowStage_regular_child_grandchild_stage
    (active := active) (role := role) (quota := quota)
    (h := h + 1) (i := i) (G := G) (low := low) (high := high)
    children ha hr hnext (7 : Fin 8) (7 : Fin 8)
  have hupdated : (d2FlowTreeRootData
      (d2FlowStage active role quota (h + 1) (i + 2)
        (d2FlowTreeChild (children 7) 7))).2.2 =
      (d2FlowTreeRootData (d2FlowTreeChild (children 7) 7)).2.2 +
        quota (i + 2) (role (i + 2)) / 2 :=
    d2FlowStage_active_ordinary_tree_root_right_front
      (d2FlowTreeChild (children 7) 7) hgrandchild hgrandchildEven
      hgrandchildRole
  rw [hgrandchildStage, hupdated]
  exact le_trans (by simpa [sizes] using hcutle) (by omega)

end Chvatal.D2Reserve
