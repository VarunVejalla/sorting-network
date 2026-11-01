import D2CandidateQuotaLower
import D2PhysicalBagState

namespace Chvatal.D2Reserve

open Chvatal.D2PhysicalBagState
open Chvatal.D2StaticWireSets

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

theorem d2FlowCutChild_endpoint_support
    (sizes : Fin 8 -> Nat) (left right : Nat)
    (hleft : left <= sizes 0) (hright : right <= sizes 7) :
    forall j : Fin 8,
      d2FlowCutChild (d2FlowPosition sizes j) (sizes j) left
        (d2FlowTotal sizes - right) =
      if j.val = 0 then (left, left, 0)
      else if j.val = 7 then (right, 0, right) else (0, 0, 0) := by
  have hordered := d2FlowPositionedChildren_ordered sizes
  have hend := d2FlowPosition_last_end sizes
  have hend' : d2FlowPosition sizes 7 + sizes 7 = d2FlowTotal sizes := by
    simpa using hend
  have htail : d2FlowPosition sizes 7 <= d2FlowTotal sizes - right := by
    have hsum : d2FlowPosition sizes 7 + right <= d2FlowTotal sizes := by
      rw [← hend']
      exact Nat.add_le_add_left hright _
    exact Nat.le_sub_of_add_le hsum
  have hprefix (j : Fin 8) (hj : 0 < j.val) :
      left <= d2FlowPosition sizes j := by
    by_cases hj7 : j.val = 7
    · have hj' : j = 7 := Fin.ext hj7
      have hpos : d2FlowPosition sizes j = d2FlowPosition sizes 7 := by
        simpa [d2FlowPosition, hj7]
      rw [hpos]
      exact le_trans hleft hordered.1
    · have hjlt : j.val < 7 := by omega
      exact le_trans hleft (hordered.2 j hj hjlt).1
  have hsuffix (j : Fin 8) (hj : j.val < 7) :
      d2FlowPosition sizes j + sizes j <= d2FlowTotal sizes - right := by
    have hbefore : d2FlowPosition sizes j + sizes j <=
        d2FlowPosition sizes 7 := by
      by_cases hj0 : j.val = 0
      · have hj' : j = 0 := Fin.ext hj0
        rw [hj']
        simpa [d2FlowPosition_zero] using hordered.1
      · exact (hordered.2 j (by omega) hj).2
    exact le_trans hbefore htail
  intro j
  by_cases hj0 : j.val = 0
  · have hj : j = 0 := Fin.ext hj0
    subst j
    rw [d2FlowPosition_zero]
    simp only [d2FlowCutChild, d2LeftCut, d2RightCut]
    have hmin : min (sizes 0) left = left := Nat.min_eq_right hleft
    have hs0 : sizes 0 <= d2FlowTotal sizes - right := by
      have := hsuffix (0 : Fin 8) (by norm_num)
      simpa [d2FlowPosition_zero] using this
    simp [d2FlowCutChild, d2LeftCut, d2RightCut,
      d2FlowPosition_zero, hmin, hs0]
  · by_cases hj7 : j.val = 7
    · have hj : j = 7 := Fin.ext hj7
      subst j
      simp only [d2FlowCutChild, d2LeftCut, d2RightCut]
      have hleftPos : left <= d2FlowPosition sizes 7 := hprefix 7 (by norm_num)
      have hleftZero : min (d2FlowPosition sizes 7 + sizes 7) left -
          d2FlowPosition sizes 7 = 0 := by omega
      have hrightEq : d2FlowPosition sizes 7 + sizes 7 -
          max (d2FlowPosition sizes 7) (d2FlowTotal sizes - right) = right := by
        rw [Nat.max_eq_right htail]
        rw [hend']
        omega
      simp only [hleftZero, hrightEq]
      simp
    · have hleftPos := hprefix j (by omega)
      have hrightPos := hsuffix j (by omega)
      simp only [d2FlowCutChild, d2LeftCut, d2RightCut]
      have hleftZero : min (d2FlowPosition sizes j + sizes j) left -
          d2FlowPosition sizes j = 0 := by omega
      have hrightZero : d2FlowPosition sizes j + sizes j -
          max (d2FlowPosition sizes j) (d2FlowTotal sizes - right) = 0 := by omega
      have hjne0 : j ≠ 0 := by
        intro heq
        have hv : j.val = 0 := by simpa using congrArg Fin.val heq
        omega
      simp [hleftZero, hrightZero, hjne0, hj7]

theorem d2FlowStageInvInputs_ordinary_fronts_fit_endpoint_child_deficits
    {scale h i G low high : Nat} {active : Nat -> Bool}
    {role : Nat -> D2Role} {quota : Nat -> D2Role -> Nat}
    {cap : Nat -> Nat} (children : Fin 8 -> D2FlowTree h)
    (hinputs : d2FlowStageInvInputs scale active role quota cap i
      (.node G low high children)) (ha : active i = true)
    (hr : role i = .topRise \/ role i = .mid \/ role i = .botDesc) :
    low + quota i (role i) / 2 <=
        d2FlowTreeRootDeficit (children 0) /\
      high + quota i (role i) / 2 <=
        d2FlowTreeRootDeficit (children 7) := by
  have hstage := hinputs.2
  simp only [ha, if_true] at hstage
  rcases hr with htop | hmid | hbot
  · simp only [htop] at hstage ⊢
    rcases hstage with ⟨hbalance, hG, hqcap, hqtotal, heven, hleft, hright⟩
    have hlow : low <= G := by omega
    have hhigh : high <= G := by omega
    have hquotaEven : quota i .topRise = 2 * (quota i .topRise / 2) := by omega
    have hfronts := d2_endpoint_fronts_fit_of_reserve
      hG hlow hhigh hqcap hquotaEven hleft hright
    simpa [htop] using ⟨hfronts.1, hfronts.2⟩
  · simp only [hmid] at hstage
    rcases hstage with ⟨hbalance, hG, hqcap, hqtotal, heven, hleft, hright⟩
    have hlow : low <= G := by omega
    have hhigh : high <= G := by omega
    have hquotaEven : quota i .mid = 2 * (quota i .mid / 2) := by omega
    have hfronts := d2_endpoint_fronts_fit_of_reserve
      hG hlow hhigh hqcap hquotaEven hleft hright
    simpa [hmid] using ⟨hfronts.1, hfronts.2⟩
  · simp only [hbot] at hstage
    rcases hstage with ⟨hbalance, hG, hqcap, hqtotal, heven, hleft, hright⟩
    have hlow : low <= G := by omega
    have hhigh : high <= G := by omega
    have hquotaEven : quota i .botDesc = 2 * (quota i .botDesc / 2) := by omega
    have hfronts := d2_endpoint_fronts_fit_of_reserve
      hG hlow hhigh hqcap hquotaEven hleft hright
    simpa [hbot] using ⟨hfronts.1, hfronts.2⟩

theorem d2FlowStageInvInputs_ordinary_cut_core
    {scale h i G low high : Nat} {active : Nat -> Bool}
    {role : Nat -> D2Role} {quota : Nat -> D2Role -> Nat}
    {cap : Nat -> Nat} (children : Fin 8 -> D2FlowTree h)
    (hinputs : d2FlowStageInvInputs scale active role quota cap i
      (.node G low high children)) (ha : active i = true)
    (hr : role i = .topRise \/ role i = .mid \/ role i = .botDesc) :
    low + high = G /\
      512 * G <= cap i /\
      256 * quota i (role i) <= cap i /\
      quota i (role i) <=
        d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G /\
      quota i (role i) % 2 = 0 := by
  have hstage := hinputs.2
  simp only [ha, if_true] at hstage
  rcases hr with htop | hmid | hbot
  · simp only [htop] at hstage ⊢
    rcases hstage with ⟨hbalance, hG, hqcap, halloc, heven, hleft, hright⟩
    simpa [htop] using ⟨hbalance, hG, hqcap, halloc, heven⟩
  · simp only [hmid] at hstage ⊢
    rcases hstage with ⟨hbalance, hG, hqcap, halloc, heven, hleft, hright⟩
    simpa [hmid] using ⟨hbalance, hG, hqcap, halloc, heven⟩
  · simp only [hbot] at hstage ⊢
    rcases hstage with ⟨hbalance, hG, hqcap, halloc, heven, hleft, hright⟩
    simpa [hbot] using ⟨hbalance, hG, hqcap, halloc, heven⟩


theorem d2FlowStage_active_ordinary_root_fronts_le_child_native
    {scale h i G low high : Nat} {active : Nat -> Bool}
    {role : Nat -> D2Role} {quota : Nat -> D2Role -> Nat}
    {cap : Nat -> Nat} (children : Fin 8 -> D2FlowTree h)
    (htree : d2FlowTreeInv scale (.node G low high children))
    (hinputs : d2FlowStageInvInputs scale active role quota cap i
      (.node G low high children)) (ha : active i = true)
    (hr : role i = .topRise \/ role i = .mid \/ role i = .botDesc) :
    (d2FlowTreeRootData
      (d2FlowStage active role quota (h + 1) i
        (.node G low high children))).2.1 <= scale * 8 ^ h /\
    (d2FlowTreeRootData
      (d2FlowStage active role quota (h + 1) i
        (.node G low high children))).2.2 <= scale * 8 ^ h := by
  have hfronts := d2FlowStageInvInputs_ordinary_fronts_fit_endpoint_child_deficits
    children hinputs ha hr
  have hparity := d2FlowStageInvInputs_ordinary_front_bounds children hinputs ha hr
  have hrootLeft : (d2FlowTreeRootData
      (d2FlowStage active role quota (h + 1) i
        (.node G low high children))).2.1 = low + quota i (role i) / 2 := by
    rcases hr with htop | hmid | hbot
    · simp [d2FlowStage, ha, htop, d2FlowTreeRootData]
    · simp [d2FlowStage, ha, hmid, d2FlowTreeRootData]
    · simp [d2FlowStage, ha, hbot, d2FlowTreeRootData]
  have hrootRight : (d2FlowTreeRootData
      (d2FlowStage active role quota (h + 1) i
        (.node G low high children))).2.2 = high + quota i (role i) / 2 := by
    rcases hr with htop | hmid | hbot
    · have hquotaEven : quota i .topRise % 2 = 0 := by
        simpa [htop] using hparity.1
      simp [d2FlowStage, ha, htop, d2FlowTreeRootData]
      omega
    · have hquotaEven : quota i .mid % 2 = 0 := by
        simpa [hmid] using hparity.1
      simp [d2FlowStage, ha, hmid, d2FlowTreeRootData]
      omega
    · have hquotaEven : quota i .botDesc % 2 = 0 := by
        simpa [hbot] using hparity.1
      simp [d2FlowStage, ha, hbot, d2FlowTreeRootData]
      omega
  have hchildInv : forall j, d2FlowTreeInv scale (children j) := by
    have hx := htree
    simp only [d2FlowTreeInv] at hx
    exact hx.2.2.2
  have hsize0 := d2FlowTreeInv_root_native_bound (children 0) (hchildInv 0)
  have hsize7 := d2FlowTreeInv_root_native_bound (children 7) (hchildInv 7)
  rw [hrootLeft, hrootRight]
  exact ⟨le_trans hfronts.1 hsize0, le_trans hfronts.2 hsize7⟩

theorem d2FlowStage_active_ordinary_root_fronts_le_tree_native
    {scale h i : Nat} {active : Nat -> Bool}
    {role : Nat -> D2Role} {quota : Nat -> D2Role -> Nat}
    {cap : Nat -> Nat} (tree : D2FlowTree (h + 1))
    (htree : d2FlowTreeInv scale tree)
    (hinputs : d2FlowStageInvInputs scale active role quota cap i tree)
    (ha : active i = true)
    (hr : role i = .topRise \/ role i = .mid \/ role i = .botDesc) :
    ((d2FlowTreeRootData (d2FlowStage active role quota (h + 1) i tree)).2.1 <= scale * 8 ^ h /\
     (d2FlowTreeRootData (d2FlowStage active role quota (h + 1) i tree)).2.2 <= scale * 8 ^ h) := by
  cases tree with
  | node G low high children =>
      exact d2FlowStage_active_ordinary_root_fronts_le_child_native
        children htree hinputs ha hr

theorem d2FlowStageInvInputs_grandchild
    {scale h i : Nat} {active : Nat -> Bool}
    {role : Nat -> D2Role} {quota : Nat -> D2Role -> Nat}
    {cap : Nat -> Nat} (tree : D2FlowTree (h + 2))
    (hinputs : d2FlowStageInvInputs scale active role quota cap i tree)
    (j k : Fin 8) :
    d2FlowStageInvInputs scale active role quota cap (i + 2)
      (d2FlowTreeChild (d2FlowTreeChild tree j) k) := by
  cases tree with
  | node G low high children =>
      have hchild := hinputs.1 j
      cases htreeChild : children j with
      | node G' low' high' grandchildren =>
          rw [htreeChild] at hchild
          change (forall k, d2FlowStageInvInputs scale active role quota cap
            (i + 2) (grandchildren k)) /\ _ at hchild
          simpa [d2FlowTreeChild, htreeChild] using hchild.1 k

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

theorem d2FlowCandidateStage_regular_first_cut_le_grandchild_left_front
    {d i t h G low high : Nat} (children : Fin 8 -> D2FlowTree (h + 2))
    (hd : 7 <= d) (ht : 2 <= t)
    (hparent : d2FlowCandidateActive d t i = true)
    (hparentRole : d2FlowCandidateRole d t i = .topRise \/
      d2FlowCandidateRole d t i = .mid \/
      d2FlowCandidateRole d t i = .botDesc)
    (hgrandchild : d2FlowCandidateActive d t (i + 2) = true)
    (hgrandchildRole : d2FlowCandidateRole d t (i + 2) = .topRise \/
      d2FlowCandidateRole d t (i + 2) = .mid \/
      d2FlowCandidateRole d t (i + 2) = .botDesc)
    (hinputs : d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d t) (d2FlowCandidateRole d t)
      (d2FlowCandidateQuota d t)
      (fun k => d2FlowCandidateCapacity d k t) i
      (.node G low high children)) :
    let stage := d2FlowStage (d2FlowCandidateActive d t)
      (d2FlowCandidateRole d t) (d2FlowCandidateQuota d t)
      (h + 3) i (.node G low high children)
    (d2FlowCutChild (d2FlowPosition
      (fun j => d2FlowTreeRootDeficit (children j)) 0)
      (d2FlowTreeRootDeficit (children 0))
      (low + d2FlowCandidateQuota d t i
        (d2FlowCandidateRole d t i) / 2)
      (d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - high -
        d2FlowCandidateQuota d t i (d2FlowCandidateRole d t i) / 2)).2.1 <=
      (d2FlowTreeRootData
        (d2FlowTreeChild (d2FlowTreeChild stage 0) 0)).2.1 := by
  have hcore := d2FlowStageInvInputs_ordinary_cut_core children hinputs
    hparent hparentRole
  have hlow : low <= G := by omega
  have hfront := d2FlowCandidate_front_le_grandchild_half_quota
    hd ht hparent hgrandchild hgrandchildRole hlow hcore.2.1 hcore.2.2.1
  have hnext := d2FlowCandidateActive_adjacent_false_of_active hparent
  simpa using (d2FlowStage_regular_first_cut_le_grandchild_left_front
    (active := d2FlowCandidateActive d t)
    (role := d2FlowCandidateRole d t)
    (quota := d2FlowCandidateQuota d t)
    children hparent hparentRole hnext hgrandchild hgrandchildRole hfront)

theorem d2FlowCandidateStage_regular_cut_endpoint_support
    {d i t h G low high : Nat} (children : Fin 8 -> D2FlowTree h)
    (hparent : d2FlowCandidateActive d t i = true)
    (hparentRole : d2FlowCandidateRole d t i = .topRise \/
      d2FlowCandidateRole d t i = .mid \/
      d2FlowCandidateRole d t i = .botDesc)
    (hinputs : d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d t) (d2FlowCandidateRole d t)
      (d2FlowCandidateQuota d t)
      (fun k => d2FlowCandidateCapacity d k t) i
      (.node G low high children)) :
    forall j : Fin 8,
      d2FlowCutChild (d2FlowPosition
        (fun k => d2FlowTreeRootDeficit (children k)) j)
        (d2FlowTreeRootDeficit (children j))
        (low + d2FlowCandidateQuota d t i
          (d2FlowCandidateRole d t i) / 2)
        (d2FlowTotal (fun k => d2FlowTreeRootDeficit (children k)) - high -
          d2FlowCandidateQuota d t i
            (d2FlowCandidateRole d t i) / 2) =
      if j.val = 0 then
        (low + d2FlowCandidateQuota d t i
          (d2FlowCandidateRole d t i) / 2,
         low + d2FlowCandidateQuota d t i
          (d2FlowCandidateRole d t i) / 2, 0)
      else if j.val = 7 then
        (high + d2FlowCandidateQuota d t i
          (d2FlowCandidateRole d t i) / 2, 0,
         high + d2FlowCandidateQuota d t i
          (d2FlowCandidateRole d t i) / 2)
      else (0, 0, 0) := by
  have hfronts := d2FlowStageInvInputs_ordinary_fronts_fit_endpoint_child_deficits
    children hinputs hparent hparentRole
  have hrightEq := d2FlowStage_right_front_subtraction_eq
    children hinputs hparent hparentRole
  rw [hrightEq]
  exact d2FlowCutChild_endpoint_support
    (fun k => d2FlowTreeRootDeficit (children k))
    (low + d2FlowCandidateQuota d t i
      (d2FlowCandidateRole d t i) / 2)
    (high + d2FlowCandidateQuota d t i
      (d2FlowCandidateRole d t i) / 2)
    hfronts.1 hfronts.2

theorem d2FlowCandidateStage_regular_last_cut_le_grandchild_right_front
    {d i t h G low high : Nat} (children : Fin 8 -> D2FlowTree (h + 2))
    (hd : 7 <= d) (ht : 2 <= t)
    (hparent : d2FlowCandidateActive d t i = true)
    (hparentRole : d2FlowCandidateRole d t i = .topRise \/
      d2FlowCandidateRole d t i = .mid \/
      d2FlowCandidateRole d t i = .botDesc)
    (hgrandchild : d2FlowCandidateActive d t (i + 2) = true)
    (hgrandchildRole : d2FlowCandidateRole d t (i + 2) = .topRise \/
      d2FlowCandidateRole d t (i + 2) = .mid \/
      d2FlowCandidateRole d t (i + 2) = .botDesc)
    (htree : d2FlowTreeInv 8192 (.node G low high children))
    (hinputs : d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d t) (d2FlowCandidateRole d t)
      (d2FlowCandidateQuota d t)
      (fun k => d2FlowCandidateCapacity d k t) i
      (.node G low high children)) :
    let stage := d2FlowStage (d2FlowCandidateActive d t)
      (d2FlowCandidateRole d t) (d2FlowCandidateQuota d t)
      (h + 3) i (.node G low high children)
    (d2FlowCutChild
      (d2FlowPosition (fun j => d2FlowTreeRootDeficit (children j)) 7)
      (d2FlowTreeRootDeficit (children 7))
      (low + d2FlowCandidateQuota d t i
        (d2FlowCandidateRole d t i) / 2)
      (d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - high -
        d2FlowCandidateQuota d t i (d2FlowCandidateRole d t i) / 2)).2.2 <=
      (d2FlowTreeRootData
        (d2FlowTreeChild (d2FlowTreeChild stage 7) 7)).2.2 := by
  classical
  have hcore := d2FlowStageInvInputs_ordinary_cut_core children hinputs
    hparent hparentRole
  have hhigh : high <= G := by omega
  have hfront := d2FlowCandidate_front_le_grandchild_half_quota
    hd ht hparent hgrandchild hgrandchildRole hhigh hcore.2.1 hcore.2.2.1
  have hnext := d2FlowCandidateActive_adjacent_false_of_active hparent
  have hgrandchildSchedule : active d (tfD2 d) (i + 2) t := by
    have hactiveEq := d2FlowCandidateActive_matches_schedule
      (d := d) (t := t) (i := i + 2) (by omega)
    rw [hactiveEq] at hgrandchild
    exact of_decide_eq_true hgrandchild
  have hroleEq := d2FlowCandidateRole_matches_schedule
    (d := d) (t := t) (i := i + 2) (by omega)
  have hgrandchildScheduleRole : d2ScheduleRole d (i + 2) t = .topRise \/
      d2ScheduleRole d (i + 2) t = .mid \/
      d2ScheduleRole d (i + 2) t = .botDesc := by
    rw [hroleEq] at hgrandchildRole
    exact hgrandchildRole
  have hgrandchildEven := d2FlowCandidateQuota_even hd
    hgrandchildSchedule (by omega) hgrandchildScheduleRole
  have hcover : G <= d2FlowTotal
      (fun j => d2FlowTreeRootDeficit (children j)) := htree.2.1
  have hrightReserve : d2FlowCandidateQuota d t i
      (d2FlowCandidateRole d t i) <=
        d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G :=
    hcore.2.2.2.1
  simpa using (d2FlowStage_regular_last_cut_le_grandchild_right_front
    (active := d2FlowCandidateActive d t)
    (role := d2FlowCandidateRole d t)
    (quota := d2FlowCandidateQuota d t)
    children hparent hparentRole hnext hgrandchild hgrandchildRole
    hgrandchildEven hcore.1 hcover hrightReserve hfront)

theorem d2FlowCandidateStage_regular_endpoint_cuts_le_grandchild_native
    {d i t h G low high : Nat} (children : Fin 8 -> D2FlowTree (h + 2))
    (hd : 7 <= d) (ht : 2 <= t)
    (hparent : d2FlowCandidateActive d t i = true)
    (hparentRole : d2FlowCandidateRole d t i = .topRise \/
      d2FlowCandidateRole d t i = .mid \/
      d2FlowCandidateRole d t i = .botDesc)
    (hgrandchild : d2FlowCandidateActive d t (i + 2) = true)
    (hgrandchildRole : d2FlowCandidateRole d t (i + 2) = .topRise \/
      d2FlowCandidateRole d t (i + 2) = .mid \/
      d2FlowCandidateRole d t (i + 2) = .botDesc)
    (htree : d2FlowTreeInv 8192 (.node G low high children))
    (hinputs : d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d t) (d2FlowCandidateRole d t)
      (d2FlowCandidateQuota d t)
      (fun k => d2FlowCandidateCapacity d k t) i
      (.node G low high children)) :
    let stage := d2FlowStage (d2FlowCandidateActive d t)
      (d2FlowCandidateRole d t) (d2FlowCandidateQuota d t)
      (h + 3) i (.node G low high children)
    (d2FlowCutChild (d2FlowPosition
      (fun j => d2FlowTreeRootDeficit (children j)) 0)
      (d2FlowTreeRootDeficit (children 0))
      (low + d2FlowCandidateQuota d t i
        (d2FlowCandidateRole d t i) / 2)
      (d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - high -
        d2FlowCandidateQuota d t i (d2FlowCandidateRole d t i) / 2)).2.1 <=
        8192 * 8 ^ h /\
    (d2FlowCutChild
      (d2FlowPosition (fun j => d2FlowTreeRootDeficit (children j)) 7)
      (d2FlowTreeRootDeficit (children 7))
      (low + d2FlowCandidateQuota d t i
        (d2FlowCandidateRole d t i) / 2)
      (d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - high -
        d2FlowCandidateQuota d t i (d2FlowCandidateRole d t i) / 2)).2.2 <=
        8192 * 8 ^ h := by
  let stage := d2FlowStage (d2FlowCandidateActive d t)
      (d2FlowCandidateRole d t) (d2FlowCandidateQuota d t)
      (h + 3) i (.node G low high children)
  have hfirstCut := d2FlowCandidateStage_regular_first_cut_le_grandchild_left_front
    children hd ht hparent hparentRole hgrandchild hgrandchildRole hinputs
  have hlastCut := d2FlowCandidateStage_regular_last_cut_le_grandchild_right_front
    children hd ht hparent hparentRole hgrandchild hgrandchildRole htree hinputs
  have hnext := d2FlowCandidateActive_adjacent_false_of_active hparent
  have hfrontFirst := d2FlowStage_active_ordinary_root_fronts_le_tree_native
    (d2FlowTreeChild (children 0) 0)
    (d2FlowTreeInv_grandchild (.node G low high children) htree 0 0)
    (d2FlowStageInvInputs_grandchild (.node G low high children) hinputs 0 0)
    hgrandchild hgrandchildRole
  have hfrontLast := d2FlowStage_active_ordinary_root_fronts_le_tree_native
    (d2FlowTreeChild (children 7) 7)
    (d2FlowTreeInv_grandchild (.node G low high children) htree 7 7)
    (d2FlowStageInvInputs_grandchild (.node G low high children) hinputs 7 7)
    hgrandchild hgrandchildRole
  have hstageFirst := d2FlowStage_regular_child_grandchild_stage
    (active := d2FlowCandidateActive d t) (role := d2FlowCandidateRole d t)
    (quota := d2FlowCandidateQuota d t) (h := h + 1) (i := i)
    (G := G) (low := low) (high := high) children hparent hparentRole hnext 0 0
  have hstageLast := d2FlowStage_regular_child_grandchild_stage
    (active := d2FlowCandidateActive d t) (role := d2FlowCandidateRole d t)
    (quota := d2FlowCandidateQuota d t) (h := h + 1) (i := i)
    (G := G) (low := low) (high := high) children hparent hparentRole hnext 7 7
  have hstageFirst' :
      d2FlowTreeChild (d2FlowTreeChild
        (d2FlowStage (d2FlowCandidateActive d t) (d2FlowCandidateRole d t)
          (d2FlowCandidateQuota d t) (h + 3) i (.node G low high children)) 0) 0 =
      d2FlowStage (d2FlowCandidateActive d t) (d2FlowCandidateRole d t)
        (d2FlowCandidateQuota d t) (h + 1) (i + 2)
        (d2FlowTreeChild (children 0) 0) := by
    convert hstageFirst using 1 <;> omega
  have hstageLast' :
      d2FlowTreeChild (d2FlowTreeChild
        (d2FlowStage (d2FlowCandidateActive d t) (d2FlowCandidateRole d t)
          (d2FlowCandidateQuota d t) (h + 3) i (.node G low high children)) 7) 7 =
      d2FlowStage (d2FlowCandidateActive d t) (d2FlowCandidateRole d t)
        (d2FlowCandidateQuota d t) (h + 1) (i + 2)
        (d2FlowTreeChild (children 7) 7) := by
    convert hstageLast using 1 <;> omega
  dsimp at hfirstCut hlastCut
  rw [hstageFirst'] at hfirstCut
  rw [hstageLast'] at hlastCut
  constructor
  · simpa [stage] using le_trans hfirstCut hfrontFirst.1
  · simpa [stage] using le_trans hlastCut hfrontLast.2

/-- An ordinary update's clamped child holes fit inside its updated parent
fronts. The endpoint reserve forces all six interior cuts to vanish; the two
remaining cuts lie in the outer child slots by the native-front bounds. -/
theorem d2FlowStage_active_ordinary_clamped_fit_of_inputs
    {scale h i G low high : Nat} {active : Nat -> Bool}
    {role : Nat -> D2Role} {quota : Nat -> D2Role -> Nat}
    {cap : Nat -> Nat} (children : Fin 8 -> D2FlowTree h)
    (htree : d2FlowTreeInv scale (.node G low high children))
    (hinputs : d2FlowStageInvInputs scale active role quota cap i
      (.node G low high children)) (ha : active i = true)
    (hr : role i = .topRise \/ role i = .mid \/ role i = .botDesc) :
    StaticHolesFit
      ((d2FlowTreeRootData
        (d2FlowStage active role quota (h + 1) i
          (.node G low high children))).2.1)
      (d2FlowNodeStaticHolesClamped 0 (scale * 8 ^ h)
        ((d2FlowTreeRootData
          (d2FlowStage active role quota (h + 1) i
            (.node G low high children))).2.1)
        ((d2FlowTreeRootData
          (d2FlowStage active role quota (h + 1) i
            (.node G low high children))).2.2)
        (fun j => d2FlowTreeChild
          (d2FlowStage active role quota (h + 1) i
            (.node G low high children)) j))
      (8 * (scale * 8 ^ h) -
        (d2FlowTreeRootData
          (d2FlowStage active role quota (h + 1) i
            (.node G low high children))).2.2) := by
  let stage := d2FlowStage active role quota (h + 1) i
    (.node G low high children)
  let outChildren : Fin 8 -> D2FlowTree h := fun j => d2FlowTreeChild stage j
  have hcore := d2FlowStageInvInputs_ordinary_cut_core children hinputs ha hr
  have hreserve := d2FlowStageInvInputs_ordinary_fronts_fit_endpoint_child_deficits
    children hinputs ha hr
  have hrightEq := d2FlowStage_right_front_subtraction_eq
    children hinputs ha hr
  have hleftValue : (d2FlowTreeRootData stage).2.1 =
      low + quota i (role i) / 2 := by
    rcases hr with htop | hmid | hbot
    · simp [stage, d2FlowStage, ha, htop, d2FlowTreeRootData]
    · simp [stage, d2FlowStage, ha, hmid, d2FlowTreeRootData]
    · simp [stage, d2FlowStage, ha, hbot, d2FlowTreeRootData]
  have hrightValue : (d2FlowTreeRootData stage).2.2 =
      high + quota i (role i) / 2 := by
    rcases hr with htop | hmid | hbot
    · have heven : quota i .topRise % 2 = 0 := by
        simpa [htop] using hcore.2.2.2.2
      simp [stage, d2FlowStage, ha, htop, d2FlowTreeRootData]
      omega
    · have heven : quota i .mid % 2 = 0 := by
        simpa [hmid] using hcore.2.2.2.2
      simp [stage, d2FlowStage, ha, hmid, d2FlowTreeRootData]
      omega
    · have heven : quota i .botDesc % 2 = 0 := by
        simpa [hbot] using hcore.2.2.2.2
      simp [stage, d2FlowStage, ha, hbot, d2FlowTreeRootData]
      omega
  have hparent : (d2FlowTreeRootData stage).2.1 <=
      8 * (scale * 8 ^ h) - (d2FlowTreeRootData stage).2.2 := by
    have hsum : (d2FlowTreeRootData stage).2.1 +
        (d2FlowTreeRootData stage).2.2 = G + quota i (role i) := by
      rw [hleftValue, hrightValue]
      omega
    have htotal : d2FlowTotal
        (fun j => d2FlowTreeRootDeficit (children j)) <= 8 * (scale * 8 ^ h) := by
      have hcap : forall j, d2FlowTreeRootDeficit (children j) <= scale * 8 ^ h := by
        intro j
        exact d2FlowTreeInv_root_native_bound (children j) (htree.2.2.2 j)
      have := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hcap j)
      simpa [d2FlowTotal] using this
    have halloc : G + quota i (role i) <=
        d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) := by
      have hquota := hcore.2.2.2.1
      have hGtotal : G <= d2FlowTotal
          (fun j => d2FlowTreeRootDeficit (children j)) := by
        simpa [d2FlowTotal] using htree.2.1
      have hsum := (Nat.le_sub_iff_add_le hGtotal).mp hquota
      simpa [Nat.add_comm] using hsum
    have hsumBound : (d2FlowTreeRootData stage).2.1 +
        (d2FlowTreeRootData stage).2.2 <= 8 * (scale * 8 ^ h) := by
      rw [hsum]
      exact le_trans halloc htotal
    exact Nat.le_sub_of_add_le hsumBound
  have hinvOut : forall j, d2FlowTreeInv scale (outChildren j) := by
    have hout := d2FlowStage_preserves_inv_of_inputs
      (.node G low high children) htree hinputs
    rcases hr with htop | hmid | hbot
    · have hout' := hout
      simp only [d2FlowStage, ha, htop, d2FlowTreeInv] at hout'
      intro j
      simpa [outChildren, stage, d2FlowStage, ha, htop, d2FlowTreeChild] using hout'.2.2.2 j
    · have hout' := hout
      simp only [d2FlowStage, ha, hmid, d2FlowTreeInv] at hout'
      intro j
      simpa [outChildren, stage, d2FlowStage, ha, hmid, d2FlowTreeChild] using hout'.2.2.2 j
    · have hout' := hout
      simp only [d2FlowStage, ha, hbot, d2FlowTreeInv] at hout'
      intro j
      simpa [outChildren, stage, d2FlowStage, ha, hbot, d2FlowTreeChild] using hout'.2.2.2 j
  have hcontain : forall j,
      d2FlowTreeRootDeficit (outChildren j) < scale * 8 ^ h ->
        (0 + (d2FlowTreeRootData stage).2.1 <=
          0 + j.val * (scale * 8 ^ h) + (d2FlowTreeRootData (outChildren j)).2.1 /\
        0 + (j.val + 1) * (scale * 8 ^ h) -
          (d2FlowTreeRootData (outChildren j)).2.2 <=
            0 + 8 * (scale * 8 ^ h) - (d2FlowTreeRootData stage).2.2) := by
    intro j _
    have hdata := d2FlowStage_regular_child_root_data
      (active := active) (role := role) (quota := quota)
      (h := h) (i := i) (G := G) (low := low) (high := high)
      children ha hr j
    rw [hrightEq] at hdata
    have hcuts := d2FlowCutChild_endpoint_support
      (fun k => d2FlowTreeRootDeficit (children k))
      (low + quota i (role i) / 2) (high + quota i (role i) / 2)
      hreserve.1 hreserve.2 j
    rw [show outChildren j = d2FlowTreeChild stage j by rfl, hdata]
    have hsmallL : (low + quota i (role i) / 2) <= scale * 8 ^ h := by
      exact le_trans hreserve.1
        (d2FlowTreeInv_root_native_bound (children 0) (htree.2.2.2 0))
    have hsmallR : (high + quota i (role i) / 2) <= scale * 8 ^ h := by
      exact le_trans hreserve.2
        (d2FlowTreeInv_root_native_bound (children 7) (htree.2.2.2 7))
    rw [hcuts]
    rw [hleftValue, hrightValue]
    by_cases hj0 : j.val = 0
    · simp [hj0]
      omega
    · by_cases hj7 : j.val = 7
      · simp [hj0, hj7]
        omega
      · simp [hj0, hj7]
        have hjlo : 1 <= j.val := by omega
        have hjhi : j.val + 1 <= 7 := by omega
        have hslotL : scale * 8 ^ h <= j.val * (scale * 8 ^ h) := by
          have hm := Nat.mul_le_mul_right (scale * 8 ^ h) hjlo
          simpa using hm
        have hslotR : (j.val + 1) * (scale * 8 ^ h) <=
            7 * (scale * 8 ^ h) := Nat.mul_le_mul_right (scale * 8 ^ h) hjhi
        have hparentR : 7 * (scale * 8 ^ h) <=
            8 * (scale * 8 ^ h) - (high + quota i (role i) / 2) := by
          apply Nat.le_sub_of_add_le
          have := hsmallR
          omega
        constructor <;> omega
  have hfit := d2FlowNodeStaticHolesClamped_fit_of_child_intervals_contained
    (base := 0) (width := scale * 8 ^ h)
    (left := (d2FlowTreeRootData stage).2.1)
    (right := (d2FlowTreeRootData stage).2.2)
    outChildren rfl hinvOut (by simpa using hparent) hcontain
  simpa using hfit

/-! When a parent overwrites a child root, the changed fronts need only be
checked against the two exposed edge grandchildren. The six interior slots
remain inside the parent whenever each new front is at most one child width. -/

theorem d2FlowNodeStaticHolesClamped_fit_of_endpoint_front_bounds
    {scale h width left right : Nat} (children : Fin 8 -> D2FlowTree h)
    (hwidth : width = scale * 8 ^ h)
    (hinv : forall j, d2FlowTreeInv scale (children j))
    (hparent : left <= 8 * width - right)
    (hleft : left <= width) (hright : right <= width)
    (hfirst : d2FlowTreeRootDeficit (children 0) < width ->
      left <= (d2FlowTreeRootData (children 0)).2.1)
    (hlast : d2FlowTreeRootDeficit (children 7) < width ->
      right <= (d2FlowTreeRootData (children 7)).2.2) :
    StaticHolesFit left
      (d2FlowNodeStaticHolesClamped 0 width left right children)
      (8 * width - right) := by
  have hfit := d2FlowNodeStaticHolesClamped_fit_of_child_intervals_contained
    (base := 0) (width := width) (left := left) (right := right)
    children hwidth hinv (by simpa using hparent) (by
      intro j hunsat
      constructor
      · by_cases hj : j.val = 0
        · have hj' : j = (0 : Fin 8) := Fin.ext hj
          subst j
          simpa [Nat.zero_add] using hfirst hunsat
        · have hjpos : 1 <= j.val := by omega
          have hslot : width <= j.val * width := by
            simpa using Nat.mul_le_mul_right width hjpos
          have hbound : left <= j.val * width +
              (d2FlowTreeRootData (children j)).2.1 := by
            calc
            left <= width := hleft
            _ <= j.val * width := hslot
            _ <= j.val * width +
                (d2FlowTreeRootData (children j)).2.1 := Nat.le_add_right _ _
          simpa [Nat.zero_add] using hbound
      · by_cases hj : j.val = 7
        · have hj' : j = (7 : Fin 8) := Fin.ext hj
          subst j
          simpa [Nat.zero_add] using
            Nat.sub_le_sub_left (hlast hunsat) (8 * width)
        · have hjlt : j.val + 1 <= 7 := by omega
          have hslot : (j.val + 1) * width <= 7 * width :=
            Nat.mul_le_mul_right width hjlt
          have hstop : 7 * width <= 8 * width - right := by
            apply Nat.le_sub_of_add_le
            omega
          have hbound : (j.val + 1) * width -
              (d2FlowTreeRootData (children j)).2.2 <= 8 * width - right :=
            le_trans (Nat.sub_le _ _) (le_trans hslot hstop)
          simpa [Nat.zero_add] using hbound)
  simpa using hfit

/-- The ordinary two-front contract makes both updated root fronts at most
`width` whenever scheduled capacity is at most `256 * width`. -/
theorem d2FlowStage_active_ordinary_fronts_le_width_of_capacity
    {scale h width i G low high : Nat} {active : Nat -> Bool}
    {role : Nat -> D2Role} {quota : Nat -> D2Role -> Nat}
    {cap : Nat -> Nat} (children : Fin 8 -> D2FlowTree h)
    (hinputs : d2FlowStageInvInputs scale active role quota cap i
      (.node G low high children)) (ha : active i = true)
    (hr : role i = .topRise \/ role i = .mid \/ role i = .botDesc)
    (hcap : cap i <= 256 * width) :
    low + quota i (role i) / 2 <= width /\
      high + quota i (role i) / 2 <= width := by
  have hcore := d2FlowStageInvInputs_ordinary_cut_core children hinputs ha hr
  have hlow : low <= G := by omega
  have hhigh : high <= G := by omega
  have hsmallLow : 512 * low <= cap i := by
    exact le_trans (Nat.mul_le_mul_left 512 hlow) hcore.2.1
  have hsmallHigh : 512 * high <= cap i := by
    exact le_trans (Nat.mul_le_mul_left 512 hhigh) hcore.2.1
  have hsmallQuota : 256 * quota i (role i) <= cap i := hcore.2.2.1
  have hbudget : cap i + cap i <= 512 * width := by omega
  have hleftSum : 512 * low + 256 * quota i (role i) <=
      512 * width := by omega
  have hrightSum : 512 * high + 256 * quota i (role i) <=
      512 * width := by omega
  constructor <;> omega

/-- If the tree height at path level `i` is `d-i`, an active ordinary
grandchild two levels below forces the candidate's scheduled capacity below
256 times one native grandchild slot. -/
theorem d2FlowCandidateCapacity_le_256_grandchild_slot
    {d i t h : Nat} (hd : 7 <= d) (ht : 2 <= t)
    (htf : t < tfD2 d)
    (hgrandchild : d2FlowCandidateActive d t (i + 2) = true)
    (hdepth : d = i + h + 3) :
    d2FlowCandidateCapacity d i t <= 256 * (8192 * 8 ^ (h + 1)) := by
  classical
  have hgrandchildSchedule : active d (tfD2 d) (i + 2) t := by
    rw [d2FlowCandidateActive_matches_schedule (d := d) (t := t)
      (i := i + 2) (show 0 < t by omega)] at hgrandchild
    exact of_decide_eq_true hgrandchild
  have hfront := (active_iff_frontiers (d := d) (tf := tfD2 d)
    (i := i + 2) (t := t) ht).1 hgrandchildSchedule
  have hthreshold := (i_le_omega_iff_threshold ht hfront.2.2.2).1
    hfront.2.2.1
  have htime : 3 * i - 3 <= t := by omega
  have hexp : d2FlowCandidateCapacityExponent d i t <= 24 + 3 * h := by
    rw [hdepth]
    unfold d2FlowCandidateCapacityExponent
    omega
  have h8pow : (8 : Nat) ^ (h + 1) = (2 : Nat) ^ (3 * (h + 1)) := by
    rw [show (8 : Nat) = 2 ^ 3 by norm_num, Nat.pow_mul]
  have hscale : (2 : Nat) ^ (24 + 3 * h) =
      256 * (8192 * 8 ^ (h + 1)) := by
    rw [h8pow]
    norm_num [Nat.pow_add]
    ring
  calc
    d2FlowCandidateCapacity d i t =
        2 ^ d2FlowCandidateCapacityExponent d i t := rfl
    _ <= 2 ^ (24 + 3 * h) := Nat.pow_le_pow_right (by omega) hexp
    _ = 256 * (8192 * 8 ^ (h + 1)) := hscale

/-- A bot-descending sender is the current bottom frontier, so the level two
below it is outside the active interval. -/
theorem d2FlowCandidateActive_two_levels_below_false_of_botDesc
    {d i t : Nat} (hd : 7 <= d) (ht : 2 <= t)
    (htf : t < tfD2 d)
    (hrole : d2FlowCandidateRole d t i = .botDesc) :
    d2FlowCandidateActive d t (i + 2) = false := by
  classical
  have hroleEq := d2FlowCandidateRole_matches_schedule
    (d := d) (t := t) (i := i) (by omega)
  have hroleSchedule : d2ScheduleRole d i t = .botDesc := by
    rw [← hroleEq]
    exact hrole
  have hphase := d2ScheduleRole_botDesc_phase ht hroleSchedule
  have hfrontier : i = omega t := by
    rcases hphase with ⟨j, hj, htEq, hiEq⟩ | ⟨j, htEq, hiEq⟩
    · rw [htEq, hiEq]
      exact (omega_three_mul_add_one j).symm
    · rw [htEq, hiEq]
      exact (omega_three_mul_add_two j).symm
  have hnotActive : ¬ active d (tfD2 d) (i + 2) t := by
    intro ha
    have hwindow := (active_iff_frontiers (d := d) (tf := tfD2 d)
      (i := i + 2) (t := t) ht).1 ha
    have hupper := hwindow.2.2.1
    omega
  rw [d2FlowCandidateActive_matches_schedule (d := d) (t := t)
    (i := i + 2) (by omega)]
  simp [hnotActive]

/-- In the active-ordinary-grandchild case, the first child overwritten by an
ordinary parent has a fitted clamped root interval. The only extra scale gate
is that the parent's scheduled capacity be at most 256 times one grandchild
slot; the endpoint-cut theorem supplies the unsaturated edge-front bound. -/
theorem d2FlowCandidateStage_first_child_clamped_fit_of_ordinary_grandchild
    {d i t h G low high : Nat} (children : Fin 8 -> D2FlowTree (h + 2))
    (hd : 7 <= d) (ht : 2 <= t)
    (hparent : d2FlowCandidateActive d t i = true)
    (hparentRole : d2FlowCandidateRole d t i = .topRise \/
      d2FlowCandidateRole d t i = .mid \/
      d2FlowCandidateRole d t i = .botDesc)
    (hgrandchild : d2FlowCandidateActive d t (i + 2) = true)
    (hgrandchildRole : d2FlowCandidateRole d t (i + 2) = .topRise \/
      d2FlowCandidateRole d t (i + 2) = .mid \/
      d2FlowCandidateRole d t (i + 2) = .botDesc)
    (htf : t < tfD2 d) (hdepth : d = i + h + 3)
    (htree : d2FlowTreeInv 8192 (.node G low high children))
    (hinputs : d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d t) (d2FlowCandidateRole d t)
      (d2FlowCandidateQuota d t)
      (fun k => d2FlowCandidateCapacity d k t) i
      (.node G low high children)) :
    let stage := d2FlowStage (d2FlowCandidateActive d t)
      (d2FlowCandidateRole d t) (d2FlowCandidateQuota d t)
      (h + 3) i (.node G low high children)
    let left := low + d2FlowCandidateQuota d t i
      (d2FlowCandidateRole d t i) / 2
    StaticHolesFit left
      (d2FlowNodeStaticHolesClamped 0 (8192 * 8 ^ (h + 1)) left 0
        (fun k => d2FlowTreeChild (d2FlowTreeChild stage 0) k))
      (8 * (8192 * 8 ^ (h + 1))) := by
  let stage := d2FlowStage (d2FlowCandidateActive d t)
    (d2FlowCandidateRole d t) (d2FlowCandidateQuota d t)
    (h + 3) i (.node G low high children)
  let left := low + d2FlowCandidateQuota d t i
    (d2FlowCandidateRole d t i) / 2
  let grandchildren : Fin 8 -> D2FlowTree (h + 1) :=
    fun k => d2FlowStage (d2FlowCandidateActive d t)
      (d2FlowCandidateRole d t) (d2FlowCandidateQuota d t)
      (h + 1) (i + 2) (d2FlowTreeChild (children 0) k)
  have hnext := d2FlowCandidateActive_adjacent_false_of_active hparent
  have hdeep (k : Fin 8) :
      d2FlowTreeChild (d2FlowTreeChild stage 0) k = grandchildren k := by
    have heq := d2FlowStage_regular_child_grandchild_stage
      (active := d2FlowCandidateActive d t)
      (role := d2FlowCandidateRole d t)
      (quota := d2FlowCandidateQuota d t) (h := h + 1) (i := i)
      (G := G) (low := low) (high := high) children
      hparent hparentRole hnext 0 k
    simpa [stage, grandchildren] using heq
  have hrootBound := d2FlowStage_active_ordinary_fronts_le_width_of_capacity
    (scale := 8192) (h := h + 2) (width := 8192 * 8 ^ (h + 1))
    (i := i) (G := G) (low := low) (high := high)
    (active := d2FlowCandidateActive d t)
    (role := d2FlowCandidateRole d t)
    (quota := d2FlowCandidateQuota d t)
    (cap := fun k => d2FlowCandidateCapacity d k t)
    children hinputs hparent hparentRole
    (d2FlowCandidateCapacity_le_256_grandchild_slot hd ht htf
      hgrandchild hdepth)
  have hsupport := d2FlowCandidateStage_regular_cut_endpoint_support
    children hparent hparentRole hinputs
  have hcut : d2FlowCutChild
      (d2FlowPosition (fun j => d2FlowTreeRootDeficit (children j)) 0)
      (d2FlowTreeRootDeficit (children 0)) left
      (d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - high -
        d2FlowCandidateQuota d t i (d2FlowCandidateRole d t i) / 2) =
      (left, left, 0) := by
    simpa [left] using hsupport 0
  have hcutLeft :
      (d2FlowCutChild
        (d2FlowPosition (fun j => d2FlowTreeRootDeficit (children j)) 0)
        (d2FlowTreeRootDeficit (children 0)) left
        (d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - high -
          d2FlowCandidateQuota d t i (d2FlowCandidateRole d t i) / 2)).2.1 =
        left := by rw [hcut]
  have hcutSmall : left <= 8192 * 8 ^ (h + 1) := by
    exact hrootBound.1
  have hgrandchildrenInv : forall k, d2FlowTreeInv 8192 (grandchildren k) := by
    intro k
    exact d2FlowStage_preserves_inv_of_inputs
      (d2FlowTreeChild (children 0) k)
      (d2FlowTreeInv_grandchild (.node G low high children) htree 0 k)
      (d2FlowStageInvInputs_grandchild (.node G low high children)
        hinputs 0 k)
  have hfirstEndpoint := d2FlowCandidateStage_regular_first_cut_le_grandchild_left_front
    children hd ht hparent hparentRole hgrandchild hgrandchildRole hinputs
  have hfirstStage : d2FlowTreeChild (d2FlowTreeChild stage 0) 0 =
      grandchildren 0 := hdeep 0
  have hfirst : d2FlowTreeRootDeficit (grandchildren 0) <
      8192 * 8 ^ (h + 1) ->
      left <= (d2FlowTreeRootData (grandchildren 0)).2.1 := by
    intro _
    have hb : left <= (d2FlowTreeRootData
        (d2FlowTreeChild (d2FlowTreeChild stage 0) 0)).2.1 := by
      have hb' := hfirstEndpoint
      rw [hcutLeft] at hb'
      simpa [left, stage] using hb'
    simpa [hfirstStage, grandchildren] using hb
  have hfit := d2FlowNodeStaticHolesClamped_fit_of_endpoint_front_bounds
    (scale := 8192) (h := h + 1) (width := 8192 * 8 ^ (h + 1))
    (left := left) (right := 0) grandchildren rfl hgrandchildrenInv
    (by omega) hcutSmall (by omega) hfirst
    (by intro; exact Nat.zero_le _)
  have hchildren : (fun k => d2FlowTreeChild (d2FlowTreeChild stage 0) k) =
      grandchildren := by
    funext k
    exact hdeep k
  simpa [stage, left, hchildren] using hfit

/-- Symmetric endpoint case: the last child overwritten by an ordinary parent
has a fitted clamped root interval when its ordinary grandchild is active. -/
theorem d2FlowCandidateStage_last_child_clamped_fit_of_ordinary_grandchild
    {d i t h G low high : Nat} (children : Fin 8 -> D2FlowTree (h + 2))
    (hd : 7 <= d) (ht : 2 <= t)
    (hparent : d2FlowCandidateActive d t i = true)
    (hparentRole : d2FlowCandidateRole d t i = .topRise \/
      d2FlowCandidateRole d t i = .mid \/
      d2FlowCandidateRole d t i = .botDesc)
    (hgrandchild : d2FlowCandidateActive d t (i + 2) = true)
    (hgrandchildRole : d2FlowCandidateRole d t (i + 2) = .topRise \/
      d2FlowCandidateRole d t (i + 2) = .mid \/
      d2FlowCandidateRole d t (i + 2) = .botDesc)
    (htf : t < tfD2 d) (hdepth : d = i + h + 3)
    (htree : d2FlowTreeInv 8192 (.node G low high children))
    (hinputs : d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d t) (d2FlowCandidateRole d t)
      (d2FlowCandidateQuota d t)
      (fun k => d2FlowCandidateCapacity d k t) i
      (.node G low high children)) :
    let stage := d2FlowStage (d2FlowCandidateActive d t)
      (d2FlowCandidateRole d t) (d2FlowCandidateQuota d t)
      (h + 3) i (.node G low high children)
    let right := high + d2FlowCandidateQuota d t i
      (d2FlowCandidateRole d t i) / 2
    StaticHolesFit 0
      (d2FlowNodeStaticHolesClamped 0 (8192 * 8 ^ (h + 1)) 0 right
        (fun k => d2FlowTreeChild (d2FlowTreeChild stage 7) k))
      (8 * (8192 * 8 ^ (h + 1)) - right) := by
  let stage := d2FlowStage (d2FlowCandidateActive d t)
    (d2FlowCandidateRole d t) (d2FlowCandidateQuota d t)
    (h + 3) i (.node G low high children)
  let right := high + d2FlowCandidateQuota d t i
    (d2FlowCandidateRole d t i) / 2
  let grandchildren : Fin 8 -> D2FlowTree (h + 1) :=
    fun k => d2FlowStage (d2FlowCandidateActive d t)
      (d2FlowCandidateRole d t) (d2FlowCandidateQuota d t)
      (h + 1) (i + 2) (d2FlowTreeChild (children 7) k)
  have hnext := d2FlowCandidateActive_adjacent_false_of_active hparent
  have hdeep (k : Fin 8) :
      d2FlowTreeChild (d2FlowTreeChild stage 7) k = grandchildren k := by
    have heq := d2FlowStage_regular_child_grandchild_stage
      (active := d2FlowCandidateActive d t)
      (role := d2FlowCandidateRole d t)
      (quota := d2FlowCandidateQuota d t) (h := h + 1) (i := i)
      (G := G) (low := low) (high := high) children
      hparent hparentRole hnext 7 k
    simpa [stage, grandchildren] using heq
  have hrootBound := d2FlowStage_active_ordinary_fronts_le_width_of_capacity
    (scale := 8192) (h := h + 2) (width := 8192 * 8 ^ (h + 1))
    (i := i) (G := G) (low := low) (high := high)
    (active := d2FlowCandidateActive d t)
    (role := d2FlowCandidateRole d t)
    (quota := d2FlowCandidateQuota d t)
    (cap := fun k => d2FlowCandidateCapacity d k t)
    children hinputs hparent hparentRole
    (d2FlowCandidateCapacity_le_256_grandchild_slot hd ht htf
      hgrandchild hdepth)
  have hsupport := d2FlowCandidateStage_regular_cut_endpoint_support
    children hparent hparentRole hinputs
  have hcut : d2FlowCutChild
      (d2FlowPosition (fun j => d2FlowTreeRootDeficit (children j)) 7)
      (d2FlowTreeRootDeficit (children 7))
      (low + d2FlowCandidateQuota d t i
        (d2FlowCandidateRole d t i) / 2)
      (d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - high -
        d2FlowCandidateQuota d t i (d2FlowCandidateRole d t i) / 2) =
      (right, 0, right) := by
    simpa [right] using hsupport 7
  have hcutRight :
      (d2FlowCutChild
        (d2FlowPosition (fun j => d2FlowTreeRootDeficit (children j)) 7)
        (d2FlowTreeRootDeficit (children 7))
        (low + d2FlowCandidateQuota d t i
          (d2FlowCandidateRole d t i) / 2)
        (d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - high -
          d2FlowCandidateQuota d t i (d2FlowCandidateRole d t i) / 2)).2.2 =
        right := by rw [hcut]
  have hcutSmall : right <= 8192 * 8 ^ (h + 1) := hrootBound.2
  have hgrandchildrenInv : forall k, d2FlowTreeInv 8192 (grandchildren k) := by
    intro k
    exact d2FlowStage_preserves_inv_of_inputs
      (d2FlowTreeChild (children 7) k)
      (d2FlowTreeInv_grandchild (.node G low high children) htree 7 k)
      (d2FlowStageInvInputs_grandchild (.node G low high children)
        hinputs 7 k)
  have hlastEndpoint :=
    d2FlowCandidateStage_regular_last_cut_le_grandchild_right_front
      children hd ht hparent hparentRole hgrandchild hgrandchildRole htree hinputs
  have hlastStage : d2FlowTreeChild (d2FlowTreeChild stage 7) 7 =
      grandchildren 7 := hdeep 7
  have hlast : d2FlowTreeRootDeficit (grandchildren 7) <
      8192 * 8 ^ (h + 1) ->
      right <= (d2FlowTreeRootData (grandchildren 7)).2.2 := by
    intro _
    have hb : right <= (d2FlowTreeRootData
        (d2FlowTreeChild (d2FlowTreeChild stage 7) 7)).2.2 := by
      have hb' := hlastEndpoint
      rw [hcutRight] at hb'
      simpa [right, stage] using hb'
    simpa [hlastStage, grandchildren] using hb
  have hfit := d2FlowNodeStaticHolesClamped_fit_of_endpoint_front_bounds
    (scale := 8192) (h := h + 1) (width := 8192 * 8 ^ (h + 1))
    (left := 0) (right := right) grandchildren rfl hgrandchildrenInv
    (by omega) (by omega) hcutSmall
    (by intro; exact Nat.zero_le _) hlast
  have hchildren : (fun k => d2FlowTreeChild (d2FlowTreeChild stage 7) k) =
      grandchildren := by
    funext k
    exact hdeep k
  simpa [stage, right, hchildren] using hfit

/-- An ordinary active parent's six interior children receive zero root cuts,
so their post-stage clamped root fit is automatic from the native slots. -/
theorem d2FlowCandidateStage_inner_child_clamped_fit
    {d i t h G low high : Nat} (children : Fin 8 -> D2FlowTree (h + 2))
    (j : Fin 8) (hj0 : j.val ≠ 0) (hj7 : j.val ≠ 7)
    (hparent : d2FlowCandidateActive d t i = true)
    (hparentRole : d2FlowCandidateRole d t i = .topRise \/
      d2FlowCandidateRole d t i = .mid \/
      d2FlowCandidateRole d t i = .botDesc)
    (htree : d2FlowTreeInv 8192 (.node G low high children))
    (hinputs : d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d t) (d2FlowCandidateRole d t)
      (d2FlowCandidateQuota d t)
      (fun k => d2FlowCandidateCapacity d k t) i
      (.node G low high children)) :
    let stage := d2FlowStage (d2FlowCandidateActive d t)
      (d2FlowCandidateRole d t) (d2FlowCandidateQuota d t)
      (h + 3) i (.node G low high children)
    StaticHolesFit 0
      (d2FlowNodeStaticHolesClamped 0 (8192 * 8 ^ (h + 1)) 0 0
        (fun k => d2FlowTreeChild (d2FlowTreeChild stage j) k))
      (8 * (8192 * 8 ^ (h + 1))) := by
  let stage := d2FlowStage (d2FlowCandidateActive d t)
    (d2FlowCandidateRole d t) (d2FlowCandidateQuota d t)
    (h + 3) i (.node G low high children)
  let grandchildren : Fin 8 -> D2FlowTree (h + 1) :=
    fun k => d2FlowStage (d2FlowCandidateActive d t)
      (d2FlowCandidateRole d t) (d2FlowCandidateQuota d t)
      (h + 1) (i + 2) (d2FlowTreeChild (children j) k)
  have hnext := d2FlowCandidateActive_adjacent_false_of_active hparent
  have hdeep (k : Fin 8) :
      d2FlowTreeChild (d2FlowTreeChild stage j) k = grandchildren k := by
    have heq := d2FlowStage_regular_child_grandchild_stage
      (active := d2FlowCandidateActive d t)
      (role := d2FlowCandidateRole d t)
      (quota := d2FlowCandidateQuota d t) (h := h + 1) (i := i)
      (G := G) (low := low) (high := high) children
      hparent hparentRole hnext j k
    simpa [stage, grandchildren] using heq
  have hsupport := d2FlowCandidateStage_regular_cut_endpoint_support
    children hparent hparentRole hinputs
  have hcutZero :
      d2FlowCutChild
        (d2FlowPosition (fun k => d2FlowTreeRootDeficit (children k)) j)
        (d2FlowTreeRootDeficit (children j))
        (low + d2FlowCandidateQuota d t i
          (d2FlowCandidateRole d t i) / 2)
        (d2FlowTotal (fun k => d2FlowTreeRootDeficit (children k)) - high -
          d2FlowCandidateQuota d t i (d2FlowCandidateRole d t i) / 2) =
      (0, 0, 0) := by
    have hjne : j ≠ (0 : Fin 8) := by
      intro heq
      apply hj0
      simpa using congrArg Fin.val heq
    simpa [hjne, hj7] using hsupport j
  have hgrandchildrenInv : forall k, d2FlowTreeInv 8192 (grandchildren k) := by
    intro k
    exact d2FlowStage_preserves_inv_of_inputs
      (d2FlowTreeChild (children j) k)
      (d2FlowTreeInv_grandchild (.node G low high children) htree j k)
      (d2FlowStageInvInputs_grandchild (.node G low high children)
        hinputs j k)
  have hfit := d2FlowNodeStaticHolesClamped_fit_of_endpoint_front_bounds
    (scale := 8192) (h := h + 1) (width := 8192 * 8 ^ (h + 1))
    (left := 0) (right := 0) grandchildren rfl hgrandchildrenInv
    (by omega) (by omega) (by omega)
    (by intro; exact Nat.zero_le _) (by intro; exact Nat.zero_le _)
  have hchildren : (fun k => d2FlowTreeChild (d2FlowTreeChild stage j) k) =
      grandchildren := by
    funext k
    exact hdeep k
  simpa [stage, hchildren] using hfit

/-- If an ordinary parent has an inactive level-two descendant and every
grandchild below each immediate child is saturated, then every overwritten
child has clamped root fit. This is the local geometry needed at botDesc. -/
theorem d2FlowCandidateStage_children_clamped_fit_of_saturated_grandchildren
    {d i t h G low high : Nat} (children : Fin 8 -> D2FlowTree (h + 2))
    (hparent : d2FlowCandidateActive d t i = true)
    (hparentRole : d2FlowCandidateRole d t i = .topRise \/
      d2FlowCandidateRole d t i = .mid \/
      d2FlowCandidateRole d t i = .botDesc)
    (hinactive2 : d2FlowCandidateActive d t (i + 2) = false)
    (htree : d2FlowTreeInv 8192 (.node G low high children))
    (hinputs : d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d t) (d2FlowCandidateRole d t)
      (d2FlowCandidateQuota d t)
      (fun k => d2FlowCandidateCapacity d k t) i
      (.node G low high children))
    (hsaturated : forall j k,
      d2FlowTreeRootDeficit (d2FlowTreeChild (children j) k) =
        8192 * 8 ^ (h + 1)) :
    forall j : Fin 8,
      let stage := d2FlowStage (d2FlowCandidateActive d t)
        (d2FlowCandidateRole d t) (d2FlowCandidateQuota d t)
        (h + 3) i (.node G low high children)
      let cut := d2FlowCutChild
        (d2FlowPosition (fun k => d2FlowTreeRootDeficit (children k)) j)
        (d2FlowTreeRootDeficit (children j))
        (low + d2FlowCandidateQuota d t i
          (d2FlowCandidateRole d t i) / 2)
        (d2FlowTotal (fun k => d2FlowTreeRootDeficit (children k)) - high -
          d2FlowCandidateQuota d t i (d2FlowCandidateRole d t i) / 2)
      StaticHolesFit cut.2.1
        (d2FlowNodeStaticHolesClamped 0 (8192 * 8 ^ (h + 1))
          cut.2.1 cut.2.2
          (fun k => d2FlowTreeChild (d2FlowTreeChild stage j) k))
        (8 * (8192 * 8 ^ (h + 1)) - cut.2.2) := by
  let stage := d2FlowStage (d2FlowCandidateActive d t)
    (d2FlowCandidateRole d t) (d2FlowCandidateQuota d t)
    (h + 3) i (.node G low high children)
  let width := 8192 * 8 ^ (h + 1)
  let grandchildren : Fin 8 -> Fin 8 -> D2FlowTree (h + 1) := fun j k =>
    d2FlowStage (d2FlowCandidateActive d t)
      (d2FlowCandidateRole d t) (d2FlowCandidateQuota d t)
      (h + 1) (i + 2) (d2FlowTreeChild (children j) k)
  have hnext := d2FlowCandidateActive_adjacent_false_of_active hparent
  have hdeep (j k : Fin 8) :
      d2FlowTreeChild (d2FlowTreeChild stage j) k = grandchildren j k := by
    have heq := d2FlowStage_regular_child_grandchild_stage
      (active := d2FlowCandidateActive d t)
      (role := d2FlowCandidateRole d t)
      (quota := d2FlowCandidateQuota d t) (h := h + 1) (i := i)
      (G := G) (low := low) (high := high) children
      hparent hparentRole hnext j k
    simpa [stage, grandchildren] using heq
  have hinvChildren : forall j, d2FlowTreeInv 8192 (children j) := by
    have hx := htree
    simp only [d2FlowTreeInv] at hx
    exact hx.2.2.2
  have hcore := d2FlowStageInvInputs_ordinary_cut_core
    children hinputs hparent hparentRole
  have hfrontsDisjoint :
      low + d2FlowCandidateQuota d t i
          (d2FlowCandidateRole d t i) / 2 <=
        d2FlowTotal (fun k => d2FlowTreeRootDeficit (children k)) - high -
          d2FlowCandidateQuota d t i (d2FlowCandidateRole d t i) / 2 := by
    have halloc := hcore.2.2.2.1
    have htotal : G <=
        d2FlowTotal (fun k => d2FlowTreeRootDeficit (children k)) := htree.2.1
    have heven := hcore.2.2.2.2
    have hquotaEven : d2FlowCandidateQuota d t i
        (d2FlowCandidateRole d t i) = 2 *
          (d2FlowCandidateQuota d t i (d2FlowCandidateRole d t i) / 2) := by
      omega
    omega
  have hwidth : 8192 * 8 ^ (h + 2) = 8 * width := by
    simp [width, Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  intro j
  let cut := d2FlowCutChild
    (d2FlowPosition (fun k => d2FlowTreeRootDeficit (children k)) j)
    (d2FlowTreeRootDeficit (children j))
    (low + d2FlowCandidateQuota d t i (d2FlowCandidateRole d t i) / 2)
    (d2FlowTotal (fun k => d2FlowTreeRootDeficit (children k)) - high -
      d2FlowCandidateQuota d t i (d2FlowCandidateRole d t i) / 2)
  have hchildSize : d2FlowTreeRootDeficit (children j) <= 8 * width := by
    have hnative := d2FlowTreeInv_root_native_bound (children j) (hinvChildren j)
    rw [hwidth] at hnative
    exact hnative
  have hcutBound := d2FlowCutChild_le_native
    (pos := d2FlowPosition (fun k => d2FlowTreeRootDeficit (children k)) j)
    (size := d2FlowTreeRootDeficit (children j))
    (left := low + d2FlowCandidateQuota d t i
      (d2FlowCandidateRole d t i) / 2)
    (right := d2FlowTotal (fun k => d2FlowTreeRootDeficit (children k)) - high -
      d2FlowCandidateQuota d t i (d2FlowCandidateRole d t i) / 2)
    (native := 8 * width) hchildSize hfrontsDisjoint
  have hparentInterval : cut.2.1 + cut.2.2 <= 8 * width := by
    have hsum : cut.1 = cut.2.1 + cut.2.2 := by
      simp [cut, d2FlowCutChild]
    rw [← hsum]
    exact hcutBound
  have hsatStage : forall k, d2FlowTreeRootDeficit (grandchildren j k) = width := by
    intro k
    change d2FlowTreeRootDeficit
      (d2FlowStage (d2FlowCandidateActive d t)
        (d2FlowCandidateRole d t) (d2FlowCandidateQuota d t)
        (h + 1) (i + 2) (d2FlowTreeChild (children j) k)) = width
    rw [d2FlowStage_root_deficit_of_inactive
      (d2FlowTreeChild (children j) k) hinactive2]
    exact hsaturated j k
  have hfit := d2FlowNodeStaticHolesClamped_fit_of_saturated_children_in_parent
    (base := 0) (width := width) (low := cut.2.1) (high := cut.2.2)
    (grandchildren j) hparentInterval hsatStage
  have hchildren :
      (fun k => d2FlowTreeChild (d2FlowTreeChild stage j) k) =
        grandchildren j := by
    funext k
    exact hdeep j k
  simpa [stage, width, cut, hchildren] using hfit

/-! The geometric fit itself has a natural recursive invariant in the clamped
representation. The transition below isolates the sole exceptional local
provider (botRise); the ordinary, inactive, and topDesc cases are discharged
from existing local fit lemmas. -/

def d2FlowTreeClampedStaticFits (scale : Nat) : {h : Nat} ->
    D2FlowTree h -> Prop
  | 0, .leaf _ _ _ => True
  | h + 1, .node _ low high children =>
      StaticHolesFit low
        (d2FlowNodeStaticHolesClamped 0 (scale * 8 ^ h) low high children)
        (8 * (scale * 8 ^ h) - high) /\
      forall j, d2FlowTreeClampedStaticFits scale (children j)

theorem d2FlowTreeClampedStaticFits_of_staticFits
    {scale h : Nat} {tree : D2FlowTree h}
    (hfit : d2FlowTreeStaticFits scale tree)
    (hinv : d2FlowTreeInv scale tree) :
    d2FlowTreeClampedStaticFits scale tree := by
  induction tree with
  | leaf G low high => trivial
  | node G low high children ih =>
      simp only [d2FlowTreeStaticFits] at hfit
      simp only [d2FlowTreeClampedStaticFits]
      constructor
      · have hinvChildren : forall j, d2FlowTreeInv scale (children j) := by
          have hx := hinv
          simp only [d2FlowTreeInv] at hx
          exact hx.2.2.2
        simpa using d2FlowNodeStaticHolesClamped_fit_of_static_fit
          (base := 0) (width := scale * 8 ^ _) (left := low) (right := high)
          children rfl hinvChildren (by simpa using hfit.1)
      · intro j
        have hinvChild : d2FlowTreeInv scale (children j) := by
          have hx := hinv
          simp only [d2FlowTreeInv] at hx
          exact hx.2.2.2 j
        exact ih j (hfit.2 j) hinvChild

theorem d2FlowTreeInitial_clamped_static_fits (scale h : Nat) :
    d2FlowTreeClampedStaticFits scale (d2FlowTreeInitial scale h) := by
  exact d2FlowTreeClampedStaticFits_of_staticFits
    (d2FlowTreeInitial_static_fits scale h) (d2FlowTreeInitial_inv scale h)

end Chvatal.D2Reserve
