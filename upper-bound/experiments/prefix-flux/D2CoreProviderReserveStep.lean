import D2StrongFlowCoreInputs
import D2RunTwoVisitReserve
import D2PathNativePreservation
import D2StrongAffineChild
import D2TerminalScheduleFacts

namespace Chvatal.D2Reserve

set_option linter.unusedVariables false
set_option maxHeartbeats 12000000
set_option maxRecDepth 4096

theorem d2FlowTreeRunWithParentOverwrites_topDesc_child_zero
    {h i n G low high : Nat} (initial : D2FlowTree (h + 1))
    (children : Fin 8 -> D2FlowTree h)
    (active : Nat -> Nat -> Bool) (role : Nat -> Nat -> D2Role)
    (quota : Nat -> Nat -> D2Role -> Nat)
    (overwrite : Nat -> Nat × Nat × Nat) (port : Fin 8)
    (hnode : d2FlowTreeRunWithParentOverwrites initial i active role quota
      overwrite n = .node G low high children)
    (ha : active n i = true) (hr : role n i = .topDesc) :
    d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowTreeRunWithParentOverwrites initial i active role quota
          overwrite (n + 1)) port) = 0 := by
  have hoverwrite :
      d2FlowTreeChildOverwrite
        (fun k => d2FlowTreeRunWithParentOverwrites initial i active role
          quota overwrite k) (i := i) active role quota port n = (0, 0, 0) := by
    simp only [d2FlowTreeChildOverwrite]
    rw [hnode]
    exact d2FlowStage_topDesc_child_rootdata children ha hr port
  rw [d2FlowTreeRun_child_as_history]
  rw [show n + 1 = Nat.succ n by rfl, d2FlowTreeRunWithParentOverwrites]
  rw [hoverwrite]
  cases h with
  | zero =>
      cases hstep : d2FlowStage (active n) (role n) (quota n) 0 (i + 1)
          (d2FlowTreeRunWithParentOverwrites (d2FlowTreeChild initial port)
            (i + 1) active role quota
            (d2FlowTreeChildOverwrite
              (fun k => d2FlowTreeRunWithParentOverwrites initial i active role
                quota overwrite k) active role quota port) n) with
      | leaf G' low' high' =>
          simp [d2FlowTreeSetRoot, d2FlowTreeRootDeficit]
  | succ h =>
      cases hstep : d2FlowStage (active n) (role n) (quota n)
          (h + 1) (i + 1)
          (d2FlowTreeRunWithParentOverwrites (d2FlowTreeChild initial port)
            (i + 1) active role quota
            (d2FlowTreeChildOverwrite
              (fun k => d2FlowTreeRunWithParentOverwrites initial i active role
                quota overwrite k) active role quota port) n) with
      | node G' low' high' grandchildren =>
          simp [d2FlowTreeSetRoot, d2FlowTreeRootDeficit]

private theorem ceilParity_succ_time_upper
    {m n s t : Nat} (hpar : s % 2 ≠ t % 2)
    (hmn : m <= n) (hnm : n <= m + 1) :
    ceilParity n t <= ceilParity m s + 1 := by
  unfold ceilParity
  by_cases hs : m % 2 = s % 2 <;>
    by_cases ht : n % 2 = t % 2 <;> simp [hs, ht] <;> omega

/-- If a child is currently on the rising top frontier, its active parent at
the preceding stage was exactly top-descending. Hence that parent's reset is
the structural source of the child's required zero deficit. -/
theorem d2ScheduleRole_parent_of_active_topRise
    {d tf i t : Nat} (ht : 3 <= t) (hi : 1 <= i)
    (ha : active d tf i t)
    (hr : d2ScheduleRole d i t = .topRise) :
    d2ScheduleRole d (i - 1) (t - 1) = .topDesc := by
  classical
  have hnotTop : ¬ (i = alpha d t /\ alpha d t < alpha d (t + 1)) := by
    intro h
    have : d2ScheduleRole d i t = .topDesc := by
      simp [d2ScheduleRole, h.1, h.2]
    rw [hr] at this
    cases this
  have hparent := active_parent_of_not_topDesc ht hi ha hnotTop
  have hfront := (active_iff_frontiers (d := d) (tf := tf)
    (i := i - 1) (t := t - 1) (by omega)).1 hparent
  have hAlphaLower : alpha d (t - 1) <= i - 1 := hfront.2.1
  have hiAlpha : i = alpha d t := by
    unfold d2ScheduleRole at hr
    by_cases htop : i = alpha d t
    · rw [if_pos htop] at hr
      by_cases hmove : alpha d t < alpha d (t + 1)
      · simp [hmove] at hr
      · simp [hmove] at hr
        exact htop
    · by_cases hbot : i = omega t
      · rw [if_neg htop, if_pos hbot] at hr
        split_ifs at hr
      · rw [if_neg htop, if_neg hbot] at hr
        simp at hr
  have hstarMono := alphaStar_mono (d := d) (by omega : t - 1 <= t)
  have hstarStep := alphaStar_succ_le (d := d) (t := t - 1)
  have hstarStep' : alphaStar d t <= alphaStar d (t - 1) + 1 := by
    rw [show t - 1 + 1 = t by omega] at hstarStep
    exact hstarStep
  have hAlphaUpper : alpha d t <= alpha d (t - 1) + 1 := by
    have hprev0 : t - 1 ≠ 0 := by omega
    have hprev1 : t - 1 ≠ 1 := by omega
    have hnow0 : t ≠ 0 := by omega
    have hnow1 : t ≠ 1 := by omega
    rw [show alpha d (t - 1) =
          ceilParity (alphaStar d (t - 1)) (t - 1) by
        simp [alpha, hprev0, hprev1],
      show alpha d t = ceilParity (alphaStar d t) t by
        simp [alpha, hnow0, hnow1]]
    exact ceilParity_succ_time_upper (by omega) hstarMono hstarStep'
  have hAlphaEq : alpha d (t - 1) = i - 1 := by omega
  have hAlphaMove : alpha d (t - 1) < alpha d t := by omega
  have hparentTop : d2ScheduleRole d (i - 1) (t - 1) = .topDesc := by
    unfold d2ScheduleRole
    rw [if_pos hAlphaEq.symm, show (t - 1) + 1 = t by omega]
    simp [hAlphaMove]
  exact hparentTop

/-- An ordinary predecessor's affine core inputs imply both endpoint reserves
at the sender's next same-level visit in the actual candidate run. This
isolates the non-`botRise` branch of the simultaneous reserve induction. -/
theorem d2FlowCandidateRun_core_provider_endpoint_reserve_step
    {h i t G low high : Nat} (hd : 7 <= h + 1 + i)
    (ht : 4 <= t) (htf : t <= tfD2 (h + 1 + i))
    (path : D2FlowPath i) (children : Fin 8 -> D2FlowTree h)
    (hnode : d2FlowTreeAtPath i
      (d2FlowCandidateRun (h + 1 + i)
        (d2FlowTreeInitial 8192 (h + 1 + i)) (t - 2)) path =
      .node G low high children)
    (hcurrent : active (h + 1 + i) (tfD2 (h + 1 + i)) i t)
    (hrole : d2ScheduleRole (h + 1 + i) i t = .topRise \/
      d2ScheduleRole (h + 1 + i) i t = .mid \/
      d2ScheduleRole (h + 1 + i) i t = .botDesc)
    (hpriorRole : d2FlowCandidateRole (h + 1 + i) (t - 2) i = .topRise \/
      d2FlowCandidateRole (h + 1 + i) (t - 2) i = .mid \/
      d2FlowCandidateRole (h + 1 + i) (t - 2) i = .botDesc)
    (hcorePrev : d2FlowStageAffineCoreInputs
      (fun k => d2FlowCandidateActive (h + 1 + i) (t - 2) k)
      (fun k => d2FlowCandidateRole (h + 1 + i) (t - 2) k)
      (fun k => d2FlowCandidateCapacity (h + 1 + i) k (t - 2)) 0
      (d2FlowCandidateRun (h + 1 + i)
        (d2FlowTreeInitial 8192 (h + 1 + i)) (t - 2))) :
    d2FlowCandidateCapacity (h + 1 + i) i t <=
      128 * d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowTreeAtPath i
            (d2FlowCandidateRun (h + 1 + i)
              (d2FlowTreeInitial 8192 (h + 1 + i)) t) path) 0) /\
    d2FlowCandidateCapacity (h + 1 + i) i t <=
      128 * d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowTreeAtPath i
            (d2FlowCandidateRun (h + 1 + i)
              (d2FlowTreeInitial 8192 (h + 1 + i)) t) path) 7) := by
  classical
  let d := h + 1 + i
  have hprevRoles := active_regular_prev_two_role_cases_le hd ht htf hcurrent hrole
  have hprevActive := hprevRoles.1
  have htPrev : 0 < t - 2 := by omega
  have hprevActiveBool : d2FlowCandidateActive d (t - 2) i = true := by
    rw [d2FlowCandidateActive_matches_schedule (d := d) (i := i)
      (t := t - 2) (by omega)]
    exact decide_eq_true hprevActive
  have hprevRoleSchedule : d2ScheduleRole d i (t - 2) = .topRise \/
      d2ScheduleRole d i (t - 2) = .mid \/
      d2ScheduleRole d i (t - 2) = .botDesc := by
    rw [d2FlowCandidateRole_matches_schedule (d := d) (t := t - 2)
      (i := i) htPrev] at hpriorRole
    exact hpriorRole
  have hprevAffine := d2FlowCandidateRun_core_provider_affine_atPath
    (h := h + 1) (i := i) (t := t - 2) hd (by omega) path hcorePrev
  rw [hnode] at hprevAffine
  have hfields := d2FlowStageAffineInputs_ordinary_fields children
    hprevAffine hprevActiveBool hpriorRole
  rcases hfields with
    ⟨hbalance, halloc, heven, hdeficit, hquota, hleft, hright, hprofileCap⟩
  have htotalSize := d2FlowSize_le_total
    (fun j => d2FlowTreeRootDeficit (children j)) 0
  have hcapTotal : d2FlowCandidateCapacity d i (t - 2) <=
      128 * d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) :=
    le_trans hleft (Nat.mul_le_mul_left 128 htotalSize)
  have hcapTotal' : d2FlowCandidateCapacity (h + 1 + i) i (t - 2) <=
      128 * d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) := by
    simpa [d] using hcapTotal
  have hcover : G <= d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) := by
    nlinarith [hdeficit, hcapTotal']
  have hcapacityScale :
      2 * t + 4 <= 13 + 3 * d + 3 * i := by
    have hexp := d2FlowCandidateCapacityExponent_ge_twenty hd hcurrent
    simp [d2FlowCandidateCapacityExponent] at hexp
    omega
  have hcap := d2FlowCandidateCapacity_two_stage_ratio
    (d := d) (i := i) (t := t) (by omega) hcapacityScale
  have hquotaLowerSchedule := d2FlowCandidateQuota_lower_ordinary
    hd hprevActive hprevRoleSchedule
  have hroleMatches := d2FlowCandidateRole_matches_schedule
    (d := d) (t := t - 2) (i := i) htPrev
  have hquotaLower : 15 * d2FlowCandidateCapacity d i (t - 2) <=
      4096 * d2FlowCandidateQuota d (t - 2) i
        (d2FlowCandidateRole d (t - 2) i) := by
    rw [hroleMatches]
    exact hquotaLowerSchedule
  have hreserve := d2FlowCandidateRun_path_endpoint_reserve_of_prior_sender
    (h := h) (i := i) (t := t) path ht hcurrent hprevActiveBool hpriorRole
    children hnode hbalance hcover hdeficit hquota halloc heven hleft hright
    hcap hquotaLower
  exact hreserve

/-- A `botRise` predecessor supplies the same endpoint reserve directly from
the native child sizes: the exceptional window preserves both child roots,
and the current capacity is exactly 128 times that native size. -/
theorem d2FlowCandidateRun_botRise_endpoint_reserve_step
    {h i t : Nat} (hd : 7 <= h + 1 + i)
    (ht : 4 <= t) (htf : t <= tfD2 (h + 1 + i))
    (path : D2FlowPath i)
    (hcurrent : active (h + 1 + i) (tfD2 (h + 1 + i)) i t)
    (hprevRole : d2FlowCandidateRole (h + 1 + i) (t - 2) i = .botRise) :
    d2FlowCandidateCapacity (h + 1 + i) i t <=
      128 * d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowTreeAtPath i
            (d2FlowCandidateRun (h + 1 + i)
              (d2FlowTreeInitial 8192 (h + 1 + i)) t) path) 0) /\
    d2FlowCandidateCapacity (h + 1 + i) i t <=
      128 * d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowTreeAtPath i
            (d2FlowCandidateRun (h + 1 + i)
              (d2FlowTreeInitial 8192 (h + 1 + i)) t) path) 7) := by
  have hprevRoleSchedule :
      d2ScheduleRole (h + 1 + i) i (t - 2) = .botRise := by
    rw [d2FlowCandidateRole_matches_schedule (d := h + 1 + i)
      (t := t - 2) (i := i) (by omega)] at hprevRole
    exact hprevRole
  have hboundary := d2FlowCandidate_botRise_prev_two_boundary ht hprevRoleSchedule
  cases i with
  | zero => omega
  | succ i =>
    have hj : 1 <= i - 1 := by omega
    let j := i - 1
    have hji : j + 1 = i := by dsimp [j]; omega
    have hji2 : j + 2 = i + 1 := by omega
    have hji3 : j + 3 = i + 2 := by omega
    have htime : t = 3 * j + 2 := by dsimp [j]; omega
    have hwindow : 3 * j + 2 <= tfD2 (h + 1 + (i + 1)) := by
      calc
        3 * j + 2 = t := htime.symm
        _ <= tfD2 (h + 1 + (i + 1)) := htf
    have hpres := d2FlowCandidate_botRise_callback_window
      (d := h + 1 + (i + 1)) (j := j) (by omega) hj hwindow
    have hleft := d2FlowCandidateRun_path_child_root_preserved
      (h := h) (n := i) (t := 3 * j + 2) path 0 (by
        simpa [hji2, hji3] using hpres)
    have hright := d2FlowCandidateRun_path_child_root_preserved
      (h := h) (n := i) (t := 3 * j + 2) path 7 (by
        simpa [hji2, hji3] using hpres)
    have hcap := d2FlowCandidate_botRise_prev_two_native_capacity
      ht (by omega) hprevRoleSchedule
    have hcap' : d2FlowCandidateCapacity (h + 1 + (i + 1)) (i + 1) t =
        128 * (8192 * 8 ^ h) := by
      have hexp : h + 1 + (i + 1) - ((i + 1) + 1) = h := by omega
      simpa [hexp] using hcap
    rw [← htime] at hleft hright
    constructor
    · rw [hcap', hleft]
    · rw [hcap', hright]

/-- Full two-visit endpoint-reserve interface. The ordinary predecessor case
uses the affine core provider; the exceptional botRise case uses native
endpoint preservation. -/
theorem d2FlowCandidateRun_core_provider_endpoint_reserve_step_all_roles
    {h i t G low high : Nat} (hd : 7 <= h + 1 + i)
    (ht : 4 <= t) (htf : t <= tfD2 (h + 1 + i))
    (path : D2FlowPath i) (children : Fin 8 -> D2FlowTree h)
    (hnode : d2FlowTreeAtPath i
      (d2FlowCandidateRun (h + 1 + i)
        (d2FlowTreeInitial 8192 (h + 1 + i)) (t - 2)) path =
      .node G low high children)
    (hcurrent : active (h + 1 + i) (tfD2 (h + 1 + i)) i t)
    (hrole : d2ScheduleRole (h + 1 + i) i t = .topRise \/
      d2ScheduleRole (h + 1 + i) i t = .mid \/
      d2ScheduleRole (h + 1 + i) i t = .botDesc)
    (hcorePrev : d2FlowStageAffineCoreInputs
      (fun k => d2FlowCandidateActive (h + 1 + i) (t - 2) k)
      (fun k => d2FlowCandidateRole (h + 1 + i) (t - 2) k)
      (fun k => d2FlowCandidateCapacity (h + 1 + i) k (t - 2)) 0
      (d2FlowCandidateRun (h + 1 + i)
        (d2FlowTreeInitial 8192 (h + 1 + i)) (t - 2))) :
    d2FlowCandidateCapacity (h + 1 + i) i t <=
      128 * d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowTreeAtPath i
            (d2FlowCandidateRun (h + 1 + i)
              (d2FlowTreeInitial 8192 (h + 1 + i)) t) path) 0) /\
    d2FlowCandidateCapacity (h + 1 + i) i t <=
      128 * d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowTreeAtPath i
            (d2FlowCandidateRun (h + 1 + i)
              (d2FlowTreeInitial 8192 (h + 1 + i)) t) path) 7) := by
  have hprevRoles := active_regular_prev_two_role_cases_le
    hd ht htf hcurrent hrole
  have htPrev : 0 < t - 2 := by omega
  have hpriorRole : d2FlowCandidateRole (h + 1 + i) (t - 2) i = .topRise \/
      d2FlowCandidateRole (h + 1 + i) (t - 2) i = .mid \/
      d2FlowCandidateRole (h + 1 + i) (t - 2) i = .botDesc \/
      d2FlowCandidateRole (h + 1 + i) (t - 2) i = .botRise := by
    rw [d2FlowCandidateRole_matches_schedule (d := h + 1 + i)
      (t := t - 2) (i := i) htPrev]
    exact hprevRoles.2
  rcases hpriorRole with htop | hmid | htail
  · exact d2FlowCandidateRun_core_provider_endpoint_reserve_step
      hd ht htf path children hnode hcurrent hrole (Or.inl htop) hcorePrev
  · exact d2FlowCandidateRun_core_provider_endpoint_reserve_step
      hd ht htf path children hnode hcurrent hrole (Or.inr (Or.inl hmid)) hcorePrev
  · rcases htail with hdesc | hrise
    · exact d2FlowCandidateRun_core_provider_endpoint_reserve_step
        hd ht htf path children hnode hcurrent hrole
          (Or.inr (Or.inr hdesc)) hcorePrev
    · exact d2FlowCandidateRun_botRise_endpoint_reserve_step
        hd ht htf path hcurrent hrise

/-- A full-tree core provider at time t-2 supplies the endpoint reserves at
every active regular sender path at time t. This is the tree-wide induction
interface for the reserve component of the core provider. -/
theorem d2FlowCandidateRun_core_provider_endpoint_reserves_at_active_path
    {h i t : Nat} (hd : 7 <= h + 1 + i)
    (ht : 4 <= t) (htf : t <= tfD2 (h + 1 + i))
    (path : D2FlowPath i)
    (hcurrent : active (h + 1 + i) (tfD2 (h + 1 + i)) i t)
    (hrole : d2ScheduleRole (h + 1 + i) i t = .topRise \/
      d2ScheduleRole (h + 1 + i) i t = .mid \/
      d2ScheduleRole (h + 1 + i) i t = .botDesc)
    (hcorePrev : d2FlowStageAffineCoreInputs
      (fun k => d2FlowCandidateActive (h + 1 + i) (t - 2) k)
      (fun k => d2FlowCandidateRole (h + 1 + i) (t - 2) k)
      (fun k => d2FlowCandidateCapacity (h + 1 + i) k (t - 2)) 0
      (d2FlowCandidateRun (h + 1 + i)
        (d2FlowTreeInitial 8192 (h + 1 + i)) (t - 2))) :
    d2FlowCandidateCapacity (h + 1 + i) i t <=
      128 * d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowTreeAtPath i
            (d2FlowCandidateRun (h + 1 + i)
              (d2FlowTreeInitial 8192 (h + 1 + i)) t) path) 0) /\
    d2FlowCandidateCapacity (h + 1 + i) i t <=
      128 * d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowTreeAtPath i
            (d2FlowCandidateRun (h + 1 + i)
              (d2FlowTreeInitial 8192 (h + 1 + i)) t) path) 7) := by
  let d := h + 1 + i
  let before := d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) (t - 2)
  cases hnode : d2FlowTreeAtPath i before path with
  | node G low high children =>
      have hresult :=
        d2FlowCandidateRun_core_provider_endpoint_reserve_step_all_roles
          (h := h) (i := i) (t := t) hd ht htf path children hnode
          hcurrent hrole (by simpa [d, before] using hcorePrev)
      simpa [d] using hresult

/-- A full-tree core provider supplies the affine child profile after any
active ordinary parent update in the actual run. This is the one-step profile
component needed alongside the t-2 endpoint-reserve transition. -/
theorem d2FlowCandidateRun_core_provider_affine_child_at_active_parent
    {h i t G low high : Nat} (hd : 7 <= h + 1 + i)
    (ht : 0 < t) (path : D2FlowPath i)
    (hcurrent : active (h + 1 + i) (tfD2 (h + 1 + i)) i t)
    (hrole : d2ScheduleRole (h + 1 + i) i t = .topRise \/
      d2ScheduleRole (h + 1 + i) i t = .mid \/
      d2ScheduleRole (h + 1 + i) i t = .botDesc)
    (hcore : d2FlowStageAffineCoreInputs
      (fun k => d2FlowCandidateActive (h + 1 + i) t k)
      (fun k => d2FlowCandidateRole (h + 1 + i) t k)
      (fun k => d2FlowCandidateCapacity (h + 1 + i) k t) 0
      (d2FlowCandidateRun (h + 1 + i)
        (d2FlowTreeInitial 8192 (h + 1 + i)) t)) :
    ∀ j, 8192 * d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowTreeAtPath i
          (d2FlowCandidateRun (h + 1 + i)
            (d2FlowTreeInitial 8192 (h + 1 + i)) (t + 1)) path) j) + 7 <=
      15 * d2FlowCandidateCapacity (h + 1 + i) (i + 1) (t + 1) := by
  classical
  let d := h + 1 + i
  have hinputs := d2FlowCandidateRun_core_provider_affine_atPath
    (h := h + 1) (i := i) (t := t) (by simpa [d] using hd) ht path
    (by simpa [d] using hcore)
  cases hnode : d2FlowTreeAtPath i
      (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) t) path with
  | node G low high children =>
      have hinputsNode : d2FlowStageAffineInputs
          (d2FlowCandidateActive d t) (d2FlowCandidateRole d t)
          (d2FlowCandidateQuota d t) (fun k => d2FlowCandidateCapacity d k t)
          i (.node G low high children) := by
        simpa [d, hnode] using hinputs
      have hactive : d2FlowCandidateActive d t i = true := by
        rw [d2FlowCandidateActive_matches_schedule (d := d) (t := t)
          (i := i) (by omega)]
        exact decide_eq_true hcurrent
      have hroleCandidate : d2FlowCandidateRole d t i = .topRise \/
          d2FlowCandidateRole d t i = .mid \/
          d2FlowCandidateRole d t i = .botDesc := by
        rw [d2FlowCandidateRole_matches_schedule (d := d) (t := t)
          (i := i) (by omega)]
        exact hrole
      have hfields := d2FlowStageAffineInputs_ordinary_fields children
        hinputsNode hactive hroleCandidate
      rcases hfields with
        ⟨hbalance, halloc, heven, _hdeficit, _hquotaCap,
          hleft, hright, hprofileCap⟩
      let q := d2FlowCandidateQuota d t i (d2FlowCandidateRole d t i)
      have hquotaPos : 0 < q := by
        rcases hroleCandidate with htop | hmid | hbot
        · simp [q, htop, d2FlowCandidateQuota]
        · simp [q, hmid, d2FlowCandidateQuota]
        · simp [q, hbot, d2FlowCandidateQuota]
      let total := d2FlowTotal (fun j =>
        d2FlowTreeRootDeficit (children j))
      have hcover : G <= total := by
        dsimp [total]
        omega
      have hconserve : (total - G) + G = total :=
        Nat.sub_add_cancel hcover
      have hevenEq : q = 2 * (q / 2) := by
        dsimp [q]
        omega
      have hlow : low <= G := by omega
      have hhigh : high <= G := by omega
      have hcapacityScale :
          2 * t + 4 <= 13 + 3 * d + 3 * i := by
        have hactiveProp : active d (tfD2 d) i t := by
          have hdec : decide (active d (tfD2 d) i t) = true := by
            rw [← d2FlowCandidateActive_matches_schedule (d := d) (t := t)
              (i := i) (by omega)]
            exact hactive
          exact of_decide_eq_true hdec
        have hexp := d2FlowCandidateCapacityExponent_ge_twenty hd hactiveProp
        simp [d2FlowCandidateCapacityExponent] at hexp
        omega
      have hchildCap :
          d2FlowCandidateCapacity d (i + 1) (t + 1) =
            2 * d2FlowCandidateCapacity d i t :=
        d2FlowCandidateCapacity_succ_level_next_stage d i t hcapacityScale
      have hcpos : 0 < d2FlowCandidateCapacity d i t := by
        unfold d2FlowCandidateCapacity
        exact Nat.pow_pos (by decide)
      have hchild := d2FlowCandidateRun_path_parent_affine_child
        (h := h) (i := i) (t := t) path children hnode hactive
        hroleCandidate (allocation := total - G)
        (c := d2FlowCandidateCapacity d i t) hcpos
        hbalance hconserve (by simpa [q, total] using halloc) hevenEq
        hlow hhigh (by simpa [q] using hprofileCap) hleft hright hchildCap
      intro j
      simpa [d] using hchild j

/-- Transport a top-descending reset through an arbitrary actual path. The
selected parent may have any number of ancestors; its child root at the next
snapshot is still exactly zero. -/
theorem d2FlowCandidateRun_topDesc_parent_child_zero_at_path
    {h i t G low high : Nat} (path : D2FlowPath i)
    (children : Fin 8 -> D2FlowTree h)
    (hnode : d2FlowTreeAtPath i
      (d2FlowCandidateRun (h + 1 + i)
        (d2FlowTreeInitial 8192 (h + 1 + i)) t) path =
      .node G low high children)
    (ha : d2FlowCandidateActive (h + 1 + i) t i = true)
    (hr : d2FlowCandidateRole (h + 1 + i) t i = .topDesc)
    (port : Fin 8) :
    d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowTreeAtPath i
          (d2FlowCandidateRun (h + 1 + i)
            (d2FlowTreeInitial 8192 (h + 1 + i)) (t + 1)) path) port) = 0 := by
  classical
  let d := h + 1 + i
  let initial := d2FlowTreeInitial 8192 d
  let runActive := d2FlowCandidateRunActive d
  let runRole := d2FlowCandidateRunRole d
  let runQuota := d2FlowCandidateRunQuota d
  let overwrite := d2FlowCandidateRunOverwrite d initial
  let ctx := d2FlowTreePathContext i initial path 0
    runActive runRole runQuota overwrite
  have hlevel : ctx.level = i := by
    simpa [ctx, runActive, runRole, runQuota, overwrite, d, initial] using
      d2FlowTreePathContext_level initial path 0 runActive runRole runQuota
        overwrite
  have hpath (s : Nat) :
      d2FlowTreeAtPath i (d2FlowCandidateRun d initial s) path =
        d2FlowTreeRunWithParentOverwrites ctx.initial ctx.level
          runActive runRole runQuota ctx.overwrite s := by
    rw [d2FlowCandidateRun_path_as_history]
    exact d2FlowTreePathHistory_eq_context_run initial path 0
      (d2FlowCandidateRunActive d) (d2FlowCandidateRunRole d)
      (d2FlowCandidateRunQuota d) (d2FlowCandidateRunOverwrite d initial) s
  have hnodeHistory :
      d2FlowTreeRunWithParentOverwrites ctx.initial ctx.level
        runActive runRole runQuota ctx.overwrite t = .node G low high children := by
    calc
      _ = d2FlowTreeAtPath i (d2FlowCandidateRun d initial t) path :=
        (hpath t).symm
      _ = .node G low high children := by simpa [d, initial] using hnode
  have haHistory : runActive t ctx.level = true := by
    simpa [runActive, hlevel, d] using ha
  have hrHistory : runRole t ctx.level = .topDesc := by
    simpa [runRole, hlevel, d] using hr
  have hzero :=
    d2FlowTreeRunWithParentOverwrites_topDesc_child_zero
      ctx.initial children runActive runRole runQuota ctx.overwrite port
      hnodeHistory haHistory hrHistory
  rw [hpath (t + 1)]
  simpa [d, initial, ctx] using hzero

/-- Regular active parents write balanced endpoint data to their children in
the concrete candidate run, even when the parent lies below active ancestors. -/
theorem d2FlowCandidateRun_regular_parent_child_balanced
    {h i t G low high : Nat} (path : D2FlowPath i)
    (children : Fin 8 → D2FlowTree (h + 1))
    (hnode : d2FlowTreeAtPath i
      (d2FlowCandidateRun (h + 2 + i)
        (d2FlowTreeInitial 8192 (h + 2 + i)) t) path =
      .node G low high children)
    (ha : d2FlowCandidateActive (h + 2 + i) t i = true)
    (hr : d2FlowCandidateRole (h + 2 + i) t i = .topRise ∨
      d2FlowCandidateRole (h + 2 + i) t i = .mid ∨
      d2FlowCandidateRole (h + 2 + i) t i = .botDesc)
    (port : Fin 8) :
    (d2FlowTreeRootData
      (d2FlowTreeChild
        (d2FlowTreeAtPath i
          (d2FlowCandidateRun (h + 2 + i)
            (d2FlowTreeInitial 8192 (h + 2 + i)) (t + 1)) path) port)).2.1 +
    (d2FlowTreeRootData
      (d2FlowTreeChild
        (d2FlowTreeAtPath i
          (d2FlowCandidateRun (h + 2 + i)
            (d2FlowTreeInitial 8192 (h + 2 + i)) (t + 1)) path) port)).2.2 =
    d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowTreeAtPath i
          (d2FlowCandidateRun (h + 2 + i)
            (d2FlowTreeInitial 8192 (h + 2 + i)) (t + 1)) path) port) := by
  classical
  let d := h + 2 + i
  let initial := d2FlowTreeInitial 8192 d
  let runActive := d2FlowCandidateRunActive d
  let runRole := d2FlowCandidateRunRole d
  let runQuota := d2FlowCandidateRunQuota d
  let overwrite := d2FlowCandidateRunOverwrite d initial
  let ctx := d2FlowTreePathContext i initial path 0
    runActive runRole runQuota overwrite
  have hlevel : ctx.level = i := by
    simpa [ctx, runActive, runRole, runQuota, overwrite, d, initial] using
      d2FlowTreePathContext_level initial path 0 runActive runRole runQuota
        overwrite
  have hpath (s : Nat) :
      d2FlowTreeAtPath i (d2FlowCandidateRun d initial s) path =
        d2FlowTreeRunWithParentOverwrites ctx.initial ctx.level
          runActive runRole runQuota ctx.overwrite s := by
    rw [d2FlowCandidateRun_path_as_history]
    exact d2FlowTreePathHistory_eq_context_run initial path 0
      (d2FlowCandidateRunActive d) (d2FlowCandidateRunRole d)
      (d2FlowCandidateRunQuota d) (d2FlowCandidateRunOverwrite d initial) s
  have hnodeHistory :
      d2FlowTreeRunWithParentOverwrites ctx.initial ctx.level
        runActive runRole runQuota ctx.overwrite t = .node G low high children := by
    calc
      _ = d2FlowTreeAtPath i (d2FlowCandidateRun d initial t) path :=
        (hpath t).symm
      _ = .node G low high children := by simpa [d, initial] using hnode
  have haHistory : runActive t ctx.level = true := by
    simpa [runActive, hlevel, d] using ha
  have hrHistory : runRole t ctx.level = .topRise ∨
      runRole t ctx.level = .mid ∨ runRole t ctx.level = .botDesc := by
    simpa [runRole, hlevel, d] using hr
  have hbalanced := d2FlowTreeRunWithParentOverwrites_child_balanced
    (h := h + 1) (i := ctx.level) (n := t) (G := G) (low := low)
    (high := high) ctx.initial runActive runRole runQuota ctx.overwrite
    children hnodeHistory haHistory hrHistory port
  rw [hpath (t + 1)]
  simpa [d, initial, ctx] using hbalanced

/-- Every active top-rise sender has zero deficit at its current path: its
active parent one stage earlier is top-descending and resets that child root.
-/
theorem d2FlowCandidateRun_active_topRise_root_zero
    {h i t G low high : Nat} (hd : 7 <= h + 1 + i) (ht : 2 <= t)
    (path : D2FlowPath i) (children : Fin 8 -> D2FlowTree h)
    (hnode : d2FlowTreeAtPath i
      (d2FlowCandidateRun (h + 1 + i)
        (d2FlowTreeInitial 8192 (h + 1 + i)) t) path =
      .node G low high children)
    (ha : active (h + 1 + i) (tfD2 (h + 1 + i)) (i + 1) (t + 1))
    (hr : d2ScheduleRole (h + 1 + i) (i + 1) (t + 1) = .topRise)
    (port : Fin 8) :
    d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowTreeAtPath i
          (d2FlowCandidateRun (h + 1 + i)
            (d2FlowTreeInitial 8192 (h + 1 + i)) (t + 1)) path) port) = 0 := by
  classical
  let d := h + 1 + i
  have hnotTop : ¬ ((i + 1) = alpha d (t + 1) /\
      alpha d (t + 1) < alpha d (t + 2)) := by
    intro h
    have htop : d2ScheduleRole d (i + 1) (t + 1) = .topDesc := by
      simp [d2ScheduleRole, h.1, h.2]
    rw [hr] at htop
    cases htop
  have hparentActive' := active_parent_of_not_topDesc
    (d := d) (tf := tfD2 d) (i := i + 1) (t := t + 1)
    (by omega) (by omega) ha hnotTop
  have hparentActive : active d (tfD2 d) i t := by
    simpa using hparentActive'
  have hparentRole := d2ScheduleRole_parent_of_active_topRise
    (d := d) (tf := tfD2 d) (i := i + 1) (t := t + 1)
    (by omega) (by omega) ha hr
  have haCandidate : d2FlowCandidateActive d t i = true := by
    rw [d2FlowCandidateActive_matches_schedule (d := d) (t := t)
      (i := i) (by omega)]
    exact decide_eq_true hparentActive
  have hrCandidate : d2FlowCandidateRole d t i = .topDesc := by
    rw [d2FlowCandidateRole_matches_schedule (d := d) (t := t)
      (i := i) (by omega)]
    exact hparentRole
  have hzero := d2FlowCandidateRun_topDesc_parent_child_zero_at_path
    (h := h) (i := i) (t := t) path children hnode haCandidate hrCandidate port
  simpa [d] using hzero

/-- Full-tree form: no local node decomposition needs to be supplied by the
caller; every path of the indicated depth has a parent node. -/
theorem d2FlowCandidateRun_active_topRise_root_zero_at_any_parent_path
    {h i t : Nat} (hd : 7 <= h + 1 + i) (ht : 2 <= t)
    (path : D2FlowPath i)
    (ha : active (h + 1 + i) (tfD2 (h + 1 + i)) (i + 1) (t + 1))
    (hr : d2ScheduleRole (h + 1 + i) (i + 1) (t + 1) = .topRise)
    (port : Fin 8) :
    d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowTreeAtPath i
          (d2FlowCandidateRun (h + 1 + i)
            (d2FlowTreeInitial 8192 (h + 1 + i)) (t + 1)) path) port) = 0 := by
  cases hnode : d2FlowTreeAtPath i
      (d2FlowCandidateRun (h + 1 + i)
        (d2FlowTreeInitial 8192 (h + 1 + i)) t) path with
  | node G low high children =>
      exact d2FlowCandidateRun_active_topRise_root_zero
        hd ht path children hnode ha hr port

/-- For any active child role other than top-descending, the previous-stage
active parent supplies the next-stage affine deficit profile: ordinary parents
cut with the checked affine bound, and a top-descending parent resets the root
to zero. -/
theorem d2FlowCandidateRun_core_provider_affine_profile_at_active_nonTopDesc_child
    {h i t G low high : Nat} (hd : 7 <= h + 1 + i) (ht : 2 <= t)
    (path : D2FlowPath i) (port : Fin 8)
    (hchildActive : active (h + 1 + i) (tfD2 (h + 1 + i))
      (i + 1) (t + 1))
    (hchildRole : d2ScheduleRole (h + 1 + i) (i + 1) (t + 1) ≠ .topDesc)
    (hcore : d2FlowStageAffineCoreInputs
      (fun k => d2FlowCandidateActive (h + 1 + i) t k)
      (fun k => d2FlowCandidateRole (h + 1 + i) t k)
      (fun k => d2FlowCandidateCapacity (h + 1 + i) k t) 0
      (d2FlowCandidateRun (h + 1 + i)
        (d2FlowTreeInitial 8192 (h + 1 + i)) t)) :
    8192 * d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowTreeAtPath i
          (d2FlowCandidateRun (h + 1 + i)
            (d2FlowTreeInitial 8192 (h + 1 + i)) (t + 1)) path) port) + 7 <=
      15 * d2FlowCandidateCapacity (h + 1 + i) (i + 1) (t + 1) := by
  classical
  let d := h + 1 + i
  have hparentCases := active_nonTop_parent_role_cases
    (d := d) (tf := tfD2 d) (i := i + 1) (t := t + 1)
    (by omega) (by omega) hchildActive hchildRole
  have hparentActive : active d (tfD2 d) i t := by
    simpa using hparentCases.1
  have hparentActiveBool : d2FlowCandidateActive d t i = true := by
    rw [d2FlowCandidateActive_matches_schedule (d := d) (t := t)
      (i := i) (by omega)]
    exact decide_eq_true hparentActive
  have hparentRoleSchedule :
      d2ScheduleRole d i t = .topDesc \/
        d2ScheduleRole d i t = .topRise \/
        d2ScheduleRole d i t = .mid \/
        d2ScheduleRole d i t = .botDesc := by
    simpa using hparentCases.2
  cases hnode : d2FlowTreeAtPath i
      (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) t) path with
  | node G low high children =>
      rcases hparentRoleSchedule with htop | hregular
      · have htopCandidate : d2FlowCandidateRole d t i = .topDesc := by
          rw [d2FlowCandidateRole_matches_schedule (d := d) (t := t)
            (i := i) (by omega)]
          exact htop
        have hzero :=
          d2FlowCandidateRun_topDesc_parent_child_zero_at_path
            path children (by simpa [d] using hnode)
            (by simpa [d] using hparentActiveBool) htopCandidate port
        have hcapPos : 0 < d2FlowCandidateCapacity d (i + 1) (t + 1) := by
          unfold d2FlowCandidateCapacity
          exact Nat.pow_pos (by decide)
        have hzero' : d2FlowTreeRootDeficit
            (d2FlowTreeChild
              (d2FlowTreeAtPath i
                (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) (t + 1))
                path) port) = 0 := by
          simpa [d] using hzero
        rw [hzero']
        nlinarith [hcapPos]
      · have hregularSchedule :
            d2ScheduleRole d i t = .topRise \/
              d2ScheduleRole d i t = .mid \/
              d2ScheduleRole d i t = .botDesc := by
          rcases hregular with hrise | hrest
          · exact Or.inl hrise
          · rcases hrest with hmid | hbot
            · exact Or.inr (Or.inl hmid)
            · exact Or.inr (Or.inr hbot)
        have hregularCandidate :
            d2FlowCandidateRole d t i = .topRise \/
              d2FlowCandidateRole d t i = .mid \/
              d2FlowCandidateRole d t i = .botDesc := by
          rw [d2FlowCandidateRole_matches_schedule (d := d) (t := t)
            (i := i) (by omega)]
          exact hregularSchedule
        have hprofile := d2FlowCandidateRun_core_provider_affine_child_at_active_parent
          (h := h) (i := i) (t := t) (G := G) (low := low) (high := high)
          hd (by omega) path
          hparentActive hregularSchedule (by simpa [d] using hcore)
        have hport := hprofile port
        simpa [d] using hport

end Chvatal.D2Reserve
