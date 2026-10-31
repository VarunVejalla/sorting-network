import D2Stage16LevelFourInputs
import D2Stage15LevelOneInputs
import D2Stage16Frontier
import D2Stage14Contract

namespace Chvatal.D2Reserve

attribute [local irreducible] d2FlowStageInvInputs
attribute [local irreducible] d2FlowTreeInv
attribute [local irreducible] d2FlowCandidateRun

set_option maxHeartbeats 10000000
set_option maxRecDepth 4096

private theorem d2FlowTreeInv_child_sub300
    {h scale : Nat} (tree : D2FlowTree (h + 1))
    (hinv : d2FlowTreeInv scale tree) (j : Fin 8) :
    d2FlowTreeInv scale (d2FlowTreeChild tree j) := by
  cases tree with
  | node G low high children =>
      have hx := hinv
      simp only [d2FlowTreeInv] at hx
      simpa using hx.2.2.2 j

/-- The actual Stage-16 level-two sender satisfies its complete recursive
input contract. At startup Stage 15 resets its parent child roots to zero;
at later depths the level-one top-rise cut supplies balance and the root cap.
In either case, Stage-15 level-three quotas provide the endpoint reserves and
fresh mass, and level-four descendants use the checked Stage-16 contract. -/
theorem d2FlowCandidateRun_stage16_levelTwo_inputs
    (childDepth : Nat) (hd : 7 <= childDepth)
    (j k : Fin 8) :
    let d := childDepth + 7
    let tree := d2FlowTreeChild
      (d2FlowTreeChild (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 16) j) k
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 16) (d2FlowCandidateRole d 16)
      (d2FlowCandidateQuota d 16)
      (fun x => d2FlowCandidateCapacity d x 16) 2 tree := by
  classical
  let d := childDepth + 7
  let initial := d2FlowTreeInitial 8192 d
  let run15 := d2FlowCandidateRun d initial 15
  let run16 := d2FlowCandidateRun d initial 16
  let parent := d2FlowTreeChild run15 j
  let tree := d2FlowTreeChild (d2FlowTreeChild run16 j) k
  have hd14 : 14 <= d := by dsimp [d]; omega
  have hstartupRole : d2FlowCandidateRole d 15 1 =
      if d = 14 then .topDesc else .topRise :=
    d2FlowCandidateRole_stage15_top hd14
  have hactive15_1 : d2FlowCandidateActive d 15 1 = true :=
    (d2FlowCandidateActive_stage15_at hd14).1
  have hparentInputs := d2FlowCandidateRun_stage15_levelOne_inputs
    childDepth hd j
  have hparentInputs' : d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 15) (d2FlowCandidateRole d 15)
      (d2FlowCandidateQuota d 15)
      (fun x => d2FlowCandidateCapacity d x 15) 1 parent := by
    simpa [d, initial, run15, parent] using hparentInputs
  have hinvRun15 := d2FlowCandidateStage14_preserves_inv childDepth hd
  have hparentInv : d2FlowTreeInv 8192 parent := by
    exact d2FlowTreeInv_child_sub300 run15 hinvRun15 j
  have hproject := d2FlowStage_child_child_projection
    (active := d2FlowCandidateActive d 15)
    (role := d2FlowCandidateRole d 15)
    (quota := d2FlowCandidateQuota d 15)
    (h := childDepth + 5) (i := 0) run15 j k
  have hrun16 : run16 = d2FlowCandidateStage d 15 run15 := by
    change d2FlowCandidateRun d initial 16 =
      d2FlowCandidateStage d 15 (d2FlowCandidateRun d initial 15)
    rw [d2FlowCandidateRun.eq_def]
  have htreeEq : tree = d2FlowTreeChild
      (d2FlowStage (d2FlowCandidateActive d 15)
        (d2FlowCandidateRole d 15) (d2FlowCandidateQuota d 15)
        (childDepth + 6) 1 parent) k := by
    simpa [d, initial, run15, run16, parent, tree, hrun16] using hproject
  have hactive16_2 : d2FlowCandidateActive d 16 2 = true := by
    rw [d2FlowCandidateActive_stage16_iff hd14]
    by_cases h14 : d = 14 <;> simp [h14]
  have hrole16_2 : d2FlowCandidateRole d 16 2 =
      if d = 14 then .topRise else .mid := by
    by_cases h14 : d = 14
    case pos =>
      have hcd : childDepth = 7 := by dsimp [d] at h14; omega
      subst childDepth
      have htop := d2FlowCandidateRole_stage16_top (d := d) hd14
      rw [h14] at htop
      simpa using htop
    case neg =>
      have h := d2FlowCandidateRole_stage16_internal_mid
        (d := d) (i := 2) (by omega) (Or.inl rfl)
      simpa [h14] using h
  have hrole15_1 : d2FlowCandidateRole d 15 1 =
      if d = 14 then .topDesc else .topRise := by
    simpa using hstartupRole
  have hactive15_2 : d2FlowCandidateActive d 15 2 = false := by
    cases h : d2FlowCandidateActive d 15 2 with
    | false => rfl
    | true =>
        have hlevel := d2FlowCandidateActive_stage15_level_bound h
        rcases hlevel with h | h | h | h <;> omega
  have hparentNodeCap : forall G low high children,
      parent = D2FlowTree.node G low high children ->
      d2FlowCandidateActive d 15 1 = true ->
      d2FlowCandidateRole d 15 1 = .topRise ->
      512 * d2FlowTreeRootDeficit tree <=
        d2FlowCandidateCapacity d 2 16 := by
    intro G low high children hnode ha hr
    have hinput : d2FlowStageInvInputs 8192
        (d2FlowCandidateActive d 15) (d2FlowCandidateRole d 15)
        (d2FlowCandidateQuota d 15)
        (fun x => d2FlowCandidateCapacity d x 15) 1
        (.node G low high children) := by
      rw [← hnode]
      exact hparentInputs'
    have hinv : d2FlowTreeInv 8192 (.node G low high children) := by
      rw [← hnode]
      exact hparentInv
    have hchild := d2FlowStage_regular_child_g_bound_of_tree_inputs
      (active := d2FlowCandidateActive d 15)
      (role := d2FlowCandidateRole d 15)
      (quota := d2FlowCandidateQuota d 15)
      (cap := fun x => d2FlowCandidateCapacity d x 15)
      (stageDepth := childDepth + 5) (i := 1)
      (.node G low high children) ha (Or.inl hr) hinv hinput
    have hscale : d2FlowCandidateCapacity d 2 16 =
        2 * d2FlowCandidateCapacity d 1 15 := by
      exact d2FlowCandidateCapacity_succ_level_next_stage d 1 15 (by omega)
    have hc := hchild k
    rw [htreeEq, hnode, hscale]
    simpa using hc
  have hbalance : (d2FlowTreeRootData tree).2.1 +
      (d2FlowTreeRootData tree).2.2 = d2FlowTreeRootDeficit tree := by
    by_cases h14 : d = 14
    case pos =>
      have hcd : childDepth = 7 := by dsimp [d] at h14; omega
      subst childDepth
      cases hnode : parent with
      | node G low high children =>
          have hz := d2FlowStage_topDesc_child_rootdata
            (active := d2FlowCandidateActive d 15)
            (role := d2FlowCandidateRole d 15)
            (quota := d2FlowCandidateQuota d 15)
            (h := 12) (i := 1) (G := G) (low := low) (high := high)
            children hactive15_1 (by simpa [h14] using hstartupRole) k
          have hz' : d2FlowTreeRootData tree = (0, 0, 0) := by
            simpa [htreeEq, hnode] using hz
          have hzdef : d2FlowTreeRootDeficit tree = 0 := by
            rw [← d2FlowTreeRootData_fst_eq_deficit, hz']
          rw [hz', hzdef]
          rfl
    case neg =>
      cases hnode : parent with
      | node G low high children =>
          have hr : d2FlowCandidateRole d 15 1 = .topRise := by
            simpa [h14] using hrole15_1
          have hb := d2FlowStage_regular_child_balanced
            (active := d2FlowCandidateActive d 15)
            (role := d2FlowCandidateRole d 15)
            (quota := d2FlowCandidateQuota d 15)
            (h := childDepth + 5) (i := 1)
            (G := G) (low := low) (high := high) children
            hactive15_1 (Or.inl hr) k
          simpa [htreeEq, hnode] using hb
  have hrootcap : 512 * d2FlowTreeRootDeficit tree <=
      d2FlowCandidateCapacity d 2 16 := by
    by_cases h14 : d = 14
    case pos =>
      have hcd : childDepth = 7 := by dsimp [d] at h14; omega
      subst childDepth
      have hzero : d2FlowTreeRootDeficit tree = 0 := by
        have hzdata : d2FlowTreeRootData tree = (0, 0, 0) := by
          cases hnode : parent with
          | node G low high children =>
              have hz := d2FlowStage_topDesc_child_rootdata
                (active := d2FlowCandidateActive d 15)
                (role := d2FlowCandidateRole d 15)
                (quota := d2FlowCandidateQuota d 15)
                (h := 12) (i := 1) (G := G) (low := low) (high := high)
                children hactive15_1 (by simpa [h14] using hstartupRole) k
              simpa [htreeEq, hnode] using hz
        have hzfst := congrArg Prod.fst hzdata
        simpa [d2FlowTreeRootData_fst_eq_deficit] using hzfst
      rw [hzero]
      omega
    case neg =>
      have hr : d2FlowCandidateRole d 15 1 = .topRise := by
        simpa [h14] using hrole15_1
      cases hnode : parent with
      | node G low high children =>
          have hc := hparentNodeCap G low high children hnode hactive15_1 hr
          simpa [htreeEq, hnode] using hc
  have hquotaCap : 256 * d2FlowCandidateQuota d 16 2
      (if d = 14 then .topRise else .mid) <=
        d2FlowCandidateCapacity d 2 16 := by
    have hactiveRaw : active d (tfD2 d) 2 16 := by
      have hm := d2FlowCandidateActive_matches_schedule
        (d := d) (i := 2) (t := 16) (by omega)
      rw [hactive16_2] at hm
      exact of_decide_eq_true hm.symm
    have hroleSchedule : d2ScheduleRole d 2 16 =
        (if d = 14 then .topRise else .mid) := by
      have hm := d2FlowCandidateRole_matches_schedule
        (d := d) (i := 2) (t := 16) (by omega)
      exact hm.symm.trans hrole16_2
    have hregular : d2ScheduleRole d 2 16 = .topRise \/
        d2ScheduleRole d 2 16 = .mid \/
        d2ScheduleRole d 2 16 = .botDesc := by
      by_cases h14 : d = 14
      case pos =>
        left
        simpa [h14] using hroleSchedule
      case neg =>
        right
        left
        simpa [h14] using hroleSchedule
    have h := d2FlowCandidateQuota_le_capacity_div_256
      (by omega) hactiveRaw hregular
    simpa [hroleSchedule] using h
  have heven : d2FlowCandidateQuota d 16 2
      (if d = 14 then .topRise else .mid) % 2 = 0 := by
    have hactiveRaw : active d (tfD2 d) 2 16 := by
      have hm := d2FlowCandidateActive_matches_schedule
        (d := d) (i := 2) (t := 16) (by omega)
      rw [hactive16_2] at hm
      exact of_decide_eq_true hm.symm
    have hroleSchedule : d2ScheduleRole d 2 16 =
        (if d = 14 then .topRise else .mid) := by
      have hm := d2FlowCandidateRole_matches_schedule
        (d := d) (i := 2) (t := 16) (by omega)
      exact hm.symm.trans hrole16_2
    have hregular : d2ScheduleRole d 2 16 = .topRise \/
        d2ScheduleRole d 2 16 = .mid \/
        d2ScheduleRole d 2 16 = .botDesc := by
      by_cases h14 : d = 14
      case pos =>
        left
        simpa [h14] using hroleSchedule
      case neg =>
        right
        left
        simpa [h14] using hroleSchedule
    have h := d2FlowCandidateQuota_even (by omega) hactiveRaw (by omega) hregular
    simpa [hrole16_2] using h
  have hq3floor : forall s : Fin 8,
      d2FlowCandidateQuota d 15 3 .mid <=
        d2FlowTreeRootDeficit (d2FlowTreeChild tree s) := by
    intro s
    have hproj3 := d2FlowStage_path3_projection
      (active := d2FlowCandidateActive d 15)
      (role := d2FlowCandidateRole d 15)
      (quota := d2FlowCandidateQuota d 15)
      (h := childDepth + 4) (i := 0) run15 j k s
    have hprojRoot := congrArg d2FlowTreeRootDeficit hproj3
    have hlocal : d2FlowTreeRootDeficit (d2FlowTreeChild tree s) =
        d2FlowTreeRootDeficit
          (d2FlowTreeChild
            (d2FlowStage (d2FlowCandidateActive d 15)
              (d2FlowCandidateRole d 15) (d2FlowCandidateQuota d 15)
              (childDepth + 5) 2 (d2FlowTreeChild parent k)) s) := by
      simpa [d, initial, run15, run16, parent, tree, hrun16] using hprojRoot
    cases hsource : d2FlowTreeChild parent k with
    | node G2 low2 high2 children2 =>
        rw [hlocal, hsource, d2FlowStage_inactive_child
          (active := d2FlowCandidateActive d 15)
          (role := d2FlowCandidateRole d 15)
          (quota := d2FlowCandidateQuota d 15)
          (h := childDepth + 4) (i := 2) (G := G2)
          (low := low2) (high := high2) children2 hactive15_2 s]
        cases hchild : children2 s with
        | node G3 low3 high3 children3 =>
            have ha3 : d2FlowCandidateActive d 15 3 = true :=
              (d2FlowCandidateActive_stage15_at hd14).2.1
            have hr3 : d2FlowCandidateRole d 15 3 = .mid :=
              d2FlowCandidateRole_stage15_internal_mid hd14 3 (Or.inl rfl)
            have hroot : d2FlowTreeRootDeficit
                (d2FlowStage (d2FlowCandidateActive d 15)
                  (d2FlowCandidateRole d 15) (d2FlowCandidateQuota d 15)
                  (childDepth + 4) 3 (.node G3 low3 high3 children3)) =
                G3 + d2FlowCandidateQuota d 15 3 .mid := by
              rw [d2FlowStage_active_node_deficit
                (active := d2FlowCandidateActive d 15)
                (role := d2FlowCandidateRole d 15)
                (quota := d2FlowCandidateQuota d 15)
                (h := childDepth + 3) (i := 3) (G := G3)
                (low := low3) (high := high3) children3 ha3, hr3]
            rw [hroot]
            omega
  have hq3relation : 128 * d2FlowCandidateQuota d 15 3 .mid =
      15 * d2FlowCandidateCapacity d 2 16 := by
    have hcap : d2FlowCandidateCapacity d 2 16 = 2 ^ (3 * d - 17) := by
      simp [d2FlowCandidateCapacity, d2FlowCandidateCapacityExponent]
      omega
    have hq : d2FlowCandidateQuota d 15 3 .mid =
        15 * 2 ^ (3 * d - 24) := by
      simp [d2FlowCandidateQuota, d2FlowCandidateCapacityExponent]
      omega
    rw [hcap, hq]
    rw [show 3 * d - 17 = 7 + (3 * d - 24) by omega, pow_add]
    ring
  have hleft : d2FlowCandidateCapacity d 2 16 <=
      128 * d2FlowTreeRootDeficit
        (d2FlowTreeChild tree (Fin.mk 0 (by omega))) := by
    have hf := hq3floor (Fin.mk 0 (by omega))
    have hcq : d2FlowCandidateCapacity d 2 16 <=
        128 * d2FlowCandidateQuota d 15 3 .mid := by
      nlinarith [hq3relation]
    exact le_trans hcq (Nat.mul_le_mul_left 128 hf)
  have hright : d2FlowCandidateCapacity d 2 16 <=
      128 * d2FlowTreeRootDeficit
        (d2FlowTreeChild tree (Fin.mk 7 (by omega))) := by
    have hf := hq3floor (Fin.mk 7 (by omega))
    have hcq : d2FlowCandidateCapacity d 2 16 <=
        128 * d2FlowCandidateQuota d 15 3 .mid := by
      nlinarith [hq3relation]
    exact le_trans hcq (Nat.mul_le_mul_left 128 hf)
  have htotalLower : 8 * d2FlowCandidateQuota d 15 3 .mid <=
      d2FlowTotal (fun s : Fin 8 =>
        d2FlowTreeRootDeficit (d2FlowTreeChild tree s)) := by
    change 8 * d2FlowCandidateQuota d 15 3 .mid <=
      Finset.univ.sum (fun s : Fin 8 =>
        d2FlowTreeRootDeficit (d2FlowTreeChild tree s))
    calc
      8 * d2FlowCandidateQuota d 15 3 .mid =
          Finset.univ.sum (fun _ : Fin 8 => d2FlowCandidateQuota d 15 3 .mid) := by simp
      _ <= Finset.univ.sum (fun s : Fin 8 =>
          d2FlowTreeRootDeficit (d2FlowTreeChild tree s)) := by
        apply Finset.sum_le_sum
        intro s hs
        exact hq3floor s
  have halloc : d2FlowCandidateQuota d 16 2
      (if d = 14 then .topRise else .mid) <=
      d2FlowTotal (fun s => d2FlowTreeRootDeficit (d2FlowTreeChild tree s)) -
        d2FlowTreeRootDeficit tree := by
    have hbudget : d2FlowCandidateQuota d 16 2
          (if d = 14 then .topRise else .mid) +
        d2FlowTreeRootDeficit tree <=
        8 * d2FlowCandidateQuota d 15 3 .mid := by
      nlinarith [hquotaCap, hrootcap, hq3relation]
    omega
  have hchildren : forall s : Fin 8,
      d2FlowStageInvInputs 8192
        (d2FlowCandidateActive d 16) (d2FlowCandidateRole d 16)
        (d2FlowCandidateQuota d 16)
        (fun x => d2FlowCandidateCapacity d x 16) 3
        (d2FlowTreeChild tree s) := by
    intro s
    have hf : d2FlowCandidateActive d 16 3 = false := by
      cases h : d2FlowCandidateActive d 16 3 with
      | false => rfl
      | true =>
          have hlev := (d2FlowCandidateActive_stage16_iff hd14).mp h
          by_cases h14 : d = 14 <;> simp [h14] at hlev <;> omega
    exact d2FlowStageInvInputs_inactive_of_children
      (active := d2FlowCandidateActive d 16)
      (role := d2FlowCandidateRole d 16)
      (quota := d2FlowCandidateQuota d 16)
      (cap := fun x => d2FlowCandidateCapacity d x 16)
      8192 3 (d2FlowTreeChild tree s) hf (by
        intro t
        exact d2FlowCandidateRun_stage16_levelFour_inputs
          childDepth hd j k s t)
  by_cases h14 : d = 14
  case pos =>
    have hcd : childDepth = 7 := by dsimp [d] at h14; omega
    subst childDepth
    have hrole : d2FlowCandidateRole d 16 2 = .topRise := by
      simpa [h14] using hrole16_2
    exact d2FlowStageInvInputs_topRise_of_contract
      8192 2 tree hactive16_2 hrole hchildren hbalance hrootcap
      (by simpa [h14] using hquotaCap) (by simpa [h14] using halloc)
      (by simpa [h14] using heven) hleft hright
  case neg =>
    have hrole : d2FlowCandidateRole d 16 2 = .mid := by
      simpa [h14] using hrole16_2
    exact d2FlowStageInvInputs_mid_of_contract
      8192 2 tree hactive16_2 hrole hchildren hbalance hrootcap
      (by simpa [h14] using hquotaCap) (by simpa [h14] using halloc)
      (by simpa [h14] using heven) hleft hright

end Chvatal.D2Reserve
