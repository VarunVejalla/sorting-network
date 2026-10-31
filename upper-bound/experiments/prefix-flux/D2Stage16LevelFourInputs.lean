import D2Stage16LevelSixInputs
import D2Stage15LevelThreeInputs
import D2Stage15PreservesInv
import D2Stage14Contract

namespace Chvatal.D2Reserve

attribute [local irreducible] d2FlowStageInvInputs
attribute [local irreducible] d2FlowTreeInv
attribute [local irreducible] d2FlowCandidateRun

set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

/-- The actual Stage-16 level-four sender satisfies its full recursive input
contract. The Stage-15 level-five quota supplies the endpoint reserves and
the fresh-allocation margin; level-six children use the checked Stage-16
level-six contracts. -/
theorem d2FlowCandidateRun_stage16_levelFour_inputs
    (childDepth : Nat) (hd : 7 <= childDepth)
    (j k m l : Fin 8) :
    let d := childDepth + 7
    let tree := d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 16) j) k) m) l
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 16) (d2FlowCandidateRole d 16)
      (d2FlowCandidateQuota d 16)
      (fun x => d2FlowCandidateCapacity d x 16) 4 tree := by
  classical
  let d := childDepth + 7
  let initial := d2FlowTreeInitial 8192 d
  let run15 := d2FlowCandidateRun d initial 15
  let run16 := d2FlowCandidateRun d initial 16
  let parent := d2FlowTreeChild (d2FlowTreeChild (d2FlowTreeChild run15 j) k) m
  let tree := d2FlowTreeChild (d2FlowTreeChild (d2FlowTreeChild
    (d2FlowTreeChild run16 j) k) m) l
  have hd14 : 14 <= d := by dsimp [d]; omega
  have hactive4 : d2FlowCandidateActive d 16 4 = true := by
    rw [d2FlowCandidateActive_stage16_iff hd14]
    by_cases h14 : d = 14 <;> simp [h14]
  have hrole4 : d2FlowCandidateRole d 16 4 = .mid := by
    by_cases h14 : d = 14
    case pos =>
      have hcd : childDepth = 7 := by dsimp [d] at h14; omega
      subst childDepth
      norm_num [d, d2FlowCandidateRole, d2ScheduleRole,
        alpha, alphaStar, ceilParity, omega]
    case neg =>
      exact d2FlowCandidateRole_stage16_internal_mid
        (i := 4) (by omega) (Or.inr rfl)
  have hactive15_4 : d2FlowCandidateActive d 15 4 = false := by
    cases h : d2FlowCandidateActive d 15 4 with
    | false => rfl
    | true =>
        have hlevel := d2FlowCandidateActive_stage15_level_bound h
        rcases hlevel with h | h | h | h <;> omega
  have hactive15_3 : d2FlowCandidateActive d 15 3 = true :=
    (d2FlowCandidateActive_stage15_at hd14).2.1
  have hrole15_3 : d2FlowCandidateRole d 15 3 = .mid :=
    d2FlowCandidateRole_stage15_internal_mid hd14 3 (Or.inl rfl)
  have hregular15_3 : d2FlowCandidateRole d 15 3 = .topRise \/
      d2FlowCandidateRole d 15 3 = .mid \/
      d2FlowCandidateRole d 15 3 = .botDesc := Or.inr (Or.inl hrole15_3)
  have hparentInputs := d2FlowCandidateRun_stage15_levelThree_inputs
    childDepth hd j k m
  have hparentInv : d2FlowTreeInv 8192 parent := by
    have hinv := d2FlowCandidateStage14_preserves_inv childDepth hd
    have h2 := d2FlowTreeInv_grandchild
      (h := childDepth + 5) run15 hinv j k
    have hnode : d2FlowTreeInv 8192
        (d2FlowTreeChild (d2FlowTreeChild run15 j) k) := h2
    cases htree : d2FlowTreeChild (d2FlowTreeChild run15 j) k with
    | node G low high children =>
        have hnode' := hnode
        rw [htree] at hnode'
        simp only [d2FlowTreeInv] at hnode'
        simpa [parent, htree] using hnode'.2.2.2 m
  have hparentInputs' : d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 15) (d2FlowCandidateRole d 15)
      (d2FlowCandidateQuota d 15)
      (fun x => d2FlowCandidateCapacity d x 15) 3 parent := by
    simpa [d, initial, run15, parent] using hparentInputs
  have hproject := d2FlowStage_path4_projection
    (active := d2FlowCandidateActive d 15)
    (role := d2FlowCandidateRole d 15)
    (quota := d2FlowCandidateQuota d 15)
    (h := childDepth + 3) (i := 0) run15 j k m l
  have hrun16 : run16 = d2FlowCandidateStage d 15 run15 := by
    change d2FlowCandidateRun d initial 16 =
      d2FlowCandidateStage d 15 (d2FlowCandidateRun d initial 15)
    rw [d2FlowCandidateRun.eq_def]
  have htreeEq : tree = d2FlowTreeChild
      (d2FlowStage (d2FlowCandidateActive d 15)
        (d2FlowCandidateRole d 15) (d2FlowCandidateQuota d 15)
        (childDepth + 4) 3 parent) l := by
    simpa [d, initial, run15, run16, parent, tree, hrun16] using hproject
  have hchildCap := d2FlowStage_regular_child_g_bound_of_tree_inputs
    (active := d2FlowCandidateActive d 15)
    (role := d2FlowCandidateRole d 15)
    (quota := d2FlowCandidateQuota d 15)
    (cap := fun x => d2FlowCandidateCapacity d x 15)
    (stageDepth := childDepth + 3) (i := 3) parent
    hactive15_3 hregular15_3 hparentInv hparentInputs'
  have hcapShift : d2FlowCandidateCapacity d 4 16 =
      2 * d2FlowCandidateCapacity d 3 15 := by
    exact d2FlowCandidateCapacity_succ_level_next_stage d 3 15 (by omega)
  have hrootcap : 512 * d2FlowTreeRootDeficit tree <=
      d2FlowCandidateCapacity d 4 16 := by
    have hc := hchildCap l
    rw [htreeEq, hcapShift]
    simpa using hc
  have hbalance : (d2FlowTreeRootData tree).2.1 +
      (d2FlowTreeRootData tree).2.2 = d2FlowTreeRootDeficit tree := by
    cases hparentNode : parent with
    | node G low high children =>
        have hb := d2FlowStage_regular_child_balanced
          (active := d2FlowCandidateActive d 15)
          (role := d2FlowCandidateRole d 15)
          (quota := d2FlowCandidateQuota d 15)
          (h := childDepth + 3) (i := 3)
          (G := G) (low := low) (high := high) children
          hactive15_3 hregular15_3 l
        simpa [htreeEq, hparentNode] using hb
  have hq5floor : forall s : Fin 8,
      d2FlowCandidateQuota d 15 5 .mid <=
        d2FlowTreeRootDeficit (d2FlowTreeChild tree s) := by
    intro s
    have hproj5 := d2FlowStage_path5_projection
      (active := d2FlowCandidateActive d 15)
      (role := d2FlowCandidateRole d 15)
      (quota := d2FlowCandidateQuota d 15)
      (h := childDepth + 2) (i := 0) run15 j k m l s
    have hlocal : d2FlowTreeRootDeficit (d2FlowTreeChild tree s) =
        d2FlowTreeRootDeficit
          (d2FlowTreeChild
            (d2FlowStage (d2FlowCandidateActive d 15)
              (d2FlowCandidateRole d 15) (d2FlowCandidateQuota d 15)
              (childDepth + 3) 4
              (d2FlowTreeChild parent l)) s) := by
      simpa [d, initial, run15, run16, tree, hrun16] using hproj5
    cases hsource : d2FlowTreeChild parent l with
    | node G4 low4 high4 children4 =>
        rw [hlocal, hsource, d2FlowStage_inactive_child
          (active := d2FlowCandidateActive d 15)
          (role := d2FlowCandidateRole d 15)
          (quota := d2FlowCandidateQuota d 15)
          (h := childDepth + 2) (i := 4)
          (G := G4) (low := low4) (high := high4) children4 hactive15_4 s]
        cases hchild : children4 s with
        | node G5 low5 high5 children5 =>
            have ha5 : d2FlowCandidateActive d 15 5 = true :=
              (d2FlowCandidateActive_stage15_at hd14).2.2.1
            have hr5 : d2FlowCandidateRole d 15 5 = .mid :=
              d2FlowCandidateRole_stage15_internal_mid hd14 5 (Or.inr rfl)
            have hroot : d2FlowTreeRootDeficit
                (d2FlowStage (d2FlowCandidateActive d 15)
                  (d2FlowCandidateRole d 15) (d2FlowCandidateQuota d 15)
                  (childDepth + 2) 5 (.node G5 low5 high5 children5)) =
                G5 + d2FlowCandidateQuota d 15 5 .mid := by
              rw [d2FlowStage_active_node_deficit
                (active := d2FlowCandidateActive d 15)
                (role := d2FlowCandidateRole d 15)
                (quota := d2FlowCandidateQuota d 15)
                (h := childDepth + 1) (i := 5) (G := G5)
                (low := low5) (high := high5) children5 ha5, hr5]
            rw [hroot]
            omega
  have hquotaCap : 256 * d2FlowCandidateQuota d 16 4 .mid <=
      d2FlowCandidateCapacity d 4 16 := by
    have hactiveRaw : active d (tfD2 d) 4 16 := by
      have hm := d2FlowCandidateActive_matches_schedule
        (d := d) (i := 4) (t := 16) (by omega)
      rw [hactive4] at hm
      exact of_decide_eq_true hm.symm
    have hrSchedule : d2ScheduleRole d 4 16 = .mid := by
      have hm := d2FlowCandidateRole_matches_schedule
        (d := d) (i := 4) (t := 16) (by omega)
      exact hm.symm.trans hrole4
    have hregular : d2ScheduleRole d 4 16 = .topRise \/
        d2ScheduleRole d 4 16 = .mid \/
        d2ScheduleRole d 4 16 = .botDesc := Or.inr (Or.inl hrSchedule)
    have h := d2FlowCandidateQuota_le_capacity_div_256 (by omega) hactiveRaw hregular
    simpa [hrSchedule] using h
  have heven : d2FlowCandidateQuota d 16 4 .mid % 2 = 0 := by
    have hactiveRaw : active d (tfD2 d) 4 16 := by
      have hm := d2FlowCandidateActive_matches_schedule
        (d := d) (i := 4) (t := 16) (by omega)
      rw [hactive4] at hm
      exact of_decide_eq_true hm.symm
    have hrSchedule : d2ScheduleRole d 4 16 = .mid := by
      have hm := d2FlowCandidateRole_matches_schedule
        (d := d) (i := 4) (t := 16) (by omega)
      exact hm.symm.trans hrole4
    have hregular : d2ScheduleRole d 4 16 = .topRise \/
        d2ScheduleRole d 4 16 = .mid \/
        d2ScheduleRole d 4 16 = .botDesc := Or.inr (Or.inl hrSchedule)
    have h := d2FlowCandidateQuota_even (by omega) hactiveRaw (by omega) hregular
    simpa [hrSchedule, d2FlowCandidateRole] using h
  have hq5relation : 128 * d2FlowCandidateQuota d 15 5 .mid =
      15 * d2FlowCandidateCapacity d 4 16 := by
    have hcap : d2FlowCandidateCapacity d 4 16 = 2 ^ (3 * d - 11) := by
      simp [d2FlowCandidateCapacity, d2FlowCandidateCapacityExponent]
      omega
    have hq : d2FlowCandidateQuota d 15 5 .mid =
        15 * 2 ^ (3 * d - 18) := by
      simp [d2FlowCandidateQuota, d2FlowCandidateCapacityExponent]
      omega
    rw [hcap, hq]
    rw [show 3 * d - 11 = 7 + (3 * d - 18) by omega, pow_add]
    ring
  have hleft : d2FlowCandidateCapacity d 4 16 <=
      128 * d2FlowTreeRootDeficit
        (d2FlowTreeChild tree (Fin.mk 0 (by omega))) := by
    have hf := hq5floor (Fin.mk 0 (by omega))
    have hcq : d2FlowCandidateCapacity d 4 16 <=
        128 * d2FlowCandidateQuota d 15 5 .mid := by
      nlinarith [hq5relation]
    exact le_trans hcq (Nat.mul_le_mul_left 128 hf)
  have hright : d2FlowCandidateCapacity d 4 16 <=
      128 * d2FlowTreeRootDeficit
        (d2FlowTreeChild tree (Fin.mk 7 (by omega))) := by
    have hf := hq5floor (Fin.mk 7 (by omega))
    have hcq : d2FlowCandidateCapacity d 4 16 <=
        128 * d2FlowCandidateQuota d 15 5 .mid := by
      nlinarith [hq5relation]
    exact le_trans hcq (Nat.mul_le_mul_left 128 hf)
  have htotalLower : 8 * d2FlowCandidateQuota d 15 5 .mid <=
      d2FlowTotal (fun s : Fin 8 =>
        d2FlowTreeRootDeficit (d2FlowTreeChild tree s)) := by
    change 8 * d2FlowCandidateQuota d 15 5 .mid <=
      Finset.univ.sum (fun s : Fin 8 =>
        d2FlowTreeRootDeficit (d2FlowTreeChild tree s))
    calc
      8 * d2FlowCandidateQuota d 15 5 .mid =
          Finset.univ.sum (fun _ : Fin 8 => d2FlowCandidateQuota d 15 5 .mid) := by simp
      _ <= Finset.univ.sum (fun s : Fin 8 =>
          d2FlowTreeRootDeficit (d2FlowTreeChild tree s)) := by
        apply Finset.sum_le_sum
        intro s hs
        exact hq5floor s
  have halloc : d2FlowCandidateQuota d 16 4 .mid <=
      d2FlowTotal (fun s => d2FlowTreeRootDeficit (d2FlowTreeChild tree s)) -
        d2FlowTreeRootDeficit tree := by
    have hbudget : d2FlowCandidateQuota d 16 4 .mid +
        d2FlowTreeRootDeficit tree <=
        8 * d2FlowCandidateQuota d 15 5 .mid := by
      nlinarith [hquotaCap, hrootcap, hq5relation]
    omega
  have hchildren : forall s : Fin 8,
      d2FlowStageInvInputs 8192
        (d2FlowCandidateActive d 16) (d2FlowCandidateRole d 16)
        (d2FlowCandidateQuota d 16)
        (fun x => d2FlowCandidateCapacity d x 16) 5
        (d2FlowTreeChild tree s) := by
    intro s
    have hf : d2FlowCandidateActive d 16 5 = false := by
      cases h : d2FlowCandidateActive d 16 5 with
      | false => rfl
      | true =>
          have hlev := (d2FlowCandidateActive_stage16_iff hd14).mp h
          by_cases h14 : d = 14 <;> simp [h14] at hlev <;> omega
    exact d2FlowStageInvInputs_inactive_of_children
      (active := d2FlowCandidateActive d 16)
      (role := d2FlowCandidateRole d 16)
      (quota := d2FlowCandidateQuota d 16)
      (cap := fun x => d2FlowCandidateCapacity d x 16)
      8192 5 (d2FlowTreeChild tree s) hf (by
        intro t
        exact d2FlowCandidateRun_stage16_levelSix_inputs
          childDepth hd j k m l s t)
  have hcontract := d2FlowStageInvInputs_mid_of_contract
    (scale := 8192) (i := 4) tree hactive4 hrole4 hchildren
    hbalance hrootcap hquotaCap halloc heven hleft hright
  simpa [d, initial, run15, run16, tree] using hcontract

end Chvatal.D2Reserve
