import D2Stage19LevelOneFloor
import D2Stage19LevelThreeInputs
import D2Stage18Frontier
import D2Stage19Frontier
import D2Stage14Contract

namespace Chvatal.D2Reserve

attribute [local irreducible] d2FlowStageInvInputs
attribute [local irreducible] d2FlowCandidateRun

set_option maxHeartbeats 20000000
set_option maxRecDepth 4096

/-- Stage 19's top-band input contract. At depth sixteen the sender is
top-descending and inherits an exact-zero root from Stage 18. From depth
seventeen onward it is top-rising; the Stage-18 level-two middle quota gives
its endpoint and aggregate reserves. -/
theorem d2FlowCandidateRun_stage19_levelOne_inputs
    (childDepth : Nat) (hd : 7 <= childDepth) (j : Fin 8) :
    let d := childDepth + 9
    let run19 := d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 19
    let tree := d2FlowTreeChild run19 j
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 19) (d2FlowCandidateRole d 19)
      (d2FlowCandidateQuota d 19)
      (fun x => d2FlowCandidateCapacity d x 19) 1 tree := by
  classical
  let d := childDepth + 9
  let initial := d2FlowTreeInitial 8192 d
  let run18 := d2FlowCandidateRun d initial 18
  let run19 := d2FlowCandidateRun d initial 19
  let tree := d2FlowTreeChild run19 j
  have hd14 : 14 <= d := by dsimp [d]; omega
  have hnotSmall : ¬ d <= 15 := by dsimp [d]; omega
  have hactive19 : d2FlowCandidateActive d 19 1 = true := by
    apply (d2FlowCandidateActive_stage19_iff (i := 1) hd14).2
    simp [hnotSmall]
  have hrun19 : run19 = d2FlowCandidateStage d 18 run18 := by
    change d2FlowCandidateRun d initial 19 =
      d2FlowCandidateStage d 18 (d2FlowCandidateRun d initial 18)
    rw [d2FlowCandidateRun.eq_def]
  have hactive18root : d2FlowCandidateActive d 18 0 = true := by
    apply (d2FlowCandidateActive_stage18_iff (i := 0) hd14).2
    simp [hnotSmall]
  have hrole18root : d2FlowCandidateRole d 18 0 = .topDesc := by
    have ht := d2FlowCandidateRole_stage18_top hd14
    simpa [hnotSmall] using ht
  have hrootData : d2FlowTreeRootData tree = (0, 0, 0) := by
    dsimp only [tree]
    rw [hrun19]
    simp only [d2FlowCandidateStage]
    change D2FlowTree (childDepth + 9) at run18
    cases hr : run18 with
    | node G low high children =>
        have hz := d2FlowStage_topDesc_child_rootdata
          (active := d2FlowCandidateActive d 18)
          (role := d2FlowCandidateRole d 18)
          (quota := d2FlowCandidateQuota d 18)
          (h := childDepth + 8) (i := 0)
          (G := G) (low := low) (high := high) children
          hactive18root hrole18root j
        simpa [hr] using hz
  have hzero : d2FlowTreeRootDeficit tree = 0 := by
    cases ht : tree with
    | node G low high children =>
        have hG : G = 0 := by
          have hp := congrArg Prod.fst hrootData
          simpa [ht, d2FlowTreeRootData] using hp
        simpa [ht, d2FlowTreeRootDeficit] using hG
  have hbalance : (d2FlowTreeRootData tree).2.1 +
      (d2FlowTreeRootData tree).2.2 = d2FlowTreeRootDeficit tree := by
    rw [hrootData, hzero]
    rfl
  have hchildren : ∀ s : Fin 8,
      d2FlowStageInvInputs 8192
        (d2FlowCandidateActive d 19) (d2FlowCandidateRole d 19)
        (d2FlowCandidateQuota d 19)
        (fun x => d2FlowCandidateCapacity d x 19) 2
        (d2FlowTreeChild tree s) := by
    intro s
    have hfalse2 : d2FlowCandidateActive d 19 2 = false := by
      cases h : d2FlowCandidateActive d 19 2 with
      | false => rfl
      | true =>
          have hs := (d2FlowCandidateActive_stage19_iff (i := 2) hd14).mp h
          simp [hnotSmall] at hs
    apply d2FlowStageInvInputs_inactive_of_children
      (active := d2FlowCandidateActive d 19)
      (role := d2FlowCandidateRole d 19)
      (quota := d2FlowCandidateQuota d 19)
      (cap := fun x => d2FlowCandidateCapacity d x 19) 8192 2
      (d2FlowTreeChild tree s) hfalse2
    intro t
    simpa [d, initial, run19, tree] using
      d2FlowCandidateRun_stage19_levelThree_inputs childDepth hd j s t
  by_cases hstartup : childDepth = 7
  · have hrole19 : d2FlowCandidateRole d 19 1 = .topDesc := by
      have ht := d2FlowCandidateRole_stage19_top hd14
      have hd16 : d = 16 := by dsimp [d]; omega
      rw [if_neg hnotSmall] at ht
      simp [hd16] at ht
      rw [hd16]
      exact ht
    have hcontract := d2FlowStageInvInputs_topDesc_of_contract
      (scale := 8192) (i := 1) tree hactive19 hrole19 hchildren hbalance hzero
    simpa [d, initial, run19, tree] using hcontract
  · have hlarge : 17 <= d := by dsimp [d]; omega
    have hrole19 : d2FlowCandidateRole d 19 1 = .topRise := by
      have ht := d2FlowCandidateRole_stage19_top hd14
      have hnot14 : d ≠ 14 := by dsimp [d]; omega
      have hnot16 : d ≠ 16 := by dsimp [d]; omega
      rw [if_neg hnotSmall] at ht
      rw [if_neg hnot14, if_neg hnot16] at ht
      exact ht
    have hfloor : ∀ s : Fin 8,
        d2FlowCandidateQuota d 18 2 .mid <=
          d2FlowTreeRootDeficit (d2FlowTreeChild tree s) := by
      intro s
      simpa [d, initial, run19, tree] using
        d2FlowCandidateRun_stage19_levelOne_child_floor
          (childDepth := childDepth) (by omega) j s
    have hcapMass : d2FlowCandidateCapacity d 1 19 =
        2 ^ (3 * d - 26) := by
      change 2 ^ d2FlowCandidateCapacityExponent d 1 19 = _
      have he : d2FlowCandidateCapacityExponent d 1 19 = 3 * d - 26 := by
        simp [d2FlowCandidateCapacityExponent]
        omega
      rw [he]
    have hfloorValue : d2FlowCandidateQuota d 18 2 .mid =
        15 * 2 ^ (3 * d - 33) := by
      change 15 * 2 ^ (d2FlowCandidateCapacityExponent d 2 18 - 12) = _
      have he : d2FlowCandidateCapacityExponent d 2 18 = 3 * d - 21 := by
        simp [d2FlowCandidateCapacityExponent]
        omega
      rw [he]
      congr 1 <;> omega
    have hleft : d2FlowCandidateCapacity d 1 19 <=
        128 * d2FlowTreeRootDeficit
          (d2FlowTreeChild tree (Fin.mk 0 (by omega))) := by
      have hf := hfloor (Fin.mk 0 (by omega))
      rw [hcapMass]
      have hf' : 15 * 2 ^ (3 * d - 33) <=
          d2FlowTreeRootDeficit (d2FlowTreeChild tree (Fin.mk 0 (by omega))) := by
        simpa [hfloorValue] using hf
      have he : 3 * d - 26 = 7 + (3 * d - 33) := by omega
      rw [he, pow_add]
      norm_num at * <;> nlinarith
    have hright : d2FlowCandidateCapacity d 1 19 <=
        128 * d2FlowTreeRootDeficit
          (d2FlowTreeChild tree (Fin.mk 7 (by omega))) := by
      have hf := hfloor (Fin.mk 7 (by omega))
      rw [hcapMass]
      have hf' : 15 * 2 ^ (3 * d - 33) <=
          d2FlowTreeRootDeficit (d2FlowTreeChild tree (Fin.mk 7 (by omega))) := by
        simpa [hfloorValue] using hf
      have he : 3 * d - 26 = 7 + (3 * d - 33) := by omega
      rw [he, pow_add]
      norm_num at * <;> nlinarith
    have hquotaCap : 256 * d2FlowCandidateQuota d 19 1 .topRise <=
        d2FlowCandidateCapacity d 1 19 := by
      have hmatch := d2FlowCandidateActive_matches_schedule
        (d := d) (i := 1) (t := 19) (by omega)
      rw [hactive19] at hmatch
      have hschedActive : active d (tfD2 d) 1 19 := of_decide_eq_true hmatch.symm
      have hschedRole : d2ScheduleRole d 1 19 = .topRise := by
        simpa [d2FlowCandidateRole] using hrole19
      have hq := d2FlowCandidateQuota_le_capacity_div_256
        (by omega) hschedActive (Or.inl hschedRole)
      simpa [hrole19, hschedRole] using hq
    have heven : d2FlowCandidateQuota d 19 1 .topRise % 2 = 0 := by
      have hmatch := d2FlowCandidateActive_matches_schedule
        (d := d) (i := 1) (t := 19) (by omega)
      rw [hactive19] at hmatch
      have hschedActive : active d (tfD2 d) 1 19 := of_decide_eq_true hmatch.symm
      have hschedRole : d2ScheduleRole d 1 19 = .topRise := by
        simpa [d2FlowCandidateRole] using hrole19
      have he := d2FlowCandidateQuota_even (by omega) hschedActive
        (by omega) (Or.inl hschedRole)
      simpa [hrole19] using he
    have htotal : 8 * d2FlowCandidateQuota d 18 2 .mid <=
        d2FlowTotal (fun s => d2FlowTreeRootDeficit (d2FlowTreeChild tree s)) := by
      change 8 * d2FlowCandidateQuota d 18 2 .mid <=
        Finset.univ.sum (fun s : Fin 8 => d2FlowTreeRootDeficit (d2FlowTreeChild tree s))
      calc
        8 * d2FlowCandidateQuota d 18 2 .mid =
            Finset.univ.sum (fun _ : Fin 8 => d2FlowCandidateQuota d 18 2 .mid) := by simp
        _ <= Finset.univ.sum (fun s : Fin 8 => d2FlowTreeRootDeficit (d2FlowTreeChild tree s)) := by
          apply Finset.sum_le_sum
          intro s hs
          exact hfloor s
    have halloc : d2FlowCandidateQuota d 19 1 .topRise <=
        d2FlowTotal (fun s => d2FlowTreeRootDeficit (d2FlowTreeChild tree s)) -
          d2FlowTreeRootDeficit tree := by
      have hq19 : d2FlowCandidateQuota d 19 1 .topRise =
          2 ^ (3 * d - 34) := by
        change 2 ^ (d2FlowCandidateCapacityExponent d 1 19 - 8) = _
        have he : d2FlowCandidateCapacityExponent d 1 19 = 3 * d - 26 := by
          simp [d2FlowCandidateCapacityExponent]
          omega
        rw [he]
        congr 1 <;> omega
      have hquotaRelation : d2FlowCandidateQuota d 18 2 .mid =
          30 * d2FlowCandidateQuota d 19 1 .topRise := by
        rw [hq19, hfloorValue]
        have he : 3 * d - 33 = (3 * d - 34) + 1 := by omega
        rw [he, pow_succ]
        ring
      rw [hzero]
      have hbudget : d2FlowCandidateQuota d 19 1 .topRise <=
          8 * d2FlowCandidateQuota d 18 2 .mid := by
        rw [hquotaRelation]
        omega
      omega
    have hcontract := d2FlowStageInvInputs_topRise_of_contract
      (scale := 8192) (i := 1) tree hactive19 hrole19 hchildren
      hbalance (by rw [hzero]; omega)
      hquotaCap halloc heven hleft hright
    simpa [d, initial, run19, tree] using hcontract

end Chvatal.D2Reserve
