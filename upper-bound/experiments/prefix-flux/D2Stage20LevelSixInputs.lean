import D2Stage20LevelEightInputs
import D2Stage19LevelFiveInputs
import D2Stage18PreservesInv
import D2Stage14Contract

namespace Chvatal.D2Reserve

attribute [local irreducible] d2FlowStageInvInputs
attribute [local irreducible] d2FlowTreeInv
attribute [local irreducible] d2FlowCandidateRun

set_option maxHeartbeats 20000000
set_option maxRecDepth 4096

private theorem d2FlowTreeInv_child_stage20s
    {scale h : Nat} (tree : D2FlowTree (h + 1))
    (hinv : d2FlowTreeInv scale tree) (j : Fin 8) :
    d2FlowTreeInv scale (d2FlowTreeChild tree j) := by
  cases tree with
  | node G low high children =>
      have hx := hinv
      simp only [d2FlowTreeInv] at hx
      simpa using hx.2.2.2 j

/-- The actual Stage-20 level-six middle senders satisfy their input contract.
Their root cap and balance come from Stage 19's level-five regular cut; the
level-seven children receive the Stage-19 bottom quota, and their level-eight
contracts are the checked Stage-20 bottom gate. -/
theorem d2FlowCandidateRun_stage20_levelSix_inputs
    (childDepth : Nat) (hd : 6 <= childDepth)
    (j k m l q r : Fin 8) :
    let d := childDepth + 10
    let run20 := d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 20
    let tree := d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild run20 j) k) m) l) q) r
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 20) (d2FlowCandidateRole d 20)
      (d2FlowCandidateQuota d 20)
      (fun x => d2FlowCandidateCapacity d x 20) 6 tree := by
  classical
  let d := childDepth + 10
  let initial := d2FlowTreeInitial 8192 d
  let run19 := d2FlowCandidateRun d initial 19
  let run20 := d2FlowCandidateRun d initial 20
  let parent := d2FlowTreeChild
    (d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild run19 j) k) m) l) q
  let tree := d2FlowTreeChild
    (d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild run20 j) k) m) l) q) r
  have hd16 : 16 <= d := by dsimp [d]; omega
  have hd14 : 14 <= d := by omega
  have hd15 : 15 <= d := by omega
  have hactive20 : d2FlowCandidateActive d 20 6 = true := by
    apply (d2FlowCandidateActive_stage20_iff hd16).2
    by_cases h16 : d = 16 <;> simp [h16]
  have hrole20 : d2FlowCandidateRole d 20 6 = .mid := by
    apply d2FlowCandidateRole_stage20_mid hd16
    · by_cases h16 : d = 16 <;> simp [h16]
    · omega
  have hactive19 : d2FlowCandidateActive d 19 5 = true := by
    apply (d2FlowCandidateActive_stage19_iff hd14).2
    by_cases hsmall : d <= 15 <;> simp [hsmall] <;> omega
  have hrole19 : d2FlowCandidateRole d 19 5 = .mid := by
    apply d2FlowCandidateRole_stage19_mid hd14
    · by_cases hsmall : d <= 15 <;> simp [hsmall] <;> omega
    · omega
  have hregular19 : d2FlowCandidateRole d 19 5 = .topRise \/
      d2FlowCandidateRole d 19 5 = .mid \/
      d2FlowCandidateRole d 19 5 = .botDesc := Or.inr (Or.inl hrole19)
  have hinv19 : d2FlowTreeInv 8192 run19 := by
    simpa [d, initial, run19] using
      d2FlowCandidateStage18_preserves_inv (childDepth + 3) (by omega)
  have hinvParent : d2FlowTreeInv 8192 parent := by
    have h1 := d2FlowTreeInv_grandchild run19 hinv19 j k
    have h2 := d2FlowTreeInv_grandchild
      (d2FlowTreeChild (d2FlowTreeChild run19 j) k) h1 m l
    simpa [parent] using d2FlowTreeInv_child_stage20s
      (d2FlowTreeChild
        (d2FlowTreeChild (d2FlowTreeChild (d2FlowTreeChild run19 j) k) m) l) h2 q
  have hparentInputs := d2FlowCandidateRun_stage19_levelFive_inputs
    (childDepth + 1) (by omega) j k m l q
  have hparentInputs' : d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 19) (d2FlowCandidateRole d 19)
      (d2FlowCandidateQuota d 19)
      (fun x => d2FlowCandidateCapacity d x 19) 5 parent := by
    simpa [d, initial, run19, parent] using hparentInputs
  have hrun20 : run20 = d2FlowCandidateStage d 19 run19 := by
    change d2FlowCandidateRun d initial 20 =
      d2FlowCandidateStage d 19 (d2FlowCandidateRun d initial 19)
    rw [d2FlowCandidateRun.eq_def]
  have htreeEq : tree = d2FlowTreeChild
      (d2FlowStage (d2FlowCandidateActive d 19)
        (d2FlowCandidateRole d 19) (d2FlowCandidateQuota d 19)
        (childDepth + 5) 5 parent) r := by
    dsimp only [tree]
    rw [hrun20]
    simp only [d2FlowCandidateStage]
    exact d2FlowStage_path6_tree_projection
      (active := d2FlowCandidateActive d 19)
      (role := d2FlowCandidateRole d 19)
      (quota := d2FlowCandidateQuota d 19)
      (h := childDepth + 4) (i := 0) run19 j k m l q r
  have hchildBound := d2FlowStage_regular_child_g_bound_of_tree_inputs
    (active := d2FlowCandidateActive d 19)
    (role := d2FlowCandidateRole d 19)
    (quota := d2FlowCandidateQuota d 19)
    (cap := fun x => d2FlowCandidateCapacity d x 19)
    (stageDepth := childDepth + 4) (i := 5) parent
    hactive19 hregular19 hinvParent hparentInputs'
  have hcapShift : d2FlowCandidateCapacity d 6 20 =
      2 * d2FlowCandidateCapacity d 5 19 :=
    d2FlowCandidateCapacity_succ_level_next_stage d 5 19 (by omega)
  have hrootcap : 512 * d2FlowTreeRootDeficit tree <=
      d2FlowCandidateCapacity d 6 20 := by
    have hc := hchildBound r
    rw [htreeEq, hcapShift]
    exact hc
  have hbalance : (d2FlowTreeRootData tree).2.1 +
      (d2FlowTreeRootData tree).2.2 = d2FlowTreeRootDeficit tree := by
    cases hp : parent with
    | node G low high children =>
        have hb := d2FlowStage_regular_child_balanced
          (active := d2FlowCandidateActive d 19)
          (role := d2FlowCandidateRole d 19)
          (quota := d2FlowCandidateQuota d 19)
          (h := childDepth + 4) (i := 5) (G := G)
          (low := low) (high := high) children hactive19
          hregular19 r
        simpa [htreeEq, hp] using hb
  have hquotaCap : 256 * d2FlowCandidateQuota d 20 6 .mid <=
      d2FlowCandidateCapacity d 6 20 := by
    have hmatch := d2FlowCandidateActive_matches_schedule
      (d := d) (i := 6) (t := 20) (by omega)
    rw [hactive20] at hmatch
    have hschedActive : active d (tfD2 d) 6 20 := of_decide_eq_true hmatch.symm
    have hschedRole : d2ScheduleRole d 6 20 = .mid := by
      simpa [d2FlowCandidateRole] using hrole20
    have hq := d2FlowCandidateQuota_le_capacity_div_256
      (by omega) hschedActive (Or.inr (Or.inl hschedRole))
    simpa [hrole20, hschedRole] using hq
  have heven : d2FlowCandidateQuota d 20 6 .mid % 2 = 0 := by
    have hmatch := d2FlowCandidateActive_matches_schedule
      (d := d) (i := 6) (t := 20) (by omega)
    rw [hactive20] at hmatch
    have hschedActive : active d (tfD2 d) 6 20 := of_decide_eq_true hmatch.symm
    have hschedRole : d2ScheduleRole d 6 20 = .mid := by
      simpa [d2FlowCandidateRole] using hrole20
    have he := d2FlowCandidateQuota_even (by omega) hschedActive
      (by omega) (Or.inr (Or.inl hschedRole))
    simpa [hrole20] using he
  have hquotaFloor : d2FlowCandidateQuota d 19 7 .botDesc =
      15 * 2 ^ (3 * d - 20) := by
    change 15 * 2 ^ (d2FlowCandidateCapacityExponent d 7 19 - 12) = _
    have he : d2FlowCandidateCapacityExponent d 7 19 = 3 * d - 8 := by
      simp [d2FlowCandidateCapacityExponent]
      omega
    rw [he]
    congr 1 <;> omega
  have hcapMass : d2FlowCandidateCapacity d 6 20 = 2 ^ (3 * d - 13) := by
    change 2 ^ d2FlowCandidateCapacityExponent d 6 20 = _
    have he : d2FlowCandidateCapacityExponent d 6 20 = 3 * d - 13 := by
      simp [d2FlowCandidateCapacityExponent]
      omega
    rw [he]
  have hfloor : ∀ v : Fin 8,
      d2FlowCandidateQuota d 19 7 .botDesc <=
        d2FlowTreeRootDeficit (d2FlowTreeChild tree v) := by
    intro v
    dsimp only [tree]
    let path6 := d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild run19 j) k) m) l) q) r
    have hproj : d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild
                  (d2FlowTreeChild run20 j) k) m) l) q) r) v =
        d2FlowTreeChild
          (d2FlowStage (d2FlowCandidateActive d 19)
            (d2FlowCandidateRole d 19) (d2FlowCandidateQuota d 19)
            (childDepth + 4) 6 path6) v := by
      rw [hrun20]
      simp only [d2FlowCandidateStage]
      exact d2FlowStage_path7_child_projection
        (active := d2FlowCandidateActive d 19)
        (role := d2FlowCandidateRole d 19)
        (quota := d2FlowCandidateQuota d 19)
        (h := childDepth + 3) (i := 0) run19 j k m l q r v
    have hfalse6 : d2FlowCandidateActive d 19 6 = false := by
      cases h : d2FlowCandidateActive d 19 6 with
      | false => rfl
      | true =>
          have hs := (d2FlowCandidateActive_stage19_iff (i := 6) hd14).mp h
          by_cases hsmall : d <= 15 <;> simp [hsmall] at hs <;> omega
    cases hp : path6 with
    | node G6 low6 high6 children6 =>
        have hstep := d2FlowStage_inactive_child
          (active := d2FlowCandidateActive d 19)
          (role := d2FlowCandidateRole d 19)
          (quota := d2FlowCandidateQuota d 19)
          (h := childDepth + 3) (i := 6) (G := G6)
          (low := low6) (high := high6) children6 hfalse6 v
        have hchildStage : d2FlowTreeChild
            (d2FlowStage (d2FlowCandidateActive d 19)
              (d2FlowCandidateRole d 19) (d2FlowCandidateQuota d 19)
              (childDepth + 4) 6 (.node G6 low6 high6 children6)) v =
            d2FlowStage (d2FlowCandidateActive d 19)
              (d2FlowCandidateRole d 19) (d2FlowCandidateQuota d 19)
              (childDepth + 3) 7 (children6 v) := by
          simpa using hstep
        cases hc : children6 v with
        | node G7 low7 high7 children7 =>
            have hactive7 : d2FlowCandidateActive d 19 7 = true := by
              apply (d2FlowCandidateActive_stage19_iff (i := 7) hd14).2
              by_cases hsmall : d <= 15 <;> simp [hsmall]
            have hrole7 : d2FlowCandidateRole d 19 7 = .botDesc :=
              d2FlowCandidateRole_stage19_bottom hd14
            have hdef := d2FlowStage_active_node_deficit
              (active := d2FlowCandidateActive d 19)
              (role := d2FlowCandidateRole d 19)
              (quota := d2FlowCandidateQuota d 19)
              (h := childDepth + 2) (i := 7) (G := G7)
              (low := low7) (high := high7) children7 hactive7
            have hDef' : d2FlowTreeRootDeficit
                (d2FlowStage (d2FlowCandidateActive d 19)
                  (d2FlowCandidateRole d 19) (d2FlowCandidateQuota d 19)
                  (childDepth + 3) 7 (children6 v)) =
                G7 + d2FlowCandidateQuota d 19 7 .botDesc := by
              simpa [hc, hrole7] using hdef
            have hG : d2FlowTreeRootDeficit (children6 v) = G7 := by
              simpa [hc, d2FlowTreeRootDeficit] using rfl
            rw [hproj, hp, hchildStage, hDef']
            omega
  have hleft : d2FlowCandidateCapacity d 6 20 <=
      128 * d2FlowTreeRootDeficit
        (d2FlowTreeChild tree (Fin.mk 0 (by omega))) := by
    rw [hcapMass]
    have hf := hfloor (Fin.mk 0 (by omega))
    rw [hquotaFloor] at hf
    have he : 3 * d - 13 = 7 + (3 * d - 20) := by omega
    rw [he, pow_add]
    norm_num at * <;> nlinarith
  have hright : d2FlowCandidateCapacity d 6 20 <=
      128 * d2FlowTreeRootDeficit
        (d2FlowTreeChild tree (Fin.mk 7 (by omega))) := by
    rw [hcapMass]
    have hf := hfloor (Fin.mk 7 (by omega))
    rw [hquotaFloor] at hf
    have he : 3 * d - 13 = 7 + (3 * d - 20) := by omega
    rw [he, pow_add]
    norm_num at * <;> nlinarith
  have htotal : 8 * d2FlowCandidateQuota d 19 7 .botDesc <=
      d2FlowTotal (fun v => d2FlowTreeRootDeficit (d2FlowTreeChild tree v)) := by
    change 8 * d2FlowCandidateQuota d 19 7 .botDesc <=
      Finset.univ.sum (fun v : Fin 8 => d2FlowTreeRootDeficit (d2FlowTreeChild tree v))
    calc
      8 * d2FlowCandidateQuota d 19 7 .botDesc =
          Finset.univ.sum (fun _ : Fin 8 => d2FlowCandidateQuota d 19 7 .botDesc) := by simp
      _ <= Finset.univ.sum (fun v : Fin 8 => d2FlowTreeRootDeficit (d2FlowTreeChild tree v)) := by
        apply Finset.sum_le_sum
        intro v hv
        exact hfloor v
  have halloc : d2FlowCandidateQuota d 20 6 .mid <=
      d2FlowTotal (fun v => d2FlowTreeRootDeficit (d2FlowTreeChild tree v)) -
        d2FlowTreeRootDeficit tree := by
    have hbudget : d2FlowCandidateQuota d 20 6 .mid +
        d2FlowTreeRootDeficit tree <= 8 * d2FlowCandidateQuota d 19 7 .botDesc := by
      rw [hquotaFloor]
      have hG : 512 * d2FlowTreeRootDeficit tree <=
          d2FlowCandidateCapacity d 6 20 := hrootcap
      rw [hcapMass] at hG
      have hq : d2FlowCandidateQuota d 20 6 .mid =
          15 * 2 ^ (3 * d - 25) := by
        change 15 * 2 ^ (d2FlowCandidateCapacityExponent d 6 20 - 12) = _
        rw [show d2FlowCandidateCapacityExponent d 6 20 = 3 * d - 13 by
          simp [d2FlowCandidateCapacityExponent]; omega]
        congr 1 <;> omega
      rw [hq]
      have hpow : 2 ^ (3 * d - 13) = 4096 * 2 ^ (3 * d - 25) := by
        have he : 3 * d - 13 = 12 + (3 * d - 25) := by omega
        rw [he, pow_add]
        norm_num
      have hpowFloor : 2 ^ (3 * d - 20) = 32 * 2 ^ (3 * d - 25) := by
        have he : 3 * d - 20 = 5 + (3 * d - 25) := by omega
        rw [he, pow_add]
        norm_num
      rw [hpowFloor]
      rw [hpow] at hG
      nlinarith [Nat.zero_le (2 ^ (3 * d - 25))]
    omega
  have hchildren : ∀ v : Fin 8,
      d2FlowStageInvInputs 8192
        (d2FlowCandidateActive d 20) (d2FlowCandidateRole d 20)
        (d2FlowCandidateQuota d 20)
        (fun x => d2FlowCandidateCapacity d x 20) 7
        (d2FlowTreeChild tree v) := by
    intro v
    have hfalse7 : d2FlowCandidateActive d 20 7 = false := by
      cases h : d2FlowCandidateActive d 20 7 with
      | false => rfl
      | true =>
          have hs := (d2FlowCandidateActive_stage20_iff (d := d) (i := 7) hd16).mp h
          by_cases h16 : d = 16 <;> simp [h16] at hs <;> omega
    apply d2FlowStageInvInputs_inactive_of_children
      (active := d2FlowCandidateActive d 20)
      (role := d2FlowCandidateRole d 20)
      (quota := d2FlowCandidateQuota d 20)
      (cap := fun x => d2FlowCandidateCapacity d x 20) 8192 7
      (d2FlowTreeChild tree v) hfalse7
    intro w
    simpa [d, initial, run20, tree] using
      d2FlowCandidateRun_stage20_levelEight_inputs childDepth hd j k m l q r v w
  have hcontract := d2FlowStageInvInputs_mid_of_contract
    (scale := 8192) (i := 6) tree hactive20 hrole20 hchildren
    hbalance hrootcap hquotaCap halloc heven hleft hright
  simpa [d, initial, run20, tree] using hcontract

end Chvatal.D2Reserve
