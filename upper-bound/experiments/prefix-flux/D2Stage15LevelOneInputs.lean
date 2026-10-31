import D2Stage15LevelThreeInputs
import D2Stage15LevelOneContract
import D2Stage15Frontier
import D2Stage14Contract

namespace Chvatal.D2Reserve

attribute [local irreducible] d2FlowStageInvInputs

set_option maxHeartbeats 20000000
set_option maxRecDepth 4096

/-- Assemble the full Stage-15 input contract at every actual level-one
sender. The startup case is a root reset; subsequent depths use the
top-rising quota and endpoint reserves. In both cases, level two is inactive
and its level-three descendants satisfy the checked contract. -/
theorem d2FlowCandidateRun_stage15_levelOne_inputs
    (childDepth : Nat) (hd : 7 <= childDepth) (j : Fin 8) :
    let d := childDepth + 7
    let initial := d2FlowTreeInitial 8192 d
    let run15 := d2FlowCandidateRun d initial 15
    let tree := d2FlowTreeChild run15 j
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 15) (d2FlowCandidateRole d 15)
      (d2FlowCandidateQuota d 15)
      (fun i => d2FlowCandidateCapacity d i 15) 1 tree := by
  classical
  let d := childDepth + 7
  let run15 := d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 15
  let tree := d2FlowTreeChild run15 j
  have hd' : 14 <= d := by dsimp [d]; omega
  have hactive : d2FlowCandidateActive d 15 1 = true :=
    (d2FlowCandidateActive_stage15_at hd').1
  have hchildren : forall k : Fin 8,
      d2FlowStageInvInputs 8192
        (d2FlowCandidateActive d 15) (d2FlowCandidateRole d 15)
        (d2FlowCandidateQuota d 15)
        (fun i => d2FlowCandidateCapacity d i 15) 2
        (d2FlowTreeChild tree k) := by
    intro k
    apply d2FlowStageInvInputs_inactive_of_children 8192 2
      (d2FlowTreeChild tree k)
    · have hfalse : d2FlowCandidateActive d 15 2 = false := by
        cases hvalue : d2FlowCandidateActive d 15 2 with
        | false => rfl
        | true =>
            have hlevel := d2FlowCandidateActive_stage15_level_bound hvalue
            rcases hlevel with h | h | h | h <;> omega
      exact hfalse
    · intro l
      exact d2FlowCandidateRun_stage15_levelThree_inputs
        childDepth hd j k l
  have hdata : d2FlowTreeRootData tree = (0, 0, 0) := by
    exact d2FlowCandidateRun_stage15_levelOne_child_rootdata_zero
      childDepth hd j
  have hzero : d2FlowTreeRootDeficit tree = 0 := by
    rw [← d2FlowTreeRootData_fst_eq_deficit]
    rw [hdata]
  have hbalance : (d2FlowTreeRootData tree).2.1 +
      (d2FlowTreeRootData tree).2.2 = d2FlowTreeRootDeficit tree := by
    rw [hdata, hzero]
    rfl
  have hroleCase := d2FlowCandidateRole_stage15_top hd'
  by_cases hstartup : d = 14
  · have hrole : d2FlowCandidateRole d 15 1 = .topDesc := by
      rw [hroleCase]
      simp [hstartup]
    exact d2FlowStageInvInputs_topDesc_of_contract 8192 1 tree
      hactive hrole hchildren hbalance hzero
  · have hrole : d2FlowCandidateRole d 15 1 = .topRise := by
      rw [hroleCase]
      simp [hstartup]
    have harith := d2FlowCandidateStage15_levelOne_quota_arithmetic hd'
    have hquotaCap : 256 * d2FlowCandidateQuota d 15 1 .topRise <=
        d2FlowCandidateCapacity d 1 15 := by
      have h := harith.1
      omega
    have heven : d2FlowCandidateQuota d 15 1 .topRise % 2 = 0 := by
      have h := harith.2.2.2.2
      exact h
    have hfloor : forall k : Fin 8,
        d2FlowCandidateQuota d 14 2 .mid <=
          d2FlowTreeRootDeficit (d2FlowTreeChild tree k) := by
      intro k
      exact d2FlowCandidateRun_stage15_levelOne_child_floor
        childDepth hd j k
    have hcover : d2FlowCandidateQuota d 15 1 .topRise <=
        8 * d2FlowCandidateQuota d 14 2 .mid := by
      have h := harith.2.2.1
      exact h
    have hsum : 8 * d2FlowCandidateQuota d 14 2 .mid <=
        d2FlowTotal (fun k =>
          d2FlowTreeRootDeficit (d2FlowTreeChild tree k)) := by
      change 8 * d2FlowCandidateQuota d 14 2 .mid <=
        Finset.univ.sum (fun k : Fin 8 =>
          d2FlowTreeRootDeficit (d2FlowTreeChild tree k))
      calc
        8 * d2FlowCandidateQuota d 14 2 .mid =
            Finset.univ.sum (fun _ : Fin 8 =>
              d2FlowCandidateQuota d 14 2 .mid) := by simp
        _ <= Finset.univ.sum (fun k : Fin 8 =>
            d2FlowTreeRootDeficit (d2FlowTreeChild tree k)) := by
          apply Finset.sum_le_sum
          intro k hk
          exact hfloor k
    have halloc : d2FlowCandidateQuota d 15 1 .topRise <=
        d2FlowTotal (fun k =>
          d2FlowTreeRootDeficit (d2FlowTreeChild tree k)) -
          d2FlowTreeRootDeficit tree := by
      rw [hzero]
      omega
    have hreserve : d2FlowCandidateCapacity d 1 15 <=
        128 * d2FlowCandidateQuota d 14 2 .mid := by
      have h := harith.2.2.2.1
      exact h
    have hleft : d2FlowCandidateCapacity d 1 15 <=
        128 * d2FlowTreeRootDeficit
          (d2FlowTreeChild tree ⟨0, by omega⟩) := by
      have hf := hfloor ⟨0, by omega⟩
      omega
    have hright : d2FlowCandidateCapacity d 1 15 <=
        128 * d2FlowTreeRootDeficit
          (d2FlowTreeChild tree ⟨7, by omega⟩) := by
      have hf := hfloor ⟨7, by omega⟩
      omega
    exact d2FlowStageInvInputs_topRise_of_contract 8192 1 tree
      hactive hrole hchildren hbalance (by simp [hzero]) hquotaCap
      halloc heven hleft hright

end Chvatal.D2Reserve
