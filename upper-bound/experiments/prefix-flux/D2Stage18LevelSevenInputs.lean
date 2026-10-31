import D2Stage18LevelEightInputs

namespace Chvatal.D2Reserve

attribute [local irreducible] d2FlowStageInvInputs
attribute [local irreducible] d2FlowCandidateRun

set_option maxHeartbeats 12000000
set_option maxRecDepth 4096

/-- Level seven is inactive at Stage 18; its level-eight children satisfy the
checked bottom-rise contract. -/
theorem d2FlowCandidateRun_stage18_levelSeven_inputs
    (childDepth : Nat) (hd : 7 <= childDepth)
    (j k m l q r s : Fin 8) :
    let d := childDepth + 7
    let run18 := d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 18
    let tree := d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild run18 j) k) m) l) q) r) s
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 18) (d2FlowCandidateRole d 18)
      (d2FlowCandidateQuota d 18)
      (fun x => d2FlowCandidateCapacity d x 18) 7 tree := by
  obtain ⟨height, rfl⟩ : ∃ height, childDepth = height + 1 :=
    ⟨childDepth - 1, by omega⟩
  let childDepth := height + 1
  let d := height + 8
  let initial := d2FlowTreeInitial 8192 d
  let run18 : D2FlowTree (height + 8) := d2FlowCandidateRun d initial 18
  let tree := d2FlowTreeChild
    (d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild run18 j) k) m) l) q) r) s
  have hd14 : 14 <= d := by dsimp [d]; omega
  have hfalse : d2FlowCandidateActive d 18 7 = false := by
    apply Bool.eq_false_of_not_eq_true
    intro ht
    have hlevels := (d2FlowCandidateActive_stage18_iff hd14).mp ht
    by_cases hsmall : d <= 15 <;> simp [hsmall] at hlevels <;> omega
  apply d2FlowStageInvInputs_inactive_of_children
    (active := d2FlowCandidateActive d 18)
    (role := d2FlowCandidateRole d 18)
    (quota := d2FlowCandidateQuota d 18)
    (cap := fun x => d2FlowCandidateCapacity d x 18)
    8192 7 tree hfalse
  intro u
  have hu := d2FlowCandidateRun_stage18_levelEight_inputs
    height (by omega) j k m l q r s u
  simpa [d, initial, run18, tree] using hu

end Chvatal.D2Reserve
