import D2Stage15LevelSevenBalance
import D2Stage15InactiveTail

namespace Chvatal.D2Reserve

attribute [local irreducible] d2FlowStageInvInputs

set_option maxHeartbeats 20000000
set_option maxRecDepth 4096

/-- The complete recursive input contract at every actual level-seven sender
on stage 15. Its descendants are inactive, and the actual stage-14 cut supplies
the balance required by the level-seven bot-rise role. -/
theorem d2FlowCandidateRun_stage15_levelSeven_inputs
    (childDepth : Nat) (hd : 7 <= childDepth)
    (j k m l q r s : Fin 8) :
    let d := childDepth + 7
    let initial := d2FlowTreeInitial 8192 d
    let run15 := d2FlowCandidateRun d initial 15
    let tree := d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild run15 j) k) m) l) q) r) s
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 15) (d2FlowCandidateRole d 15)
      (d2FlowCandidateQuota d 15)
      (fun i => d2FlowCandidateCapacity d i 15) 7 tree := by
  obtain ⟨height, rfl⟩ : ∃ height, childDepth = height + 1 :=
    ⟨childDepth - 1, by omega⟩
  let d := (height + 1) + 7
  let initial := d2FlowTreeInitial 8192 d
  let run15 := d2FlowCandidateRun d initial 15
  let tree := d2FlowTreeChild
    (d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild run15 j) k) m) l) q) r) s
  have hd' : 14 <= d := by dsimp [d]; omega
  have hactive : d2FlowCandidateActive d 15 7 = true :=
    (d2FlowCandidateActive_stage15_at (d := d) hd').2.2.2
  have hrole : d2FlowCandidateRole d 15 7 = .botRise :=
    d2FlowCandidateRole_stage15_bottom (d := d) hd'
  have hbalance := d2FlowCandidateRun_stage15_levelSeven_balanced
    (height + 1) (by omega) j k m l q r s
  have hchildren : forall u : Fin 8,
      d2FlowStageInvInputs 8192
        (d2FlowCandidateActive d 15) (d2FlowCandidateRole d 15)
        (d2FlowCandidateQuota d 15)
        (fun i => d2FlowCandidateCapacity d i 15) 8
        (d2FlowTreeChild tree u) := by
    intro u
    exact d2FlowCandidateStage15_inactive_tail_inputs d 8 (by omega)
      (d2FlowTreeChild tree u)
  exact d2FlowStageInvInputs_botRise_of_contract
    8192 7 tree hactive hrole hchildren hbalance

end Chvatal.D2Reserve
