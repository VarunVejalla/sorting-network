import D2Stage15LevelSevenScheduleFacts

namespace Chvatal.D2Reserve

attribute [local irreducible] d2FlowCandidateRun
set_option maxHeartbeats 500000

theorem d2FlowCandidateRun_stage15_levelSeven_path_history
    (height : Nat) (initial : D2FlowTree (height + 8))
    (path : D2FlowPath 7) :
    d2FlowTreeAtPath 7
        (d2FlowCandidateRun (height + 1 + 7) initial 15) path =
      d2FlowTreeRunWithParentOverwrites
        (d2FlowTreePathContext 7 initial path 0
          (d2FlowCandidateRunActive (height + 1 + 7))
          (d2FlowCandidateRunRole (height + 1 + 7))
          (d2FlowCandidateRunQuota (height + 1 + 7))
          (d2FlowCandidateRunOverwrite (height + 1 + 7) initial)).initial
        (d2FlowTreePathContext 7 initial path 0
          (d2FlowCandidateRunActive (height + 1 + 7))
          (d2FlowCandidateRunRole (height + 1 + 7))
          (d2FlowCandidateRunQuota (height + 1 + 7))
          (d2FlowCandidateRunOverwrite (height + 1 + 7) initial)).level
        (d2FlowCandidateRunActive (height + 1 + 7))
        (d2FlowCandidateRunRole (height + 1 + 7))
        (d2FlowCandidateRunQuota (height + 1 + 7))
        (d2FlowTreePathContext 7 initial path 0
          (d2FlowCandidateRunActive (height + 1 + 7))
          (d2FlowCandidateRunRole (height + 1 + 7))
          (d2FlowCandidateRunQuota (height + 1 + 7))
          (d2FlowCandidateRunOverwrite (height + 1 + 7) initial)).overwrite 15 := by
  have hpath := d2FlowCandidateRun_path_as_history
    (h := height + 1) (n := 7) (initial := initial)
    (path := path) (step := 15)
  have hhistory := d2FlowTreePathHistory_eq_context_run
    (h := height + 1) (n := 7) initial path 0
    (d2FlowCandidateRunActive (height + 1 + 7))
    (d2FlowCandidateRunRole (height + 1 + 7))
    (d2FlowCandidateRunQuota (height + 1 + 7))
    (d2FlowCandidateRunOverwrite (height + 1 + 7) initial) 15
  rw [hpath, hhistory]

end Chvatal.D2Reserve
