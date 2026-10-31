import D2Stage14Arithmetic

namespace Chvatal.D2Reserve

set_option maxHeartbeats 10000000

theorem d2FlowStage14BalanceProbe (childDepth : Nat) (hd : Nat.le 7 childDepth)
    (j k m l q r : Fin 8) :
    let d := childDepth + 7
    let run := d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 14
    let tree := d2FlowTreeChild (d2FlowTreeChild (d2FlowTreeChild
      (d2FlowTreeChild (d2FlowTreeChild (d2FlowTreeChild run j) k) m) l) q) r
    (d2FlowTreeRootData tree).2.1 + (d2FlowTreeRootData tree).2.2 =
      d2FlowTreeRootDeficit tree := by
  dsimp only
  exact d2FlowCandidateStage14_actual_levelSix_balanced childDepth hd j k m l q r

end Chvatal.D2Reserve
