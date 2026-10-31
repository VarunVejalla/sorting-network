import D2Stage14Arithmetic

namespace Chvatal.D2Reserve

set_option maxHeartbeats 10000000

theorem d2FlowStage14ReserveProbe (childDepth : Nat) (hd : Nat.le 7 childDepth)
    (j k m l q r : Fin 8) :
    let d := childDepth + 7
    let run := d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 14
    let tree := d2FlowTreeChild (d2FlowTreeChild (d2FlowTreeChild
      (d2FlowTreeChild (d2FlowTreeChild (d2FlowTreeChild run j) k) m) l) q) r
    d2FlowCandidateCapacity d 6 14 <=
      128 * d2FlowTreeRootDeficit (d2FlowTreeChild tree (Fin.mk 0 (by omega))) ∧
    d2FlowCandidateCapacity d 6 14 <=
      128 * d2FlowTreeRootDeficit (d2FlowTreeChild tree (Fin.mk 7 (by omega))) := by
  let d := childDepth + 7
  let initial := d2FlowTreeInitial 8192 d
  let run := d2FlowCandidateRun d initial 14
  let path : D2FlowPath 6 := .cons j (.cons k (.cons m (.cons l (.cons q (.cons r .nil)))))
  let tree := d2FlowTreeChild (d2FlowTreeChild (d2FlowTreeChild
    (d2FlowTreeChild (d2FlowTreeChild (d2FlowTreeChild run j) k) m) l) q) r
  have hreserve := d2FlowCandidateStage14_actual_levelSix_endpoint_reserves
    childDepth hd path
  change d2FlowCandidateCapacity (childDepth + 7) 6 14 <=
      128 * d2FlowTreeRootDeficit (d2FlowTreeChild
        (d2FlowTreeAtPath 6
          (d2FlowCandidateRun (childDepth + 7)
            (d2FlowTreeInitial 8192 (childDepth + 7)) 14)
          (.cons j (.cons k (.cons m (.cons l (.cons q (.cons r .nil)))))))
        (Fin.mk 0 (by omega))) ∧
    d2FlowCandidateCapacity (childDepth + 7) 6 14 <=
      128 * d2FlowTreeRootDeficit (d2FlowTreeChild
        (d2FlowTreeAtPath 6
          (d2FlowCandidateRun (childDepth + 7)
            (d2FlowTreeInitial 8192 (childDepth + 7)) 14)
          (.cons j (.cons k (.cons m (.cons l (.cons q (.cons r .nil)))))))
        (Fin.mk 7 (by omega))) at hreserve
  exact hreserve

end Chvatal.D2Reserve
