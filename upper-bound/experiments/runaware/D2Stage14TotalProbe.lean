import D2Stage14Arithmetic

namespace Chvatal.D2Reserve

set_option maxHeartbeats 10000000

theorem d2FlowStage14TotalProbe (childDepth : Nat) (hd : Nat.le 7 childDepth)
    (j k m l q r : Fin 8) :
    let d := childDepth + 7
    let initial := d2FlowTreeInitial 8192 d
    let run := d2FlowCandidateRun d initial 14
    let path : D2FlowPath 6 := .cons j (.cons k (.cons m (.cons l (.cons q (.cons r .nil)))))
    let tree := d2FlowTreeChild (d2FlowTreeChild (d2FlowTreeChild
      (d2FlowTreeChild (d2FlowTreeChild (d2FlowTreeChild run j) k) m) l) q) r
    d2FlowTotal (fun s => d2FlowTreeRootDeficit (d2FlowTreeChild tree s)) =
      8 * (8192 * 8 ^ childDepth) := by
  let d := childDepth + 7
  let initial := d2FlowTreeInitial 8192 d
  let run := d2FlowCandidateRun d initial 14
  let path : D2FlowPath 6 := .cons j (.cons k (.cons m (.cons l (.cons q (.cons r .nil)))))
  let tree := d2FlowTreeChild (d2FlowTreeChild (d2FlowTreeChild
    (d2FlowTreeChild (d2FlowTreeChild (d2FlowTreeChild run j) k) m) l) q) r
  have htreePath : tree = d2FlowTreeAtPath 6
      (d2FlowCandidateRun d initial 14) path := by rfl
  have htotal : d2FlowTotal
      (fun s => d2FlowTreeRootDeficit (d2FlowTreeChild tree s)) =
        8 * (8192 * 8 ^ childDepth) := by
    have hconst : (fun s : Fin 8 =>
        d2FlowTreeRootDeficit (d2FlowTreeChild tree s)) =
        fun _ => 8192 * 8 ^ childDepth := by
      funext s
      rw [htreePath,
        d2FlowCandidateLevelSix_children_preserved childDepth hd path s,
        d2FlowTreeFull_root_deficit]
    simp [d2FlowTotal, hconst]
  exact htotal

end Chvatal.D2Reserve
