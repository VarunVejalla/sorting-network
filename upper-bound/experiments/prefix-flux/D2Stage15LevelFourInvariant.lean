import D2Stage15LevelThreeRootCap

namespace Chvatal.D2Reserve

attribute [local irreducible] d2FlowTreeInv

/-- Stage 13's invariant descends to every actual level-four sender entering
Stage 14. -/
theorem d2FlowCandidateRun_stage14_levelFour_invariant
    (childDepth : Nat) (hd : 7 <= childDepth) (j k m l : Fin 8) :
    d2FlowTreeInv 8192
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowCandidateRun (childDepth + 7)
                (d2FlowTreeInitial 8192 (childDepth + 7)) 14) j) k) m) l) := by
  let run := d2FlowCandidateRun (childDepth + 7)
    (d2FlowTreeInitial 8192 (childDepth + 7)) 14
  let path2 := d2FlowTreeChild (d2FlowTreeChild run j) k
  let path4 := d2FlowTreeChild (d2FlowTreeChild path2 m) l
  have hinv := d2FlowCandidateStage13_preserves_inv (childDepth + 1) (by omega)
  have hinv2 : d2FlowTreeInv 8192 path2 := by
    exact d2FlowTreeInv_grandchild (h := childDepth + 5) run hinv j k
  have hinv4 : d2FlowTreeInv 8192 path4 := by
    exact d2FlowTreeInv_grandchild (h := childDepth + 3) path2 hinv2 m l
  simpa [run, path2, path4] using hinv4

end Chvatal.D2Reserve
