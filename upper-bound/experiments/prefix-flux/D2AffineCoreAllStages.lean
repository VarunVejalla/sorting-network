import D2TreePathGeometry
import D2AffineCoreBootstrap

namespace Chvatal.D2Reserve

def d2FlowCandidateRunAffineCore (d t : Nat) : Prop :=
  d2FlowStageAffineCoreInputs
    (fun k => d2FlowCandidateActive d t k)
    (fun k => d2FlowCandidateRole d t k)
    (fun k => d2FlowCandidateCapacity d k t) 0
    (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) t)

/-- The affine-core flow contract and tree invariant hold at every candidate
stage for dimensions at least seven. The induction starts from the checked
four-snapshot bootstrap and uses the one-step full-tree transition. -/
theorem d2FlowCandidateRun_affine_core_and_inv_all
    (d : Nat) (hd : 7 <= d) (n : Nat) :
    d2FlowCandidateRunAffineCore d n /\
      d2FlowTreeInv 8192
        (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n < 4
      · have hnle : n <= 3 := by omega
        interval_cases n
        · constructor
          · exact d2FlowCandidateRun_initial_affine_core d
          · exact d2FlowTreeInitial_inv 8192 d
        · have hcore := d2FlowCandidateRun_stage1_affine_core
            (d - 2) (by omega)
          have hinv := d2FlowCandidateBootstrap_preserves_inv d
          have hdRecover : d - 2 + 2 = d := by omega
          constructor
          · exact d2FlowCandidateRun_affine_core_transport hdRecover hcore
          · exact hinv
        · have hcore := d2FlowCandidateRun_stage2_affine_core
            (d - 2) (by omega)
          have hinv := d2FlowCandidateStage1_preserves_inv (d - 2) (by omega)
          have hdRecover : d - 2 + 2 = d := by omega
          constructor
          · exact d2FlowCandidateRun_affine_core_transport hdRecover hcore
          · exact d2FlowCandidateRun_inv_transport hdRecover hinv
        · have hcore := d2FlowCandidateRun_stage3_affine_core
            (d - 2) (by omega)
          have hinv := d2FlowCandidateStage2_preserves_inv (d - 2) (by omega)
          have hdRecover : d - 2 + 2 = d := by omega
          constructor
          · exact d2FlowCandidateRun_affine_core_transport hdRecover hcore
          · exact d2FlowCandidateRun_inv_transport hdRecover hinv
      · have hprev := ih (n - 1) (by omega)
        have hprevprev := ih (n - 2) (by omega)
        have hcore := d2FlowCandidateRun_affine_core_next
          (d := d) (t := n - 1) hd (by omega)
          (by simpa [d2FlowCandidateRunAffineCore] using hprevprev.1)
          (by simpa [d2FlowCandidateRunAffineCore] using hprev.1)
          hprev.2
        have hinv := d2FlowCandidateRun_preserves_inv_next_of_affine_core
          (d := d) (t := n - 1) hd (by omega) hprev.2
          (by simpa [d2FlowCandidateRunAffineCore] using hprev.1)
        have hnRecover : n - 1 + 1 = n := by omega
        constructor
        · simpa [d2FlowCandidateRunAffineCore, hnRecover] using hcore
        · simpa [hnRecover] using hinv

end Chvatal.D2Reserve
