import D2Stage14ActualLevelFourBalance
import D2Stage14ActualLevelFiveInputs
import D2Stage14LevelFourReserve

namespace Chvatal.D2Reserve

set_option maxHeartbeats 10000000
set_option linter.constructorNameAsVariable false

/-- The complete Stage-14 recursive input contract holds at every actual
level-four node: Stage 13 supplies its balance, deficit, and endpoint
reserves; the reserve also pays the quota, while level five is inactive. -/
theorem d2FlowCandidateStage14_actual_levelFour_inputs
    (childDepth : Nat) (hd : 7 <= childDepth) :
    forall j k m l,
      d2FlowStageInvInputs 8192
        (d2FlowCandidateActive (childDepth + 7) 14)
        (d2FlowCandidateRole (childDepth + 7) 14)
        (d2FlowCandidateQuota (childDepth + 7) 14)
        (fun x => d2FlowCandidateCapacity (childDepth + 7) x 14) 4
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowCandidateRun (childDepth + 7)
                  (d2FlowTreeInitial 8192 (childDepth + 7)) 14) j) k) m) l) := by
  intro j k m l
  let d := childDepth + 7
  let output := d2FlowTreeChild
    (d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowCandidateRun d
            (d2FlowTreeInitial 8192 d) 14) j) k) m) l
  have hactive4 : d2FlowCandidateActive d 14 4 = true := by
    simp [d2FlowCandidateActive, tfD2]
    omega
  have hstar14 : alphaStar d 14 = 0 := by
    unfold alphaStar
    have h : 39 <= 3 * d := by omega
    simp [h]
  have hstar15 : alphaStar d 15 = 0 := by
    unfold alphaStar
    have h : 41 <= 3 * d := by omega
    simp [h]
  have ha14 : alpha d 14 = 0 := by simp [alpha, hstar14, ceilParity]
  have ha15 : alpha d 15 = 1 := by simp [alpha, hstar15, ceilParity]
  have ho14 : omega 14 = 6 := by norm_num [omega, ceilParity]
  have ho15 : omega 15 = 7 := by norm_num [omega, ceilParity]
  have hrole4 : d2FlowCandidateRole d 14 4 = .mid := by
    rw [d2FlowCandidateRole_matches_schedule (by omega)]
    simp [d2ScheduleRole, ha14, ho14]
  have hstate := d2FlowCandidateStage14_actual_levelFour_balance_deficit
    childDepth hd j k m l
  change (d2FlowTreeRootData output).2.1 +
      (d2FlowTreeRootData output).2.2 = d2FlowTreeRootDeficit output /\
    512 * d2FlowTreeRootDeficit output <=
      d2FlowCandidateCapacity d 4 14 at hstate
  have hreserve := d2FlowCandidateStage14_actual_levelFour_endpoint_reserves
    childDepth hd j k m l
  change d2FlowCandidateCapacity d 4 14 <=
      128 * d2FlowTreeRootDeficit (d2FlowTreeChild output ⟨0, by omega⟩) /\
    d2FlowCandidateCapacity d 4 14 <=
      128 * d2FlowTreeRootDeficit (d2FlowTreeChild output ⟨7, by omega⟩)
    at hreserve
  have hbudget := d2FlowCandidateStage14_levelFour_mid_budgets d (by omega)
  rcases hbudget with ⟨_, _, hquotaCap, _⟩
  have hquotaEven : d2FlowCandidateQuota d 14 4 .mid % 2 = 0 := by
    have hquota : d2FlowCandidateQuota d 14 4 .mid =
        15 * 2 ^ (3 * d - 19) := by
      simp [d2FlowCandidateQuota, d2FlowCandidateCapacityExponent]
      omega
    rw [hquota]
    obtain ⟨e, he⟩ := Nat.exists_eq_succ_of_ne_zero
      (show 3 * d - 19 ≠ 0 by omega)
    rw [he, pow_succ]
    omega
  have hdD : 14 <= d := by dsimp [d]; omega
  have hrecursive : forall s : Fin 8,
      d2FlowStageInvInputs 8192
        (d2FlowCandidateActive d 14) (d2FlowCandidateRole d 14)
        (d2FlowCandidateQuota d 14)
        (fun x => d2FlowCandidateCapacity d x 14) 5
        (d2FlowTreeChild output s) := by
    intro s
    have hs := d2FlowCandidateStage14_actual_levelFive_inputs
      childDepth hd j k m l s
    change d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 14) (d2FlowCandidateRole d 14)
      (d2FlowCandidateQuota d 14)
      (fun x => d2FlowCandidateCapacity d x 14) 5
      (d2FlowTreeChild output s) at hs
    exact hs
  have hleft : d2FlowCandidateCapacity d 4 14 <=
      128 * d2FlowTreeRootDeficit
        (d2FlowTreeChild output (Fin.mk 0 (by omega))) := hreserve.1
  have hright : d2FlowCandidateCapacity d 4 14 <=
      128 * d2FlowTreeRootDeficit
        (d2FlowTreeChild output (Fin.mk 7 (by omega))) := hreserve.2
  have halloc : d2FlowCandidateQuota d 14 4 .mid <=
      d2FlowTotal (fun s =>
        d2FlowTreeRootDeficit (d2FlowTreeChild output s)) -
        d2FlowTreeRootDeficit output := by
    exact d2FlowCandidateStage14_levelFour_allocation_of_endpoint
      d (d2FlowTreeRootDeficit output)
      (fun s => d2FlowTreeRootDeficit (d2FlowTreeChild output s))
      (Fin.mk 0 (by omega)) hdD hstate.2 hleft
  exact d2FlowStageInvInputs_mid_of_contract 8192 4 output
    (by simpa [d] using hactive4) (by simpa [d] using hrole4)
    hrecursive hstate.1 hstate.2 hquotaCap halloc hquotaEven hleft hright
end Chvatal.D2Reserve
