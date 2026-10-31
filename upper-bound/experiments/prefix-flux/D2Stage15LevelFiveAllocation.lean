import D2Stage15ActualReserves
import D2Stage15LevelFiveRootCap

namespace Chvatal.D2Reserve

attribute [local irreducible] d2FlowTreeRootDeficit

set_option maxHeartbeats 2000000

/-- The Stage-14 level-six bottom-descending quota is 32 times the next
Stage-15 level-five middle quota. -/
theorem d2FlowCandidateStage14_levelSix_quota_eq_32_stage15_levelFive
    {d : Nat} (hd : 14 <= d) :
    d2FlowCandidateQuota d 14 6 .botDesc =
      32 * d2FlowCandidateQuota d 15 5 .mid := by
  have hscale := d2FlowCandidateCapacity_stage14_child_eq_32_stage15_parent
    (d := d) (i := 5) hd
  have h14 := d2FlowCandidateStage14_quota_exact_ratio
    (d := d) (i := 5) hd (r := .botDesc) (Or.inr rfl)
  have h15 : 4096 * d2FlowCandidateQuota d 15 5 .mid =
      15 * d2FlowCandidateCapacity d 5 15 := by
    let e := d2FlowCandidateCapacityExponent d 5 15
    have he : 12 <= e := by dsimp [e, d2FlowCandidateCapacityExponent]; omega
    have hp : 2 ^ 12 * 2 ^ (e - 12) = 2 ^ e := by
      rw [← pow_add]
      congr 1
      omega
    change 4096 * (15 * 2 ^ (e - 12)) = 15 * 2 ^ e
    calc
      4096 * (15 * 2 ^ (e - 12)) = 15 * (2 ^ 12 * 2 ^ (e - 12)) := by ring
      _ = 15 * 2 ^ e := by rw [hp]
  rw [hscale] at h14
  nlinarith

/-- Every actual Stage-15 level-six child receives the fresh quota of its
active Stage-14 level-six bottom-descending sender. -/
theorem d2FlowCandidateRun_stage15_levelFive_child_quota
    (h : Nat) (hd : 14 <= h + 7) (j k m l q s : Fin 8) :
    d2FlowCandidateQuota (h + 7) 14 6 .botDesc <=
      d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild
                  (d2FlowTreeChild
                    (d2FlowCandidateRun (h + 7)
                      (d2FlowTreeInitial 8192 (h + 7)) 15) j) k) m) l) q) s) := by
  rw [d2FlowCandidateRun_stage15_levelSix_root_eq_local h hd j k m l q s]
  have hroles := d2FlowCandidateStage14_reserve_sender_roles
    (d := h + 7) (by omega)
  let input := d2FlowTreeChild (d2FlowTreeChild
    (d2FlowTreeChild (d2FlowTreeChild
      (d2FlowTreeChild (d2FlowTreeChild
        (d2FlowCandidateRun (h + 7)
          (d2FlowTreeInitial 8192 (h + 7)) 14) j) k) m) l) q) s
  cases hnode : input with
  | node G low high children =>
      change d2FlowCandidateQuota (h + 7) 14 6 .botDesc <=
        d2FlowTreeRootDeficit
          (d2FlowStage (d2FlowCandidateActive (h + 7) 14)
            (d2FlowCandidateRole (h + 7) 14)
            (d2FlowCandidateQuota (h + 7) 14) (h + 1) 6 input)
      rw [hnode, d2FlowStage_active_node_deficit children hroles.2.2.1]
      simp only [hroles.2.2.2]
      omega

/-- Fresh bottom-descending child quotas cover the next middle quota and its
root deficit whenever the actual Stage-15 sender satisfies its 1/512 cap. -/
theorem d2FlowCandidateStage15_levelFive_allocation_from_child_floor
    {d G : Nat} (hd : 14 <= d) (childDeficit : Fin 8 -> Nat)
    (hfloor : forall j, d2FlowCandidateQuota d 14 6 .botDesc <= childDeficit j)
    (hG : 512 * G <= d2FlowCandidateCapacity d 5 15) :
    d2FlowCandidateQuota d 15 5 .mid <= d2FlowTotal childDeficit - G := by
  have hsum : 8 * d2FlowCandidateQuota d 14 6 .botDesc <=
      d2FlowTotal childDeficit := by
    change 8 * d2FlowCandidateQuota d 14 6 .botDesc <=
      Finset.univ.sum childDeficit
    calc
      8 * d2FlowCandidateQuota d 14 6 .botDesc =
          Finset.univ.sum (fun _ : Fin 8 => d2FlowCandidateQuota d 14 6 .botDesc) := by simp
      _ <= Finset.univ.sum childDeficit := by
        apply Finset.sum_le_sum
        intro j hj
        exact hfloor j
  have hquotaRelation :=
    d2FlowCandidateStage14_levelSix_quota_eq_32_stage15_levelFive hd
  have hrate : 4096 * d2FlowCandidateQuota d 15 5 .mid =
      15 * d2FlowCandidateCapacity d 5 15 := by
    have hscale := d2FlowCandidateCapacity_stage14_child_eq_32_stage15_parent
      (d := d) (i := 5) hd
    have h14 := d2FlowCandidateStage14_quota_exact_ratio
      (d := d) (i := 5) hd (r := .botDesc) (Or.inr rfl)
    rw [hscale] at h14
    nlinarith [hquotaRelation]
  have hGsmall : G <= d2FlowCandidateQuota d 15 5 .mid := by
    nlinarith [hG, hrate]
  have hmargin : d2FlowCandidateQuota d 15 5 .mid + G <=
      8 * d2FlowCandidateQuota d 14 6 .botDesc := by
    nlinarith [hquotaRelation, hGsmall]
  omega

/-- The actual Stage-15 level-five sender satisfies its allocation field. -/
theorem d2FlowCandidateRun_stage15_levelFive_allocation
    (childDepth : Nat) (hd : 7 <= childDepth)
    (j k m l q : Fin 8) :
    d2FlowCandidateQuota (childDepth + 7) 15 5 .mid <=
      d2FlowTotal (fun s => d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild
                  (d2FlowTreeChild
                    (d2FlowCandidateRun (childDepth + 7)
                      (d2FlowTreeInitial 8192 (childDepth + 7)) 15) j) k) m) l) q) s)) -
      d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild
                  (d2FlowCandidateRun (childDepth + 7)
                    (d2FlowTreeInitial 8192 (childDepth + 7)) 15) j) k) m) l) q) := by
  have hrootCap := d2FlowCandidateRun_stage15_levelFive_root_cap
    childDepth hd j k m l q
  have hfloor : forall s : Fin 8,
      d2FlowCandidateQuota (childDepth + 7) 14 6 .botDesc <=
        d2FlowTreeRootDeficit
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild
                  (d2FlowTreeChild
                    (d2FlowTreeChild
                      (d2FlowCandidateRun (childDepth + 7)
                        (d2FlowTreeInitial 8192 (childDepth + 7)) 15) j) k) m) l) q) s) := by
    intro s
    exact d2FlowCandidateRun_stage15_levelFive_child_quota
      childDepth (by omega) j k m l q s
  exact d2FlowCandidateStage15_levelFive_allocation_from_child_floor
    (d := childDepth + 7) (by omega)
    (fun s => d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild
                  (d2FlowCandidateRun (childDepth + 7)
                    (d2FlowTreeInitial 8192 (childDepth + 7)) 15) j) k) m) l) q) s))
    hfloor hrootCap

end Chvatal.D2Reserve
