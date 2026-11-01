import D2AffineCoreAllStages
import D2CandidateTwoFrontBridge

namespace Chvatal.D2Reserve

open Chvatal.D2CandidateTwoFrontBridge
open Chvatal.D2RankAlignment

/-- If the aggregate unmatched-prefix allowance vanishes, then no child
interval has a positive exact-prefix overrun above its two-front reserve. -/
theorem d2FlowStage_regular_child_exact_prefix_le_deficit_of_zero_overrun
    {active : Nat -> Bool} {role : Nat -> D2Role}
    {quota : Nat -> D2Role -> Nat} {h i G low high : Nat}
    (children : Fin 8 -> D2FlowTree h)
    (ha : active i = true)
    (hr : role i = .topRise ∨ role i = .mid ∨ role i = .botDesc)
    (hG : G <= d2FlowTotal (fun k => d2FlowTreeRootDeficit (children k)))
    (hoverrun : G - min G (low + quota i (role i) / 2) = 0)
    (j : Fin 8) :
    prefixIntervalMass G
        (d2FlowRankBoundary (fun k => d2FlowTreeRootDeficit (children k)) j.val)
        (d2FlowRankBoundary (fun k => d2FlowTreeRootDeficit (children k)) (j.val + 1)) <=
      d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowStage active role quota (h + 1) i
            (.node G low high children)) j) := by
  classical
  let excess : Fin 8 -> Nat := fun k =>
    prefixIntervalMass G
        (d2FlowRankBoundary (fun u => d2FlowTreeRootDeficit (children u)) k.val)
        (d2FlowRankBoundary (fun u => d2FlowTreeRootDeficit (children u)) (k.val + 1)) -
      d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowStage active role quota (h + 1) i
            (.node G low high children)) k)
  have hsum := d2FlowStage_regular_child_prefix_excess_sum_le
    (active := active) (role := role) (quota := quota) (h := h)
    (i := i) (G := G) (low := low) (high := high)
    (children := children) ha hr hG
  rw [hoverrun] at hsum
  have hnonneg : forall k, k ∈ (Finset.univ : Finset (Fin 8)) -> 0 <= excess k := by
    intro k hk
    exact Nat.zero_le _
  have hterm := Finset.single_le_sum hnonneg (Finset.mem_univ j)
  have hterm0 : excess j <= 0 := by
    dsimp [excess] at hterm
    exact le_trans hterm hsum
  have hzero : excess j = 0 := Nat.eq_zero_of_le_zero hterm0
  dsimp [excess] at hzero
  omega

/-- Every active ordinary sender in the all-stage candidate flow tree has
zero aggregate ideal-prefix overrun, and each child's exact-prefix ideal mass
is bounded by that child's two-front deficit. This composes the all-time
affine profile with the candidate quota lower bound. It is an abstract flow
statement; it does not identify Boolean tile masses or tags. -/
theorem d2FlowCandidateRun_active_ordinary_two_front_overrun_zero_atPath
    {h i t : Nat} (hd : 7 <= (h + 1) + i) (ht : 0 < t)
    (path : D2FlowPath i)
    (ha : d2FlowCandidateActive ((h + 1) + i) t i = true)
    (hr : d2FlowCandidateRole ((h + 1) + i) t i = .topRise ∨
      d2FlowCandidateRole ((h + 1) + i) t i = .mid ∨
      d2FlowCandidateRole ((h + 1) + i) t i = .botDesc)
    (G low high : Nat) (children : Fin 8 -> D2FlowTree h)
    (hnode : d2FlowTreeAtPath i
      (d2FlowCandidateRun ((h + 1) + i)
        (d2FlowTreeInitial 8192 ((h + 1) + i)) t) path =
        .node G low high children) :
    And (G - min G
      (low + d2FlowCandidateQuota ((h + 1) + i) t i
        (d2FlowCandidateRole ((h + 1) + i) t i) / 2) = 0) (forall j : Fin 8, prefixIntervalMass G
        (d2FlowRankBoundary (fun k => d2FlowTreeRootDeficit (children k)) j.val)
        (d2FlowRankBoundary (fun k => d2FlowTreeRootDeficit (children k)) (j.val + 1)) <=
      d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowStage (d2FlowCandidateActive ((h + 1) + i) t)
            (d2FlowCandidateRole ((h + 1) + i) t)
            (d2FlowCandidateQuota ((h + 1) + i) t)
            (h + 1) i (.node G low high children)) j)) := by
  classical
  let d := (h + 1) + i
  let run := d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) t
  let node := d2FlowTreeAtPath i run path
  have hcoreAll := d2FlowCandidateRun_affine_core_and_inv_all d hd t
  have hcore := hcoreAll.1
  change d2FlowStageAffineCoreInputs
      (fun k => d2FlowCandidateActive d t k)
      (fun k => d2FlowCandidateRole d t k)
      (fun k => d2FlowCandidateCapacity d k t) 0 run at hcore
  have hlocal := d2FlowCandidateRun_core_provider_affine_atPath
    (h := h + 1) (i := i) (t := t) hd ht path hcore
  have hlocal' : d2FlowStageAffineInputs
      (d2FlowCandidateActive d t) (d2FlowCandidateRole d t)
      (d2FlowCandidateQuota d t)
      (fun k => d2FlowCandidateCapacity d k t) i node := by
    simpa [d, run, node] using hlocal
  have hactiveSchedule : active d (tfD2 d) i t := by
    have haD : d2FlowCandidateActive d t i = true := by simpa [d] using ha
    have hmatch := d2FlowCandidateActive_matches_schedule
      (d := d) (t := t) (i := i) ht
    rw [hmatch] at haD
    exact of_decide_eq_true haD
  have haD : d2FlowCandidateActive d t i = true := by simpa [d] using ha
  have hrD : d2FlowCandidateRole d t i = .topRise ∨
      d2FlowCandidateRole d t i = .mid ∨
      d2FlowCandidateRole d t i = .botDesc := by simpa [d] using hr
  have hroleSchedule : d2ScheduleRole d i t = .topRise ∨
      d2ScheduleRole d i t = .mid ∨ d2ScheduleRole d i t = .botDesc := by
    simpa [d, d2FlowCandidateRole, Nat.ne_of_gt ht] using hr
  have hroleEq : d2FlowCandidateRole d t i = d2ScheduleRole d i t :=
    d2FlowCandidateRole_matches_schedule ht
  have hlocalNode : d2FlowStageAffineInputs
      (d2FlowCandidateActive d t) (d2FlowCandidateRole d t)
      (d2FlowCandidateQuota d t)
      (fun k => d2FlowCandidateCapacity d k t) i
      (D2FlowTree.node G low high children) := by
    simpa [d, run, node, hnode] using hlocal'
  have hfields := d2FlowStageAffineInputs_ordinary_fields children
    hlocalNode haD hrD
  have hquotaAlloc := hfields.2.1
  rcases hfields with ⟨_, _, heven, _, _, _, _, hprofile⟩
  have hdeficit : 8192 * G <= 15 * d2FlowCandidateCapacity d i t := by
    rcases hprofile with hzero | hstrong
    · rcases hzero with ⟨hGzero, _⟩
      simp [hGzero]
    · omega
  have hevenSchedule : d2FlowCandidateQuota d t i (d2ScheduleRole d i t) % 2 = 0 := by
    rw [← hroleEq]
    exact heven
  have hover := candidate_sender_two_front_overrun_zero_of_15over8192
    (d := d) (i := i) (t := t) (G := G) (low := low)
    (by omega) hactiveSchedule hroleSchedule hdeficit hevenSchedule
  rw [hroleEq.symm] at hover
  have hzero : G - min G
      (low + d2FlowCandidateQuota d t i (d2FlowCandidateRole d t i) / 2) = 0 := by
    simpa [d] using hover
  have hinvPath := d2FlowTreeInv_atPath (scale := 8192)
    (tree := run) (path := path) (by simpa [run, d] using hcoreAll.2)
  have hnode' : node = .node G low high children := by
    simpa [node, run, d] using hnode
  have hinvNode : d2FlowTreeInv 8192 (.node G low high children) := by
    change d2FlowTreeInv 8192 node at hinvPath
    rw [hnode'] at hinvPath
    exact hinvPath
  simp only [d2FlowTreeInv] at hinvNode
  have hGtotal : G <= d2FlowTotal (fun k => d2FlowTreeRootDeficit (children k)) := by
    exact hinvNode.2.1
  refine ⟨hzero, ?_⟩
  intro j
  have hzeroConcrete : G - min G
      (low + d2FlowCandidateQuota ((h + 1) + i) t i
        (d2FlowCandidateRole ((h + 1) + i) t i) / 2) = 0 := by
    simpa [d] using hzero
  exact d2FlowStage_regular_child_exact_prefix_le_deficit_of_zero_overrun
    (active := d2FlowCandidateActive ((h + 1) + i) t)
    (role := d2FlowCandidateRole ((h + 1) + i) t)
    (quota := d2FlowCandidateQuota ((h + 1) + i) t)
    (h := h) (i := i) (G := G) (low := low) (high := high)
    children ha hr hGtotal hzeroConcrete j

end Chvatal.D2Reserve
