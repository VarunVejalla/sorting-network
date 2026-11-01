import D2BotRiseRunBridge
import D2PathNativePreservation
import D2AllStagePortGrid
import D2PhysicalBagState

/-! Schedule-to-geometry adapter for the exceptional bottom-rise case. -/

namespace Chvatal.D2BotRiseStaticFit

open Chvatal.D2Reserve
open Chvatal.D2PhysicalBagState
open Chvatal.D2StaticWireSets
open Chvatal.D2AllStagePortGrid

/-- At a reachable `botRise` snapshot, every child remains saturated from the
standard initialization. Therefore the updated parent has clamped static-hole
fit at its collapsed boundary. This closes the special-role fit obligation
without assuming endpoint fronts directly. -/
theorem candidate_botRise_path_static_fit_clamped
    {h j : Nat} (hd : 7 <= h + 1 + (j + 2)) (hj : 1 <= j)
    (hwindow : 3 * j + 2 <= tfD2 (h + 1 + (j + 2)))
    (path : D2FlowPath (j + 2)) :
    exists G low high, exists children : Fin 8 -> D2FlowTree h,
      d2FlowTreeAtPath (j + 2)
          (d2FlowCandidateRun (h + 1 + (j + 2))
            (d2FlowTreeInitial 8192 (h + 1 + (j + 2))) (3 * j)) path =
        .node G low high children /\
      StaticHolesFit
        (low + (d2FlowTotal (fun k => d2FlowTreeRootDeficit (children k)) - G) / 2)
        (d2FlowNodeStaticHolesClamped 0 (8192 * 8 ^ h)
          (low + (d2FlowTotal (fun k => d2FlowTreeRootDeficit (children k)) - G) / 2)
          (high + (d2FlowTotal (fun k => d2FlowTreeRootDeficit (children k)) - G) -
            (d2FlowTotal (fun k => d2FlowTreeRootDeficit (children k)) - G) / 2)
          (fun k => d2FlowTreeChild
            (d2FlowStage (d2FlowCandidateActive (h + 1 + (j + 2)) (3 * j))
              (d2FlowCandidateRole (h + 1 + (j + 2)) (3 * j))
              (d2FlowCandidateQuota (h + 1 + (j + 2)) (3 * j))
              (h + 1) (j + 2) (.node G low high children)) k))
        (8 * (8192 * 8 ^ h) -
          (high + (d2FlowTotal (fun k => d2FlowTreeRootDeficit (children k)) - G) -
            (d2FlowTotal (fun k => d2FlowTreeRootDeficit (children k)) - G) / 2)) := by
  let d := h + 1 + (j + 2)
  let initial := d2FlowTreeInitial 8192 d
  let run := d2FlowCandidateRun d initial
  let tree := d2FlowTreeAtPath (j + 2) (run (3 * j)) path
  have hinvRoot := (d2FlowCandidateRun_affine_core_and_inv_all d hd (3 * j)).2
  have htree : d2FlowTreeInv 8192 tree := by
    exact d2FlowTreeInv_atPath (scale := 8192) (tree := run (3 * j))
      path hinvRoot
  have hinputsRaw := d2FlowCandidateRun_stage_inv_inputs_atPath
    (d := d) (h := h + 1) (n := j + 2) (t := 3 * j) hd rfl path
  have hinputs : d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d (3 * j))
      (d2FlowCandidateRole d (3 * j))
      (d2FlowCandidateQuota d (3 * j))
      (fun k => d2FlowCandidateCapacity d k (3 * j)) (j + 2) tree := by
    simpa [d, initial, run, tree] using hinputsRaw
  have hpreserves : forall k, k < 3 * j ->
      d2FlowCandidateRunActive d k (j + 3) = false /\
        (d2FlowCandidateRunActive d k (j + 2) = false \/
          d2FlowCandidateRunRole d k (j + 2) = .botRise) := by
    intro k hk
    have hk' : k < 3 * j + 2 := by omega
    simpa [d] using
      d2FlowCandidate_botRise_callback_window hd hj hwindow k hk'
  have hsatRaw : forall k : Fin 8,
      d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowTreeAtPath (j + 2)
            (d2FlowCandidateRun (h + 1 + (j + 2))
              (d2FlowTreeInitial 8192 (h + 1 + (j + 2))) (3 * j)) path)
          k) = 8192 * 8 ^ h := by
    intro k
    exact d2FlowCandidateRun_path_child_root_preserved
      (h := h) (n := j + 1) (t := 3 * j) path k hpreserves
  cases hnode : tree with
  | node G low high children =>
    have htreeNode : d2FlowTreeInv 8192 (.node G low high children) := by
      simpa [hnode] using htree
    have hinputsNode := hinputs
    rw [hnode] at hinputsNode
    have hsat : forall k, d2FlowTreeRootDeficit (children k) = 8192 * 8 ^ h := by
      intro k
      simpa [tree, run, initial, d, hnode] using hsatRaw k
    have hroleActive := d2FlowCandidate_botRise_current_active_role hd hj hwindow
    have ha : d2FlowCandidateActive d (3 * j) (j + 2) = true := by
      simpa [d, d2FlowCandidateRunActive] using hroleActive.1
    have hr : d2FlowCandidateRole d (3 * j) (j + 2) = .botRise := by
      simpa [d, d2FlowCandidateRunRole] using hroleActive.2
    have hwindow' := d2FlowCandidate_botRise_callback_window hd hj hwindow
      (3 * j) (by omega)
    have hnext : d2FlowCandidateActive d (3 * j) (j + 3) = false := by
      simpa [d, d2FlowCandidateRunActive] using hwindow'.1
    have hfit := d2FlowStage_active_bot_rise_static_fit_clamped_of_saturated_children
      (scale := 8192) (h := h) (i := j + 2) (children := children)
      htreeNode hinputsNode ha hr hnext hsat
    exact ⟨G, low, high, children, hnode, by simpa [d] using hfit⟩

end Chvatal.D2BotRiseStaticFit
