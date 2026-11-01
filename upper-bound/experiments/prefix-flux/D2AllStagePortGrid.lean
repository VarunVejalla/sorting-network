import D2AffineCoreAllStages
import D2VariableTilePhysicalFlowTransfer
import D2StrongFlowCoreInputs

namespace Chvatal.D2AllStagePortGrid

open Chvatal.D2Reserve
open Chvatal.D2VariableTilePhysicalFlowTransfer
open Chvatal.D2StaticWireSets

/-- The all-stage affine-core theorem supplies the recursive sender-input
contract itself, before projecting it to any one sender. -/
theorem d2FlowCandidateRun_stage_inv_inputs_all
    (d : Nat) (hd : 7 <= d) :
    forall t, d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d t) (d2FlowCandidateRole d t)
      (d2FlowCandidateQuota d t)
      (fun k => d2FlowCandidateCapacity d k t)
      0 (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) t) := by
  intro t
  have hsnapshot := d2FlowCandidateRun_affine_core_and_inv_all d hd t
  by_cases ht : t = 0
  · subst t
    have hnoAlloc := d2FlowCandidateRun_stage0_affine_noAlloc d
    have haffine := d2FlowStageAffineInputs_of_noAlloc
      (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 0) hnoAlloc
    exact d2FlowStageAffineInputs.to_d2FlowStageInvInputs
      (scale := 8192) _ haffine
  · have htpos : 0 < t := by omega
    have haffine := d2FlowCandidateRun_core_provider_affine_atPath
      (h := d) (i := 0) (t := t) hd htpos D2FlowPath.nil hsnapshot.1
    exact d2FlowStageAffineInputs.to_d2FlowStageInvInputs
      (scale := 8192) _ haffine

/-- Project the all-stage sender-input provider to an actual candidate-run
subtree selected by a path. The cast only reconciles the path-height index. -/
theorem d2FlowCandidateRun_stage_inv_inputs_atPath
    {d h n t : Nat} (hd : 7 <= d) (hdepth : d = h + n)
    (path : D2FlowPath n) :
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive (h + n) t)
      (d2FlowCandidateRole (h + n) t)
      (d2FlowCandidateQuota (h + n) t)
      (fun k => d2FlowCandidateCapacity (h + n) k t) n
      (d2FlowTreeAtPath n
        (cast (congrArg D2FlowTree hdepth)
          (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) t)) path) := by
  cases hdepth
  simpa using d2FlowStageInvInputs_atPath
    (tree := d2FlowCandidateRun (h + n)
      (d2FlowTreeInitial 8192 (h + n)) t)
    path (d2FlowCandidateRun_stage_inv_inputs_all (h + n) hd t)

/-- The all-stage affine-core theorem supplies the stage-input contract used
by the sender-boundary grid theorem. Thus every active ordinary sender in the
candidate flow has 4096-aligned ten-port boundaries at every stage. -/
theorem d2FlowCandidateRun_sender_boundary_grid_all
    (d : Nat) (hd : 7 <= d) :
    forall t, d2FlowStagePortGrid 4096
      (d2FlowCandidateActive d t) (d2FlowCandidateRole d t)
      (d2FlowCandidateQuota d t)
      0
      (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) t) := by
  intro t
  have hsnapshot := d2FlowCandidateRun_affine_core_and_inv_all d hd t
  have hinputs := d2FlowCandidateRun_stage_inv_inputs_all d hd t
  exact d2FlowCandidateRun_sender_boundary_grid_of_invariants
    hd hsnapshot.2 hinputs

/-- Project the all-stage port-grid theorem to a concrete candidate sender
path, so the local rank boundaries are available at the same node as its
static-hole and endpoint contracts. -/
theorem d2FlowCandidateRun_sender_boundary_grid_atPath
    {d h n t : Nat} (hd : 7 <= d) (hdepth : d = h + n)
    (path : D2FlowPath n) :
    d2FlowStagePortGrid 4096
      (d2FlowCandidateActive (h + n) t)
      (d2FlowCandidateRole (h + n) t)
      (d2FlowCandidateQuota (h + n) t) n
      (d2FlowTreeAtPath n
        (cast (congrArg D2FlowTree hdepth)
          (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) t)) path) := by
  cases hdepth
  simpa using d2FlowStagePortGrid_atPath
    (tree := d2FlowCandidateRun (h + n)
      (d2FlowTreeInitial 8192 (h + n)) t)
    path (d2FlowCandidateRun_sender_boundary_grid_all (h + n) hd t)

end Chvatal.D2AllStagePortGrid
