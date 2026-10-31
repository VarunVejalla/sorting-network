import D2BotRiseRunBridge
import D2CandidateQuotaLower
import D2TwoStageEndpointReserve

namespace Chvatal.D2Reserve

set_option linter.unusedVariables false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8192

/-- Transfer the ordinary two-visit endpoint-reserve estimate from a sender's
local tree to its actual subtree in the full candidate run. The path-history
model accounts for arbitrary ancestor overwrites; the only schedule fact used
at the intervening stage is that this sender is inactive there. -/
theorem d2FlowCandidateRun_path_endpoint_reserve_of_prior_sender
    {h i t G low high : Nat} (path : D2FlowPath i)
    (ht : 4 <= t)
    (hcurrent : active (h + 1 + i) (tfD2 (h + 1 + i)) i t)
    (hpriorActive : d2FlowCandidateActive (h + 1 + i) (t - 2) i = true)
    (hpriorRole :
      d2FlowCandidateRole (h + 1 + i) (t - 2) i = .topRise \/
      d2FlowCandidateRole (h + 1 + i) (t - 2) i = .mid \/
      d2FlowCandidateRole (h + 1 + i) (t - 2) i = .botDesc)
    (children : Fin 8 -> D2FlowTree h)
    (hnode : d2FlowTreeAtPath i
        (d2FlowCandidateRun (h + 1 + i)
          (d2FlowTreeInitial 8192 (h + 1 + i)) (t - 2)) path =
      .node G low high children)
    (hbalance : low + high = G)
    (hcover : G <= d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)))
    (hdeficit : 512 * G <=
      d2FlowCandidateCapacity (h + 1 + i) i (t - 2))
    (hquota : 256 * d2FlowCandidateQuota (h + 1 + i) (t - 2) i
      (d2FlowCandidateRole (h + 1 + i) (t - 2) i) <=
        d2FlowCandidateCapacity (h + 1 + i) i (t - 2))
    (halloc : d2FlowCandidateQuota (h + 1 + i) (t - 2) i
      (d2FlowCandidateRole (h + 1 + i) (t - 2) i) <=
        d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G)
    (heven : d2FlowCandidateQuota (h + 1 + i) (t - 2) i
      (d2FlowCandidateRole (h + 1 + i) (t - 2) i) % 2 = 0)
    (hleft : d2FlowCandidateCapacity (h + 1 + i) i (t - 2) <=
      128 * d2FlowTreeRootDeficit (children 0))
    (hright : d2FlowCandidateCapacity (h + 1 + i) i (t - 2) <=
      128 * d2FlowTreeRootDeficit (children 7))
    (hcap : d2FlowCandidateCapacity (h + 1 + i) i (t - 2) =
      16 * d2FlowCandidateCapacity (h + 1 + i) i t)
    (hquotaLower : 15 * d2FlowCandidateCapacity (h + 1 + i) i (t - 2) <=
      4096 * d2FlowCandidateQuota (h + 1 + i) (t - 2) i
        (d2FlowCandidateRole (h + 1 + i) (t - 2) i)) :
    d2FlowCandidateCapacity (h + 1 + i) i t <=
      128 * d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowTreeAtPath i
            (d2FlowCandidateRun (h + 1 + i)
              (d2FlowTreeInitial 8192 (h + 1 + i)) t) path) 0) /\
    d2FlowCandidateCapacity (h + 1 + i) i t <=
      128 * d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowTreeAtPath i
            (d2FlowCandidateRun (h + 1 + i)
              (d2FlowTreeInitial 8192 (h + 1 + i)) t) path) 7) := by
  classical
  let d := h + 1 + i
  let initial := d2FlowTreeInitial 8192 d
  let runActive := d2FlowCandidateRunActive d
  let runRole := d2FlowCandidateRunRole d
  let runQuota := d2FlowCandidateRunQuota d
  let overwrite := d2FlowCandidateRunOverwrite d initial
  let ctx := d2FlowTreePathContext i initial path 0 runActive runRole runQuota overwrite
  have hlevel : ctx.level = i := by
    simpa [ctx, runActive, runRole, runQuota, overwrite, d, initial] using
      d2FlowTreePathContext_level initial path 0 runActive runRole runQuota overwrite
  have hpath (s : Nat) :
      d2FlowTreeAtPath i (d2FlowCandidateRun d initial s) path =
        d2FlowTreeRunWithParentOverwrites ctx.initial ctx.level
          runActive runRole runQuota ctx.overwrite s := by
    rw [d2FlowCandidateRun_path_as_history]
    exact d2FlowTreePathHistory_eq_context_run initial path 0
      (d2FlowCandidateRunActive d) (d2FlowCandidateRunRole d)
      (d2FlowCandidateRunQuota d)
      (d2FlowCandidateRunOverwrite d initial) s
  have hprev :
      d2FlowTreeRunWithParentOverwrites ctx.initial ctx.level
        runActive runRole runQuota ctx.overwrite (t - 2) = .node G low high children := by
    calc
      _ = d2FlowTreeAtPath i (d2FlowCandidateRun d initial (t - 2)) path :=
        (hpath (t - 2)).symm
      _ = .node G low high children := hnode
  have hnotInter : Not (active d (tfD2 d) i (t - 1)) :=
    active_level_inactive_previous_stage ht hcurrent
  have hinterBool : d2FlowCandidateActive d (t - 1) i = false := by
    rw [d2FlowCandidateActive_matches_schedule
      (d := d) (t := t - 1) (i := i) (by omega)]
    simp [hnotInter]
  have hidx : t - 2 + 1 = t - 1 := by omega
  have hinterCtx : runActive (t - 2 + 1) ctx.level = false := by
    rw [hidx, hlevel]
    change d2FlowCandidateActive d (t - 1) i = false
    exact hinterBool
  have htwo0 := d2FlowTreeRunWithParentOverwrites_child_two_step_eq
    (h := h) (i := ctx.level) (n := t - 2)
    ctx.initial runActive runRole runQuota ctx.overwrite 0 hinterCtx
  have htwo7 := d2FlowTreeRunWithParentOverwrites_child_two_step_eq
    (h := h) (i := ctx.level) (n := t - 2)
    ctx.initial runActive runRole runQuota ctx.overwrite 7 hinterCtx
  rw [hprev] at htwo0 htwo7
  have hlocal := d2FlowStage_regular_two_step_endpoint_reserve
    (active := d2FlowCandidateRunActive d (t - 2))
    (nextActive := d2FlowCandidateRunActive d (t - 1))
    (role := d2FlowCandidateRunRole d (t - 2))
    (nextRole := d2FlowCandidateRunRole d (t - 1))
    (quota := d2FlowCandidateRunQuota d (t - 2))
    (nextQuota := d2FlowCandidateRunQuota d (t - 1))
    (oldCap := d2FlowCandidateCapacity d i (t - 2))
    (newCap := d2FlowCandidateCapacity d i t)
    children hpriorActive hpriorRole hbalance hcover hdeficit hquota halloc
    heven hleft hright hinterBool hcap hquotaLower
  have htwo0' :
      d2FlowTreeChild
          (d2FlowTreeRunWithParentOverwrites ctx.initial ctx.level
            runActive runRole runQuota ctx.overwrite t) 0 =
        d2FlowTreeChild
          (d2FlowStage (d2FlowCandidateRunActive d (t - 1))
            (d2FlowCandidateRunRole d (t - 1))
            (d2FlowCandidateRunQuota d (t - 1)) (h + 1) i
            (d2FlowStage (d2FlowCandidateRunActive d (t - 2))
              (d2FlowCandidateRunRole d (t - 2))
              (d2FlowCandidateRunQuota d (t - 2)) (h + 1) i
              (.node G low high children))) 0 := by
    simpa [runActive, runRole, runQuota, d2FlowCandidateRunActive,
      d2FlowCandidateRunRole, d2FlowCandidateRunQuota, d, hlevel, hprev, hidx, Nat.sub_add_cancel
      (show 2 <= t by omega)] using htwo0
  have htwo7' :
      d2FlowTreeChild
          (d2FlowTreeRunWithParentOverwrites ctx.initial ctx.level
            runActive runRole runQuota ctx.overwrite t) 7 =
        d2FlowTreeChild
          (d2FlowStage (d2FlowCandidateRunActive d (t - 1))
            (d2FlowCandidateRunRole d (t - 1))
            (d2FlowCandidateRunQuota d (t - 1)) (h + 1) i
            (d2FlowStage (d2FlowCandidateRunActive d (t - 2))
              (d2FlowCandidateRunRole d (t - 2))
              (d2FlowCandidateRunQuota d (t - 2)) (h + 1) i
              (.node G low high children))) 7 := by
    simpa [runActive, runRole, runQuota, d2FlowCandidateRunActive,
      d2FlowCandidateRunRole, d2FlowCandidateRunQuota, d, hlevel, hprev, hidx, Nat.sub_add_cancel
      (show 2 <= t by omega)] using htwo7
  constructor
  · rw [hpath t, htwo0']
    exact hlocal.1
  · rw [hpath t, htwo7']
    exact hlocal.2

end Chvatal.D2Reserve
