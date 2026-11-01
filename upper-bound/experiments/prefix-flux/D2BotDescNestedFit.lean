import D2NestedCutContainment
import D2PathNativePreservation
import D2FlowPathLast

namespace Chvatal.D2Reserve

open Chvatal.D2PhysicalBagState
open Chvatal.D2StaticWireSets

/-! The bot-descending path-history provider and nested cut geometry meet here.
The only state-specific premise is the actual stage-input contract at the
selected sender node. -/

/-- At an actual botDesc candidate-run path, the existing native-history
theorem supplies saturation of every level-two grandchild. Therefore all
eight child-root fits follow from the local saturated-grandchild adapter. -/
theorem d2FlowCandidateRun_botDesc_children_clamped_fit
    {h i t G low high : Nat} (path : D2FlowPath i)
    (hd : 7 <= h + 2 + (i + 1)) (ht : 2 <= t)
    (htf : t < tfD2 (h + 2 + (i + 1)))
    (hparent : d2FlowCandidateActive (h + 2 + (i + 1)) t i = true)
    (hrole : d2FlowCandidateRole (h + 2 + (i + 1)) t i = .botDesc)
    (children : Fin 8 -> D2FlowTree (h + 2))
    (hnode : d2FlowTreeAtPath (h := h + 3) i
        (cast (congrArg D2FlowTree
          (show h + 2 + (i + 1) = (h + 3) + i by omega))
          (d2FlowCandidateRun (h + 2 + (i + 1))
            (d2FlowTreeInitial 8192 (h + 2 + (i + 1))) t)) path =
      .node G low high children)
    (htree : d2FlowTreeInv 8192 (.node G low high children))
    (hinputs : d2FlowStageInvInputs 8192
      (d2FlowCandidateActive (h + 2 + (i + 1)) t)
      (d2FlowCandidateRole (h + 2 + (i + 1)) t)
      (d2FlowCandidateQuota (h + 2 + (i + 1)) t)
      (fun k => d2FlowCandidateCapacity (h + 2 + (i + 1)) k t) i
      (.node G low high children)) :
    forall j : Fin 8,
      let d := h + 2 + (i + 1)
      let stage := d2FlowStage (d2FlowCandidateActive d t)
        (d2FlowCandidateRole d t) (d2FlowCandidateQuota d t)
        (h + 3) i (.node G low high children)
      let cut := d2FlowCutChild
        (d2FlowPosition (fun k => d2FlowTreeRootDeficit (children k)) j)
        (d2FlowTreeRootDeficit (children j))
        (low + d2FlowCandidateQuota d t i (d2FlowCandidateRole d t i) / 2)
        (d2FlowTotal (fun k => d2FlowTreeRootDeficit (children k)) - high -
          d2FlowCandidateQuota d t i (d2FlowCandidateRole d t i) / 2)
      StaticHolesFit cut.2.1
        (d2FlowNodeStaticHolesClamped 0 (8192 * 8 ^ (h + 1))
          cut.2.1 cut.2.2
          (fun k => d2FlowTreeChild (d2FlowTreeChild stage j) k))
        (8 * (8192 * 8 ^ (h + 1)) - cut.2.2) := by
  let d := h + 2 + (i + 1)
  let run := cast (congrArg D2FlowTree
      (show h + 2 + (i + 1) = (h + 3) + i by omega))
      (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) t)
  have hpathChild (j : Fin 8) :
      d2FlowTreeAtPath (i + 1)
          (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) t)
          (d2FlowPathSnoc path j) = children j := by
    calc
      _ = d2FlowTreeChild
            (d2FlowTreeAtPath (h := h + 3) i run path) j := by
          simpa [d, run] using
            (d2FlowTreeAtPath_snoc (h := h + 2) (n := i)
              (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) t) path j)
      _ = children j := by rw [hnode]; rfl
  have hsaturated : forall j k,
      d2FlowTreeRootDeficit (d2FlowTreeChild (children j) k) =
        8192 * 8 ^ (h + 1) := by
    intro j k
    have hnative := d2FlowCandidateRun_botDesc_grandchild_root_native
      (h := h + 1) (i := i) (t := t)
      (hd := hd) (ht := ht) (htf := htf) (hrole := hrole)
      (path := d2FlowPathSnoc path j) (child := k)
    rw [hpathChild j] at hnative
    exact hnative
  have hinactive2 := d2FlowCandidateActive_two_levels_below_false_of_botDesc
    hd ht htf hrole
  exact d2FlowCandidateStage_children_clamped_fit_of_saturated_grandchildren
    (d := d) (i := i) (t := t) (h := h) (G := G) (low := low) (high := high)
    children hparent (Or.inr (Or.inr hrole)) hinactive2 htree hinputs hsaturated

end Chvatal.D2Reserve
