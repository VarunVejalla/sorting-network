import D2BotRiseRunBridge
import D2PathNativePreservation
import D2AllStagePortGrid
import D2PhysicalBagState
import D2DynamicSenderNode

/-! Schedule-to-geometry adapter for the exceptional bottom-rise case. -/

namespace Chvatal.D2BotRiseStaticFit

open Chvatal.D2Reserve
open Chvatal.D2PhysicalBagState
open Chvatal.D2StaticWireSets
open Chvatal.D2AllStagePortGrid
open Chvatal.D2OrdinaryRankRouting

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
      StaticHolesFit low
        (d2FlowNodeStaticHolesClamped 0 (8192 * 8 ^ h) low high children)
        (8 * (8192 * 8 ^ h) - high) /\
      (d2FlowNodeStaticBag (n := 8 * (8192 * 8 ^ h)) 0
        (8192 * 8 ^ h) G low high children).card =
          8 * (8192 * 8 ^ h) - G /\
      (d2FlowTotal (fun k => d2FlowTreeRootDeficit (children k)) - G) % 2 = 0 /\
      d2FlowTotal (fun k => d2FlowTreeRootDeficit (children k)) =
        8 * (8192 * 8 ^ h) /\
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
            (d2FlowTotal (fun k => d2FlowTreeRootDeficit (children k)) - G) / 2)) /\
      d2FlowNodeStaticBag (n := 8 * (8192 * 8 ^ h)) 0 (8192 * 8 ^ h)
        (G + (d2FlowTotal (fun k => d2FlowTreeRootDeficit (children k)) - G))
        (low + (d2FlowTotal (fun k => d2FlowTreeRootDeficit (children k)) - G) / 2)
        (high + (d2FlowTotal (fun k => d2FlowTreeRootDeficit (children k)) - G) -
          (d2FlowTotal (fun k => d2FlowTreeRootDeficit (children k)) - G) / 2)
        (fun k => d2FlowTreeChild
          (d2FlowStage (d2FlowCandidateActive (h + 1 + (j + 2)) (3 * j))
            (d2FlowCandidateRole (h + 1 + (j + 2)) (3 * j))
            (d2FlowCandidateQuota (h + 1 + (j + 2)) (3 * j))
            (h + 1) (j + 2) (.node G low high children)) k) = Finset.empty := by
  let d := h + 1 + (j + 2)
  let width := 8192 * 8 ^ h
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
    have htileRoot := (d2FlowCandidateRun_alignment_all (d := d) hd (3 * j)
      (by omega : 1 <= 3 * j)).1
    have htileSelected := d2FlowTileAligned_atPath
      (d2FlowCandidateRun d initial (3 * j)) path htileRoot
    have htileNode : d2FlowTileAligned (.node G low high children) := by
      simpa [tree, run, initial, d, hnode] using htileSelected
    have hGgrid : 4096 ∣ G := htileNode.1
    have hstageInput := hinputsNode.2
    simp only [ha, if_pos, hr] at hstageInput
    have hbalance : low + high = G := hstageInput.1
    have hrootCap : G <= 8 * width := by
      have hcap := htreeNode.1
      simpa [width, Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm,
        Nat.mul_left_comm] using hcap
    have hparent : low + high <= 8 * width := by omega
    have hsourceFit := d2FlowNodeStaticHolesClamped_fit_of_saturated_children_in_parent
      (base := 0) (width := width) (low := low) (high := high)
      children hparent (by simpa [width] using hsat)
    have hwindow' := d2FlowCandidate_botRise_callback_window hd hj hwindow
      (3 * j) (by omega)
    have hnext : d2FlowCandidateActive d (3 * j) (j + 3) = false := by
      simpa [d, d2FlowCandidateRunActive] using hwindow'.1
    have hfit := d2FlowStage_active_bot_rise_static_fit_clamped_of_saturated_children
      (scale := 8192) (h := h) (i := j + 2) (children := children)
      htreeNode hinputsNode ha hr hnext hsat
    have htotal : d2FlowTotal (fun k => d2FlowTreeRootDeficit (children k)) =
        8 * (8192 * 8 ^ h) := by
      unfold d2FlowTotal
      calc
        Finset.univ.sum (fun k : Fin 8 => d2FlowTreeRootDeficit (children k)) =
            Finset.univ.sum (fun _ : Fin 8 => 8192 * 8 ^ h) := by
          apply Finset.sum_congr rfl
          intro k hk
          exact hsat k
        _ = 8 * (8192 * 8 ^ h) := by simp
    have htotalGrid : 4096 ∣ d2FlowTotal
        (fun k => d2FlowTreeRootDeficit (children k)) := by
      rw [htotal]
      exact ⟨16 * 8 ^ h, by ring⟩
    have hallocationGrid : 4096 ∣ (d2FlowTotal
        (fun k => d2FlowTreeRootDeficit (children k)) - G) :=
      d2_dvd_sub_trunc htotalGrid hGgrid
    have hallocationEven : (d2FlowTotal
        (fun k => d2FlowTreeRootDeficit (children k)) - G) % 2 = 0 := by
      rcases hallocationGrid with ⟨m, hm⟩
      omega
    have hsourceCard :
        (d2FlowNodeStaticBag (n := 8 * (8192 * 8 ^ h)) 0
          (8192 * 8 ^ h) G low high children).card =
            8 * (8192 * 8 ^ h) - G := by
      by_cases hsatG : G = 8 * (8192 * 8 ^ h)
      · rw [d2FlowNodeStaticBag, if_pos hsatG]
        simp [hsatG]
      · have hstop : 8 * (8192 * 8 ^ h) - high <=
            8 * (8192 * 8 ^ h) := by omega
        have hcard := d2FlowNodeStaticBag_card_eq_child_total_sub_G_of_clamped_fit
          (n := 8 * (8192 * 8 ^ h)) (scale := 8192) 0 G low high
          children htreeNode (by simpa using hsourceFit)
          (by simpa using hstop) (by omega)
        rw [htotal] at hcard
        exact hcard
    have hcover : G <= d2FlowTotal
        (fun k => d2FlowTreeRootDeficit (children k)) := by
      simpa using htreeNode.2.1
    have hfull : G +
        (d2FlowTotal (fun k => d2FlowTreeRootDeficit (children k)) - G) =
        8 * (8192 * 8 ^ h) := by omega
    have hbag : d2FlowNodeStaticBag (n := 8 * (8192 * 8 ^ h))
        0 (8192 * 8 ^ h)
        (G + (d2FlowTotal (fun k => d2FlowTreeRootDeficit (children k)) - G))
        (low + (d2FlowTotal (fun k => d2FlowTreeRootDeficit (children k)) - G) / 2)
        (high + (d2FlowTotal (fun k => d2FlowTreeRootDeficit (children k)) - G) -
          (d2FlowTotal (fun k => d2FlowTreeRootDeficit (children k)) - G) / 2)
        (fun k => d2FlowTreeChild
          (d2FlowStage (d2FlowCandidateActive d (3 * j))
            (d2FlowCandidateRole d (3 * j))
            (d2FlowCandidateQuota d (3 * j))
            (h + 1) (j + 2) (.node G low high children)) k) = Finset.empty := by
      rw [d2FlowNodeStaticBag, if_pos (by simpa [d, htotal] using hfull)]
      rfl
    exact ⟨G, low, high, children, hnode,
      by simpa [d, width] using hsourceFit,
      by simpa [d, width] using hsourceCard,
      by simpa [d] using hallocationEven,
      by simpa [d, width] using htotal,
      by simpa [d, width] using hfit, by simpa [d, width] using hbag⟩

/-- Expose the all-child saturation consequence at every reachable bot-rise
path, for use in nested static-hole containment. -/
theorem candidate_botRise_path_children_saturated
    {h j : Nat} (hd : 7 <= h + 1 + (j + 2)) (hj : 1 <= j)
    (hwindow : 3 * j + 2 <= tfD2 (h + 1 + (j + 2)))
    (path : D2FlowPath (j + 2)) :
    exists G low high, exists children : Fin 8 -> D2FlowTree h,
      d2FlowTreeAtPath (j + 2)
          (d2FlowCandidateRun (h + 1 + (j + 2))
            (d2FlowTreeInitial 8192 (h + 1 + (j + 2))) (3 * j)) path =
        .node G low high children /\
      forall k, d2FlowTreeRootDeficit (children k) = 8192 * 8 ^ h := by
  let d := h + 1 + (j + 2)
  let initial := d2FlowTreeInitial 8192 d
  let run := d2FlowCandidateRun d initial
  let tree := d2FlowTreeAtPath (j + 2) (run (3 * j)) path
  obtain ⟨G, low, high, children, hnode, -, -, -, htotal, -⟩ :=
    candidate_botRise_path_static_fit_clamped hd hj hwindow path
  have hinvRoot := (d2FlowCandidateRun_affine_core_and_inv_all d hd (3 * j)).2
  have htree : d2FlowTreeInv 8192 tree := by
    exact d2FlowTreeInv_atPath (scale := 8192)
      (tree := run (3 * j)) path hinvRoot
  have hnodeInv : d2FlowTreeInv 8192 (.node G low high children) := by
    rw [← hnode]
    exact htree
  have hinvChildren : forall k, d2FlowTreeInv 8192 (children k) := by
    intro k
    have h := hnodeInv
    simp only [d2FlowTreeInv] at h
    exact h.2.2.2 k
  have hsat := d2FlowTreeInv_children_saturated_of_total_full
    children hinvChildren htotal
  exact ⟨G, low, high, children, hnode, hsat⟩

/-- At a reachable bot-rise callback, the node itself becomes saturated after
its children have supplied their full native mass. -/
theorem candidate_botRise_path_post_root_saturated
    {h j : Nat} (hd : 7 <= h + 1 + (j + 2)) (hj : 1 <= j)
    (hwindow : 3 * j + 2 <= tfD2 (h + 1 + (j + 2)))
    (path : D2FlowPath (j + 2)) :
    exists G low high, exists children : Fin 8 -> D2FlowTree h,
      d2FlowTreeAtPath (j + 2)
          (d2FlowCandidateRun (h + 1 + (j + 2))
            (d2FlowTreeInitial 8192 (h + 1 + (j + 2))) (3 * j)) path =
        .node G low high children /\
      d2FlowTreeRootDeficit
        (d2FlowStage (d2FlowCandidateActive (h + 1 + (j + 2)) (3 * j))
          (d2FlowCandidateRole (h + 1 + (j + 2)) (3 * j))
          (d2FlowCandidateQuota (h + 1 + (j + 2)) (3 * j))
          (h + 1) (j + 2) (.node G low high children)) = 8192 * 8 ^ (h + 1) := by
  let d := h + 1 + (j + 2)
  obtain ⟨G, low, high, children, hnode, hsat⟩ :=
    candidate_botRise_path_children_saturated hd hj hwindow path
  have hinvRoot := (d2FlowCandidateRun_affine_core_and_inv_all d hd (3 * j)).2
  have htree := d2FlowTreeInv_atPath (scale := 8192)
    (tree := d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) (3 * j))
    path hinvRoot
  have hnodeInv : d2FlowTreeInv 8192 (.node G low high children) := by
    rw [← hnode]
    exact htree
  have hcover := d2FlowTreeInv_node_children_cover children hnodeInv
  have hactiveRole := d2FlowCandidate_botRise_current_active_role hd hj hwindow
  have ha : d2FlowCandidateActive d (3 * j) (j + 2) = true := by
    simpa [d] using hactiveRole.1
  have hr : d2FlowCandidateRole d (3 * j) (j + 2) = .botRise := by
    simpa [d] using hactiveRole.2
  have hsaturates := d2FlowStage_botRise_root_saturates
    (quota := d2FlowCandidateQuota d (3 * j)) (h := h)
    (i := j + 2) (G := G) (low := low) (high := high)
    children ha hr hcover
  have htotal : d2FlowTotal (fun k => d2FlowTreeRootDeficit (children k)) =
      8 * (8192 * 8 ^ h) := by
    unfold d2FlowTotal
    calc
      Finset.univ.sum (fun k : Fin 8 => d2FlowTreeRootDeficit (children k)) =
          Finset.univ.sum (fun _ : Fin 8 => 8192 * 8 ^ h) := by
        apply Finset.sum_congr rfl
        intro k hk
        exact hsat k
      _ = 8 * (8192 * 8 ^ h) := by simp
  have hsaturates' : d2FlowTreeRootDeficit
      (d2FlowStage (d2FlowCandidateActive
          (h + 1 + (j + 2)) (3 * j))
        (d2FlowCandidateRole (h + 1 + (j + 2)) (3 * j))
        (d2FlowCandidateQuota (h + 1 + (j + 2)) (3 * j))
        (h + 1) (j + 2) (.node G low high children)) =
      d2FlowTotal (fun k => d2FlowTreeRootDeficit (children k)) := by
    simpa [d] using hsaturates
  refine ⟨G, low, high, children, hnode, ?_⟩
  calc
    _ = d2FlowTotal (fun k => d2FlowTreeRootDeficit (children k)) := hsaturates'
    _ = 8 * (8192 * 8 ^ h) := htotal
    _ = 8192 * 8 ^ (h + 1) := by rw [Nat.pow_succ]; ring

def CandidateBotRisePorts {n : Nat} (h j G low high : Nat)
    (children : Fin 8 -> D2FlowTree h) (s : Finset (Fin n)) : Prop :=
  let d := h + 1 + (j + 2)
  let widths : Fin 8 -> Nat := fun k =>
    d2FlowTreeRootDeficit (children k) -
      d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowStage (d2FlowCandidateActive d (3 * j))
            (d2FlowCandidateRole d (3 * j))
            (d2FlowCandidateQuota d (3 * j))
            (h + 1) (j + 2) (.node G low high children)) k)
  let pi := d2FlowTotal
    (fun k => d2FlowTreeRootDeficit (children k)) - G
  let boundary := d2FlowRankBoundary widths
  (forall target : Option (Fin 8), destinationPiece (ports := 8) s boundary (pi / 2)
      (s.card - pi / 2) target ⊆ s) /\
    Finset.univ.biUnion (destinationPiece (ports := 8) s boundary (pi / 2)
      (s.card - pi / 2)) = s /\
    (forall (a b : Option (Fin 8)), a ≠ b ->
      Disjoint (destinationPiece (ports := 8) s boundary (pi / 2)
        (s.card - pi / 2) a)
        (destinationPiece (ports := 8) s boundary (pi / 2)
          (s.card - pi / 2) b)) /\
    (destinationPiece (ports := 8) s boundary (pi / 2)
      (s.card - pi / 2) none).card = pi /\
    (forall j : Fin 8,
      (destinationPiece (ports := 8) s boundary (pi / 2)
        (s.card - pi / 2) (some j)).card = 0)

/-- The all-stage parity result instantiates the generic bottom-rise routing
partition for every sender set with the candidate flow-allocation cardinality. -/
theorem candidate_botRise_path_piece_partition
    {h j : Nat} (hd : 7 <= h + 1 + (j + 2)) (hj : 1 <= j)
    (hwindow : 3 * j + 2 <= tfD2 (h + 1 + (j + 2)))
    (path : D2FlowPath (j + 2)) :
    exists G low high, exists children : Fin 8 -> D2FlowTree h,
      d2FlowTreeAtPath (j + 2)
          (d2FlowCandidateRun (h + 1 + (j + 2))
            (d2FlowTreeInitial 8192 (h + 1 + (j + 2))) (3 * j)) path =
        .node G low high children /\
      (forall {n : Nat} (s : Finset (Fin n)),
        s.card = d2FlowTotal
          (fun k => d2FlowTreeRootDeficit (children k)) - G ->
        CandidateBotRisePorts h j G low high children s) := by
  obtain ⟨G, low, high, children, hnode, hfit, hcard, heven, htotal,
      hpostfit, hpostempty⟩ :=
    candidate_botRise_path_static_fit_clamped hd hj hwindow path
  let d := h + 1 + (j + 2)
  have hrole := d2FlowCandidate_botRise_current_active_role hd hj hwindow
  have ha : d2FlowCandidateActive d (3 * j) (j + 2) = true := by
    simpa [d, d2FlowCandidateRunActive] using hrole.1
  have hr : d2FlowCandidateRole d (3 * j) (j + 2) = .botRise := by
    simpa [d, d2FlowCandidateRunRole] using hrole.2
  have hwindow' := d2FlowCandidate_botRise_callback_window hd hj hwindow
    (3 * j) (by omega)
  have hnext : d2FlowCandidateActive d (3 * j) (j + 3) = false := by
    simpa [d, d2FlowCandidateRunActive] using hwindow'.1
  have hroute : forall {n : Nat} (s : Finset (Fin n)),
      s.card = d2FlowTotal
        (fun k => d2FlowTreeRootDeficit (children k)) - G ->
      CandidateBotRisePorts h j G low high children s := by
    intro n s hsender
    let widths : Fin 8 -> Nat := fun k =>
      d2FlowTreeRootDeficit (children k) -
        d2FlowTreeRootDeficit
          (d2FlowTreeChild
            (d2FlowStage (d2FlowCandidateActive d (3 * j))
              (d2FlowCandidateRole d (3 * j))
              (d2FlowCandidateQuota d (3 * j))
              (h + 1) (j + 2) (.node G low high children)) k)
    let pi := d2FlowTotal
      (fun k => d2FlowTreeRootDeficit (children k)) - G
    let boundary := d2FlowRankBoundary widths
    have hparts := bot_rise_sender_piece_partition
      (active := d2FlowCandidateActive d (3 * j))
      (role := d2FlowCandidateRole d (3 * j))
      (quota := d2FlowCandidateQuota d (3 * j))
      (h := h) (i := j + 2) (G := G) (low := low) (high := high)
      children s ha hr hnext heven hsender
    have hwidth (k : Fin 8) : widths k = 0 := by
      simp [widths, d2FlowStage_botRise_child_root_deficit children ha hr hnext k]
    have htotalZero : d2FlowTotal widths = 0 := by
      simp [d2FlowTotal, hwidth]
    have hparentCard :
        (destinationPiece (ports := 8) s boundary (pi / 2)
          (s.card - pi / 2) none).card = pi := by
      simpa [pi, boundary] using
        destinationPiece_d2_parent_card s (d2FlowRankBoundary widths) pi
          (by omega) heven
    have hchildCard (k : Fin 8) :
        (destinationPiece (ports := 8) s boundary (pi / 2)
          (s.card - pi / 2) (some k)).card = 0 := by
      have hboundary : d2FlowRankBoundary widths (k.val + 1) = 0 := by
        have hbound := d2FlowRankBoundary_le_total_local widths (k.val + 1)
        rw [htotalZero] at hbound
        omega
      rw [destinationPiece_d2_child_card s widths (pi / 2)
        (s.card - pi / 2) k (by
          rw [hboundary]
          have hpi : pi = s.card := by simpa [pi] using hsender.symm
          omega)]
      exact hwidth k
    exact ⟨hparts.1, hparts.2.1, hparts.2.2,
      by simpa [pi, boundary] using hparentCard,
      by simpa [pi, boundary] using hchildCard⟩
  exact ⟨G, low, high, children, hnode, hroute⟩

end Chvatal.D2BotRiseStaticFit
