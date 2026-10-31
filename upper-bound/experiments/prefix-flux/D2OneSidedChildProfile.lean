import D2ScheduleReserve
import D2RankCutTail

namespace Chvatal.D2Reserve

set_option maxHeartbeats 3000000

/-- Under the standard endpoint-reserve hypotheses, the ordinary interval
cut writes only a low component to child 0, only a high component to child 7,
and zero data to every interior child. -/
theorem d2_ordinary_cut_output_sides_of_reserve
    {a G total low high pi half c : Nat} (size pos : Fin 8 -> Nat)
    (hbalance : low + high = G) (hconserve : a + G = total)
    (hpiAlloc : pi <= a) (heven : pi = 2 * half)
    (hG : 512 * G <= c) (hlow : low <= G) (hhigh : high <= G)
    (hpi : 256 * pi <= c) (hleftReserve : c <= 128 * size 0)
    (hrightReserve : c <= 128 * size 7)
    (hstart : pos 0 = 0)
    (hcontig : forall k : Nat, (hk : k < 7) ->
      pos ⟨k + 1, by omega⟩ = pos ⟨k, by omega⟩ + size ⟨k, by omega⟩)
    (htotal : pos 7 + size 7 = total) :
    d2FlowCutChild (pos 0) (size 0) (low + half) (total - high - half) =
        (low + half, low + half, 0) /\
      d2FlowCutChild (pos 7) (size 7) (low + half) (total - high - half) =
        (high + half, 0, high + half) /\
      forall j : Fin 8, 0 < j.val -> j.val < 7 ->
        d2FlowCutChild (pos j) (size j) (low + half)
          (total - high - half) = (0, 0, 0) := by
  have hshape := d2_ordinary_update_shape_of_reserve size pos hbalance
    hconserve hpiAlloc heven hG hlow hhigh hpi hleftReserve hrightReserve
    hstart hcontig htotal
  have hvalid := d2_ordinary_cut_fronts_valid hbalance hconserve hpiAlloc
    heven hG hlow hhigh hpi hleftReserve hrightReserve
  have hordered := d2_contiguous_children_ordered size pos hstart hcontig
  have hfirstLeft : d2LeftCut (pos 0) (size 0) (low + half) = low + half := by
    rw [hstart]
    unfold d2LeftCut
    simp only [zero_add]
    exact Nat.min_eq_right hvalid.2.1
  have hfirstRight : d2RightCut (pos 0) (size 0)
      (total - high - half) = 0 := by
    unfold d2RightCut
    rw [hstart]
    have hsizeLe : size 0 <= total - high - half := by
      have hpos7 : pos 7 <= total - high - half := by
        rw [show total - high - half = total - (high + half) by omega]
        omega
      exact le_trans hordered.1 hpos7
    simp
    omega
  have hlastLeft : d2LeftCut (pos 7) (size 7) (low + half) = 0 := by
    unfold d2LeftCut
    have hleftPos : low + half <= pos 7 := by
      have hfirst : low + half <= size 0 := hvalid.2.1
      omega
    have htotal' : pos 7 + size 7 = total := htotal
    rw [htotal']
    omega
  have hlastRight : d2RightCut (pos 7) (size 7)
      (total - high - half) = high + half := by
    unfold d2RightCut
    have hrightStart : pos 7 <= total - high - half := by
      rw [show total - high - half = total - (high + half) by omega]
      have hfit : high + half <= size 7 := hvalid.2.2
      omega
    rw [Nat.max_eq_right hrightStart, htotal]
    omega
  refine ⟨?_, ?_, ?_⟩
  · unfold d2FlowCutChild
    simp [hfirstLeft, hfirstRight]
  · unfold d2FlowCutChild
    simp [hlastLeft, hlastRight]
  · intro j hjlo hjhi
    have hinterior := hshape.2.2 j hjlo hjhi
    have hcuts : d2LeftCut (pos j) (size j) (low + half) +
        d2RightCut (pos j) (size j) (total - high - half) = 0 := by
      simpa [d2LocalChildDeficitUpdate] using hinterior
    have hleft : d2LeftCut (pos j) (size j) (low + half) = 0 := by omega
    have hright : d2RightCut (pos j) (size j)
        (total - high - half) = 0 := by omega
    unfold d2FlowCutChild
    simp [hleft, hright]

/-- The same endpoint-only shape is stored in the concrete recursive flow
tree after an ordinary sender stage. -/
theorem d2FlowStage_regular_child_rootdata_profile
    {active : Nat -> Bool} {role : Nat -> D2Role}
    {quota : Nat -> D2Role -> Nat}
    {h i G low high pi half c : Nat}
    (children : Fin 8 -> D2FlowTree h)
    (ha : active i = true)
    (hr : role i = .topRise \/ role i = .mid \/ role i = .botDesc)
    (hbalance : low + high = G)
    (hcover : G <= d2FlowTotal
      (fun j => d2FlowTreeRootDeficit (children j)))
    (hpiAlloc : pi <= d2FlowTotal
      (fun j => d2FlowTreeRootDeficit (children j)) - G)
    (hpiEq : pi = quota i (role i))
    (heven : pi = 2 * half)
    (hG : 512 * G <= c) (hlow : low <= G) (hhigh : high <= G)
    (hpi : 256 * pi <= c)
    (hleftReserve : c <= 128 * d2FlowTreeRootDeficit (children 0))
    (hrightReserve : c <= 128 * d2FlowTreeRootDeficit (children 7)) :
    d2FlowTreeRootData
        (d2FlowTreeChild
          (d2FlowStage active role quota (h + 1) i
            (.node G low high children)) 0) =
        (low + half, low + half, 0) /\
      d2FlowTreeRootData
        (d2FlowTreeChild
          (d2FlowStage active role quota (h + 1) i
            (.node G low high children)) 7) =
        (high + half, 0, high + half) /\
      forall j : Fin 8, 0 < j.val -> j.val < 7 ->
        d2FlowTreeRootData
          (d2FlowTreeChild
            (d2FlowStage active role quota (h + 1) i
              (.node G low high children)) j) = (0, 0, 0) := by
  let sizes : Fin 8 -> Nat := fun j => d2FlowTreeRootDeficit (children j)
  let positions : Fin 8 -> Nat := d2FlowPosition sizes
  let total := d2FlowTotal sizes
  have hconserve : total - G + G = total := Nat.sub_add_cancel hcover
  have hhalf : quota i (role i) / 2 = half := by
    rw [← hpiEq, heven]
    omega
  have hreserveLeft : c <= 128 * sizes 0 := by simpa [sizes] using hleftReserve
  have hreserveRight : c <= 128 * sizes 7 := by simpa [sizes] using hrightReserve
  have hpositions := d2FlowPositions_contiguous sizes
  have hprofile := d2_ordinary_cut_output_sides_of_reserve
    sizes positions hbalance hconserve hpiAlloc heven hG hlow hhigh hpi
    hreserveLeft hreserveRight hpositions.1 hpositions.2.1 (by
      simpa [positions, total] using hpositions.2.2)
  have hcut := d2FlowStage_regular_child_setroot
    (quota := quota) (h := h) (i := i) (G := G) (low := low) (high := high)
    children ha hr 0
  have hcut7 := d2FlowStage_regular_child_setroot
    (quota := quota) (h := h) (i := i) (G := G) (low := low) (high := high)
    children ha hr 7
  have hcutj (j : Fin 8) := d2FlowStage_regular_child_setroot
    (quota := quota) (h := h) (i := i) (G := G) (low := low) (high := high)
    children ha hr j
  constructor
  · rw [hcut, d2FlowTreeRootData_setRoot]
    simpa [d2FlowCutChild, sizes, positions, total, hhalf, hpiEq] using hprofile.1
  constructor
  · rw [hcut7, d2FlowTreeRootData_setRoot]
    simpa [d2FlowCutChild, sizes, positions, total, hhalf, hpiEq] using hprofile.2.1
  · intro j hjlo hjhi
    rw [hcutj j, d2FlowTreeRootData_setRoot]
    simpa [d2FlowCutChild, sizes, positions, total, hhalf, hpiEq] using
      hprofile.2.2 j hjlo hjhi

/-- The endpoint-only flow profile lets the abstract one-sided tail algebra
charge a single local error allowance, provided the flow-side low/high fields
are the quantities to which the rank-tail provider applies. This theorem is
deliberately conditional: it does not identify those fields with actual
key-rank outsider counts. -/
theorem d2FlowStage_regular_child_flow_tail_bound
    {active : Nat -> Bool} {role : Nat -> D2Role}
    {quota : Nat -> D2Role -> Nat}
    {h i G low high pi half c margin err : Nat}
    (children : Fin 8 -> D2FlowTree h)
    (ha : active i = true)
    (hr : role i = .topRise \/ role i = .mid \/ role i = .botDesc)
    (hbalance : low + high = G)
    (hcover : G <= d2FlowTotal
      (fun j => d2FlowTreeRootDeficit (children j)))
    (hpiAlloc : pi <= d2FlowTotal
      (fun j => d2FlowTreeRootDeficit (children j)) - G)
    (hpiEq : pi = quota i (role i))
    (heven : pi = 2 * half)
    (hG : 512 * G <= c) (hlow : low <= G) (hhigh : high <= G)
    (hpi : 256 * pi <= c)
    (hleftReserve : c <= 128 * d2FlowTreeRootDeficit (children 0))
    (hrightReserve : c <= 128 * d2FlowTreeRootDeficit (children 7)) :
    forall j : Fin 8,
      Chvatal.D2RankCutTail.rankCutTail
          (d2FlowTreeRootData
            (d2FlowTreeChild
              (d2FlowStage active role quota (h + 1) i
                (.node G low high children)) j)).2.1 margin err +
        Chvatal.D2RankCutTail.rankCutTail
          (d2FlowTreeRootData
            (d2FlowTreeChild
              (d2FlowStage active role quota (h + 1) i
                (.node G low high children)) j)).2.2 margin err <=
      err + max (
        (d2FlowTreeRootData
          (d2FlowTreeChild
            (d2FlowStage active role quota (h + 1) i
              (.node G low high children)) j)).2.1 +
        (d2FlowTreeRootData
          (d2FlowTreeChild
            (d2FlowStage active role quota (h + 1) i
              (.node G low high children)) j)).2.2 - margin) 0 := by
  have hprofile := d2FlowStage_regular_child_rootdata_profile
    children ha hr hbalance hcover hpiAlloc hpiEq heven hG hlow hhigh hpi
    hleftReserve hrightReserve
  intro j
  have hone :
      (d2FlowTreeRootData
        (d2FlowTreeChild
          (d2FlowStage active role quota (h + 1) i
            (.node G low high children)) j)).2.1 = 0 \/
      (d2FlowTreeRootData
        (d2FlowTreeChild
          (d2FlowStage active role quota (h + 1) i
            (.node G low high children)) j)).2.2 = 0 := by
    by_cases hj0 : j.val = 0
    · have hj : j = 0 := Fin.ext hj0
      subst j
      rw [hprofile.1]
      exact Or.inr rfl
    · by_cases hj7 : j.val = 7
      · have hj : j = 7 := Fin.ext hj7
        subst j
        rw [hprofile.2.1]
        exact Or.inl rfl
      · have hjlo : 0 < j.val := by omega
        have hjhi : j.val < 7 := by omega
        rw [hprofile.2.2 j hjlo hjhi]
        exact Or.inl rfl
  simpa only [Nat.max_eq_left (Nat.zero_le _)] using
    (Chvatal.D2RankCutTail.rankCutTail_one_sided_le
      _ _ _ _ hone)

end Chvatal.D2Reserve
