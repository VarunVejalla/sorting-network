import D2Stage14Inputs

namespace Chvatal.D2Reserve

theorem d2FlowStageInvInputs_botDesc_of_contract
    {active : Nat -> Bool} {role : Nat -> D2Role}
    {quota : Nat -> D2Role -> Nat} {cap : Nat -> Nat}
    (scale i : Nat) {h : Nat} (tree : D2FlowTree (h + 1))
    (hactive : active i = true) (hrole : role i = .botDesc)
    (hchildren : forall s : Fin 8,
      d2FlowStageInvInputs scale active role quota cap (i + 1)
        (d2FlowTreeChild tree s))
    (hbalance : (d2FlowTreeRootData tree).2.1 +
      (d2FlowTreeRootData tree).2.2 = d2FlowTreeRootDeficit tree)
    (hdeficit : 512 * d2FlowTreeRootDeficit tree ≤ cap i)
    (hquotaCap : 256 * quota i .botDesc ≤ cap i)
    (halloc : quota i .botDesc ≤
      d2FlowTotal (fun s => d2FlowTreeRootDeficit (d2FlowTreeChild tree s)) -
        d2FlowTreeRootDeficit tree)
    (heven : quota i .botDesc % 2 = 0)
    (hleft : cap i ≤ 128 * d2FlowTreeRootDeficit
      (d2FlowTreeChild tree (Fin.mk 0 (by omega))))
    (hright : cap i ≤ 128 * d2FlowTreeRootDeficit
      (d2FlowTreeChild tree (Fin.mk 7 (by omega)))) :
    d2FlowStageInvInputs scale active role quota cap i tree := by
  cases tree with
  | node G low high children =>
    have hb : low + high = G := by
      simpa [d2FlowTreeRootData, d2FlowTreeRootDeficit] using hbalance
    have hd : 512 * G ≤ cap i := by
      simpa [d2FlowTreeRootDeficit] using hdeficit
    have ha : quota i .botDesc ≤
        d2FlowTotal (fun s => d2FlowTreeRootDeficit (children s)) - G := by
      simpa [d2FlowTreeChild, d2FlowTreeRootDeficit] using halloc
    have hl : cap i ≤ 128 * d2FlowTreeRootDeficit (children (Fin.mk 0 (by omega))) := by
      simpa [d2FlowTreeChild] using hleft
    have hr : cap i ≤ 128 * d2FlowTreeRootDeficit (children (Fin.mk 7 (by omega))) := by
      simpa [d2FlowTreeChild] using hright
    simp only [d2FlowStageInvInputs, hactive, if_true, hrole]
    exact ⟨by simpa [d2FlowTreeChild] using hchildren,
      hb, hd, hquotaCap, ha, heven, hl, hr⟩


end Chvatal.D2Reserve
