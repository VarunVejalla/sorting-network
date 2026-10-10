module

public import AKS.Chvatal.KernelSetup
public import AKS.Chvatal.StrangerBounds

@[expose] public section

/-! The real-network stage kernel: `StageKernel` for the execution-defined
placements from `BadSendField` / `FringeSendField` and the outsider bound `P` at stage `t`. -/

namespace Chvatal

/-- The real placement step: parent-sends and children-sends of the executed networks. -/
noncomputable def realPlacementStep {d : ℕ} (hd : 7 ≤ d)
    (nets : ℕ → (b : KBag 64 d) → (n : ℕ) → ComparatorNetwork n)
    (v : Equiv.Perm (Fin (64 ^ d))) (t : ℕ) (ht : t + 1 ≤ tf7 d) :
    PlacementStep d (execPlacement (flowSizes7 d hd) nets v t (by omega))
      (execPlacement (flowSizes7 d hd) nets v (t + 1) ht) where
  fromParent b _ := fromParentK (flowSizes7 d hd) nets v t b
  fromChildren b _ := fromChildrenK (flowSizes7 d hd) nets v t b
  hregs b hb := by
    rw [execPlacement_succ_regs (flowSizes7 d hd) nets v t ht b hb]

noncomputable def realStageKernel {d : ℕ} (hd : 7 ≤ d)
    (nets : ℕ → (b : KBag 64 d) → (n : ℕ) → ComparatorNetwork n)
    (v : Equiv.Perm (Fin (64 ^ d))) (t : ℕ) (ht : t + 1 ≤ tf7 d)
    (hP : OutsiderBoundLe d t
      (execPlacement (flowSizes7 d hd) nets v t (by omega)) id)
    (hBad : BadSendField hd nets v t (by omega))
    (hFringe : FringeSendField hd nets v t (by omega)) :
    StageKernel d t
      (execPlacement (flowSizes7 d hd) nets v t (by omega)) id
      (execPlacement (flowSizes7 d hd) nets v (t + 1) ht) id where
  ht := ht
  step := realPlacementStep hd nets v t ht
  hBadSend0 b hb := hBad b hb
  hFringeSend b r hr1 hrd hb := hFringe b r hr1 hrd hb
  hFromChildren0 b hb :=
    hFromChildren0_of_subset d t _ hP b hb
      (fromChildrenK (flowSizes7 d hd) nets v t b)
      (fun hbd => fromChildrenK_subset (flowSizes7 d hd) nets v t (by omega) b hbd)
      (fun h => fromChildrenK_of_not_lt (flowSizes7 d hd) nets v t b (by omega))
  hFromChildrenR b r hr1 hrd hb :=
    hFromChildrenR_of_subset d t _ hP b hb
      (fromChildrenK (flowSizes7 d hd) nets v t b)
      (fun hbd => fromChildrenK_subset (flowSizes7 d hd) nets v t (by omega) b hbd)
      (fun h => fromChildrenK_of_not_lt (flowSizes7 d hd) nets v t b (by omega))
      r hr1 hrd
  level0 b r hb0 hr := by
    have h0 : (b.strangers (r + 1) id
        ((execPlacement (flowSizes7 d hd) nets v (t + 1) ht).regs b) : ℕ) = 0 :=
      KBag.strangers_eq_zero_of_lt_order b (r + 1) id _ (by norm_num) (by omega)
        (by omega)
    rw [h0]
    have := capacity_pos d 0 (t + 1)
    have hm := invMu_pos
    have hdl := invDelta_pos
    push_cast
    positivity

end Chvatal
