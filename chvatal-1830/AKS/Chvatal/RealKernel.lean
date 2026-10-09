module

public import AKS.Chvatal.KernelSetup
public import AKS.Chvatal.StrangerBounds
public import AKS.Chvatal.StageCountsFill

@[expose] public section

/-! The real-network stage kernel: `StageKernel params7 invariantReal` for the execution-defined
placements from `BadSendField` / `FringeSendField` and the outsider bound `P` at stage `t`. -/

namespace Chvatal

/-- The real placement step: parent-sends and children-sends of the executed networks. -/
noncomputable def realPlacementStep {d : ℕ} (hd : 7 ≤ d)
    (nets : ℕ → (b : KBag 64 d) → (n : ℕ) → ComparatorNetwork n)
    (v : Equiv.Perm (Fin (64 ^ d))) (t : ℕ) (ht : t + 1 ≤ tf7 d) :
    PlacementStep params7 d (execPlacement (flowSizes7 d hd) nets v t (by omega))
      (execPlacement (flowSizes7 d hd) nets v (t + 1) ht) where
  fromParent b _ := fromParentK (flowSizes7 d hd) nets v t b
  fromChildren b _ := fromChildrenK (flowSizes7 d hd) nets v t b
  hregs b hb := by
    rw [execPlacement_succ_regs (flowSizes7 d hd) nets v t ht b hb]
    exact Finset.Subset.refl _

/-- Real local separator quality at the paper budgets. -/
noncomputable def realParentSep (d t : ℕ) (b : KBag 64 d) : LocalSeparatorQuality invariantReal where
  a := capacity params7 d (b.l - 1) t
  ha_pos := capacity_pos _ _ _ _
  ha_le := fun _ => True
  intrusion := invariantReal.epsB * capacity params7 d (b.l - 1) t
  hIntrusion := le_refl _
  fringeSent := fun src => invariantReal.epsF * src
  hFringe := fun _ => le_refl _

noncomputable def realStageKernel {d : ℕ} (hd : 7 ≤ d)
    (nets : ℕ → (b : KBag 64 d) → (n : ℕ) → ComparatorNetwork n)
    (v : Equiv.Perm (Fin (64 ^ d))) (t : ℕ) (ht : t + 1 ≤ tf7 d)
    (hP : OutsiderBoundLe params7 invariantReal d (levelSchedule7 d hd) t
      (execPlacement (flowSizes7 d hd) nets v t (by omega)) id)
    (hBad : BadSendField hd nets v t (by omega))
    (hFringe : FringeSendField hd nets v t (by omega)) :
    StageKernel params7 invariantReal d (levelSchedule7 d hd) t
      (execPlacement (flowSizes7 d hd) nets v t (by omega)) id
      (execPlacement (flowSizes7 d hd) nets v (t + 1) ht) id where
  ht := ht
  step := realPlacementStep hd nets v t ht
  counts := stageCounts_on_schedule params7 invariantReal d (levelSchedule7 d hd) t
  counts_wires := stageCounts_on_schedule_wires params7 invariantReal d (levelSchedule7 d hd) t
  counts_bad := stageCounts_on_schedule_bad params7 invariantReal d (levelSchedule7 d hd) t
  parentSep b _ := realParentSep d t b
  ha_le_cap b hb := le_refl _
  slack0 b hb := slackBound params7 d t b hb
  hSlack0 b hb := le_refl _
  hBadSend0 b hb := by simpa [realParentSep, realPlacementStep] using hBad b hb
  hFringeSend b r hr1 hrd hb := by simpa [realParentSep, realPlacementStep] using hFringe b r hr1 hrd hb
  hFromChildren0 b hb :=
    hFromChildren0_of_subset params7 invariantReal d (levelSchedule7 d hd) t _ hP b hb
      (fromChildrenK (flowSizes7 d hd) nets v t b)
      (fun hbd => fromChildrenK_subset (flowSizes7 d hd) nets v t (by omega) b hbd)
      (fun h => fromChildrenK_of_not_lt (flowSizes7 d hd) nets v t b (by omega))
  hFromChildrenR b r hr1 hrd hb :=
    hFromChildrenR_of_subset params7 invariantReal d (levelSchedule7 d hd) t _ hP b hb
      (fromChildrenK (flowSizes7 d hd) nets v t b)
      (fun hbd => fromChildrenK_subset (flowSizes7 d hd) nets v t (by omega) b hbd)
      (fun h => fromChildrenK_of_not_lt (flowSizes7 d hd) nets v t b (by omega))
      r hr1 hrd
  level0 b r hb0 hr := by
    have h0 : (b.strangers (r + 1) id
        ((execPlacement (flowSizes7 d hd) nets v (t + 1) ht).regs b) (br_ge_one params7) : ℕ) = 0 :=
      KBag.strangers_eq_zero_of_lt_order b (r + 1) id _ (br_ge_one params7) (by omega)
        (by omega)
    rw [h0]
    have := capacity_pos params7 d 0 (t + 1)
    have hm := invariantReal.hmu_pos
    have hdl := invariantReal.hdelta_pos
    push_cast
    positivity

end Chvatal
