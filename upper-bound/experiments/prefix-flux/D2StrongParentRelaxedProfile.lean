import D2TolerantSenderFactor

namespace Chvatal.D2Reserve

/-! At a strong `botDesc` cut, equal native child deficits still give the
endpoint/interior profile needed by the relaxed sender-factor gate. The
relaxed cap `4096*G ≤ 23*cOld` is sufficient: each cut front is at most
`(46+15)/8192` of `cOld`, while one child has size `64/8192` of `cOld`.
-/

theorem d2_strong_parent_relaxed_cut_profile
    {cOld U half G low high : Nat}
    (hU : 128 * U = cOld)
    (hhalf : 8192 * half = 15 * cOld)
    (hG : 4096 * G ≤ 23 * cOld)
    (hbalance : low + high = G) :
    (∀ j : Fin 8,
      d2FlowCutChild (d2FlowPosition (fun _ : Fin 8 => U) j) U
        (low + half) (8 * U - high - half) =
        if j.val = 0 then (low + half, low + half, 0)
        else if j.val = 7 then (high + half, 0, high + half)
        else (0, 0, 0)) ∧
    8192 * (U - (low + half)) + 8192 * low = 49 * cOld ∧
    8192 * (U - (high + half)) + 8192 * high = 49 * cOld ∧
    8192 * U = 64 * cOld := by
  have hGscaled : 8192 * G ≤ 46 * cOld := by nlinarith
  have hlow : low ≤ G := by omega
  have hhigh : high ≤ G := by omega
  have hUscaled : 8192 * U = 64 * cOld := by nlinarith
  have hleft : low + half ≤ U := by nlinarith
  have htail : high + half ≤ U := by nlinarith
  have hshape := d2FlowCutChild_uniform_asymmetric
    (u := U) (left := low + half) (tail := high + half) hleft htail
  refine ⟨?_, ?_, ?_, hUscaled⟩
  · intro j
    simpa [d2FlowPosition_uniform,
      show 8 * U - high - half = 8 * U - (high + half) by omega]
      using hshape j
  · have hmul' : 8192 * (low + half) = 8192 * low + 15 * cOld := by
      rw [Nat.mul_add, hhalf]
    have hsub : U - (low + half) + (low + half) = U := Nat.sub_add_cancel hleft
    have hmulsub := congrArg (fun x : Nat => 8192 * x) hsub
    change 8192 * (U - (low + half) + (low + half)) = 8192 * U at hmulsub
    rw [Nat.mul_add, hmul', hUscaled] at hmulsub
    omega
  · have hmul : 8192 * (high + half) = 8192 * high + 15 * cOld := by
      rw [Nat.mul_add, hhalf]
    have hsub : U - (high + half) + (high + half) = U := Nat.sub_add_cancel htail
    have hmulsub := congrArg (fun x : Nat => 8192 * x) hsub
    change 8192 * (U - (high + half) + (high + half)) = 8192 * U at hmulsub
    rw [Nat.mul_add, hmul, hUscaled] at hmulsub
    omega

theorem d2_strong_parent_relaxed_port_profile
    {cOld U half G low high : Nat} {c : Rat}
    (childRho : Fin 8 → Rat)
    (hU : 128 * U = cOld)
    (hhalf : 8192 * half = 15 * cOld)
    (hG : 4096 * G ≤ 23 * cOld)
    (hbalance : low + high = G)
    (hc : 0 < c)
    (hcOld : (cOld : Rat) = 16 * c)
    (hchildRho : ∀ j : Fin 8, childRho j =
      ((U - (d2FlowCutChild
        (d2FlowPosition (fun _ : Fin 8 => U) j) U
        (low + half) (8 * U - high - half)).1 : Nat) : Rat) / (32 * c)) :
    childRho 0 ≤ 49 / 16384 ∧ childRho 7 ≤ 49 / 16384 ∧
      (∀ j : Fin 8, j.val ≠ 0 → j.val ≠ 7 → childRho j ≤ 1 / 256) := by
  have hprofile := d2_strong_parent_relaxed_cut_profile hU hhalf hG hbalance
  have hfirst : childRho 0 ≤ 49 / 16384 := by
    rw [hchildRho]
    have hshape := hprofile.1 0
    simp only [Fin.val_zero, if_true] at hshape
    have hcut : (d2FlowCutChild
        (d2FlowPosition (fun _ : Fin 8 => U) 0) U
        (low + half) (8 * U - high - half)).1 = low + half := by
      simpa using congrArg Prod.fst hshape
    have hblock : 8192 * (U - (low + half)) + 8192 * low = 49 * cOld :=
      hprofile.2.1
    have hbound : (8192 : Rat) *
        ((U - (low + half) : Nat) : Rat) ≤ 49 * (cOld : Rat) := by
      have hlo : (0 : Rat) ≤ (low : Nat) := by positivity
      have heq := congrArg (fun x : Nat => (x : Rat)) hblock
      norm_num at heq
      nlinarith
    rw [hcOld] at hbound
    rw [hcut]
    apply (div_le_iff₀ (by positivity : (0 : Rat) < 32 * c)).2
    nlinarith [hbound]
  have hlast : childRho 7 ≤ 49 / 16384 := by
    rw [hchildRho]
    have hshape := hprofile.1 7
    have hval : (⟨7, by omega⟩ : Fin 8).val = 7 := rfl
    simp only [hval, if_pos, if_false] at hshape
    have hcut : (d2FlowCutChild
        (d2FlowPosition (fun _ : Fin 8 => U) 7) U
        (low + half) (8 * U - high - half)).1 = high + half := by
      simpa using congrArg Prod.fst hshape
    have hblock : 8192 * (U - (high + half)) + 8192 * high = 49 * cOld :=
      hprofile.2.2.1
    have hbound : (8192 : Rat) *
        ((U - (high + half) : Nat) : Rat) ≤ 49 * (cOld : Rat) := by
      have hhi : (0 : Rat) ≤ (high : Nat) := by positivity
      have heq := congrArg (fun x : Nat => (x : Rat)) hblock
      norm_num at heq
      nlinarith
    rw [hcOld] at hbound
    rw [hcut]
    apply (div_le_iff₀ (by positivity : (0 : Rat) < 32 * c)).2
    nlinarith [hbound]
  refine ⟨hfirst, hlast, ?_⟩
  intro j hj0 hj7
  rw [hchildRho]
  have hshape := hprofile.1 j
  have hjval0 : j.val ≠ 0 := hj0
  have hjval7 : j.val ≠ 7 := hj7
  simp only [hjval0, hjval7, if_false] at hshape
  have hcut : (d2FlowCutChild
      (d2FlowPosition (fun _ : Fin 8 => U) j) U
      (low + half) (8 * U - high - half)).1 = 0 := by
    simpa using congrArg Prod.fst hshape
  have hUscaled : 8192 * U = 64 * cOld := hprofile.2.2.2
  have hUrat : (8192 : Rat) * (U : Rat) = 64 * (cOld : Rat) := by
    exact_mod_cast hUscaled
  rw [hcOld] at hUrat
  rw [hcut, Nat.sub_zero]
  apply (div_le_iff₀ (by positivity : (0 : Rat) < 32 * c)).2
  nlinarith [hUrat]

theorem d2_exceptional_two_step_sender_factor_279_of_strong_parent
    {a c gOld gNow rhoOld : Rat}
    {cOld U half G low high : Nat}
    (childRho : Fin 8 → Rat)
    (hU : 128 * U = cOld)
    (hhalf : 8192 * half = 15 * cOld)
    (hG : 4096 * G ≤ 23 * cOld)
    (hbalance : low + high = G)
    (hc : 0 < c) (hcOld : (cOld : Rat) = 16 * c)
    (hchildRho : ∀ j : Fin 8, childRho j =
      ((U - (d2FlowCutChild
        (d2FlowPosition (fun _ : Fin 8 => U) j) U
        (low + half) (8 * U - high - half)).1 : Nat) : Rat) / (32 * c))
    (hid : a / c = 16 * gOld + 16 * rhoOld +
      32 * (Finset.univ.sum childRho) - gNow)
    (hgOld : gOld ≤ 23 / 4096) (hgNow : 0 ≤ gNow)
    (hrhoOld : rhoOld ≤ 15 / 4096) :
    a / c ≤ 279 / 256 := by
  have hprofile := d2_strong_parent_relaxed_port_profile childRho
    hU hhalf hG hbalance hc hcOld hchildRho
  have hsum := d2_botRise_child_quota_sum_of_endpoint_caps childRho
    hprofile.1 hprofile.2.1 hprofile.2.2
  exact d2_two_step_sender_factor_279_of_tolerant_budget childRho
    hid hgOld hgNow (Or.inl ⟨hrhoOld, hsum⟩)

theorem d2FlowStage_strong_cut_botRise_child_port
    {h i G low high U half : Nat}
    {activeOld : Nat → Bool} {roleOld : Nat → D2Role}
    {quotaOld : Nat → D2Role → Nat}
    {activeNext : Nat → Bool} {roleNext : Nat → D2Role}
    {quotaNext : Nat → D2Role → Nat}
    (children : Fin 8 → D2FlowTree (h + 1))
    (hactiveOld : activeOld i = true) (hroleOld : roleOld i = .botDesc)
    (hquotaOld : quotaOld i .botDesc = 2 * half)
    (hchildInactive : activeOld (i + 1) = false)
    (hgrandchildInactive : activeOld (i + 2) = false)
    (hnextActive : activeNext (i + 1) = true)
    (hnextRole : roleNext (i + 1) = .botRise)
    (hchildRoot : ∀ j, d2FlowTreeRootDeficit (children j) = U)
    (hgrandchildRoot : ∀ j k,
      d2FlowTreeRootDeficit (d2FlowTreeChild (children j) k) = U / 8)
    (hUdiv : U % 8 = 0)
    (hleft : low + half ≤ U) (hright : high + half ≤ U) :
    let after := d2FlowStage activeOld roleOld quotaOld (h + 2) i
      (.node G low high children)
    ∀ j : Fin 8,
      d2FlowStagePort activeNext roleNext quotaNext (h + 1) (i + 1)
        (d2FlowTreeChild after j) =
          U - d2FlowTreeRootDeficit (d2FlowTreeChild after j) := by
  dsimp only
  let after := d2FlowStage activeOld roleOld quotaOld (h + 2) i
    (.node G low high children)
  have htotal : d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) =
      8 * U := by
    unfold d2FlowTotal
    simp_rw [hchildRoot]
    norm_num [Fin.sum_univ_succ]
  have htotalConst : d2FlowTotal (fun _ : Fin 8 => U) = 8 * U := by
    unfold d2FlowTotal
    norm_num [Fin.sum_univ_succ]
  have hcutShape : ∀ j : Fin 8,
      d2FlowCutChild (d2FlowPosition (fun _ : Fin 8 => U) j) U
        (low + half) (8 * U - (high + half)) =
        if j.val = 0 then (low + half, low + half, 0)
        else if j.val = 7 then (high + half, 0, high + half)
        else (0, 0, 0) :=
    by
      simpa only [d2FlowPosition_uniform] using
        d2FlowCutChild_uniform_asymmetric hleft hright
  have hquotaHalf : quotaOld i (roleOld i) / 2 = half := by
    rw [hroleOld, hquotaOld]
    omega
  have hchildShape : ∀ j : Fin 8,
      d2FlowTreeRootDeficit (d2FlowTreeChild after j) =
        if j.val = 0 then low + half
        else if j.val = 7 then high + half else 0 := by
    intro j
    have hdef := d2FlowStage_regular_child_deficit
      (active := activeOld) (role := roleOld) (quota := quotaOld)
      (h := h + 1) (i := i) (G := G) (low := low) (high := high)
      children hactiveOld (Or.inr (Or.inr hroleOld)) j
    dsimp [after] at hdef ⊢
    have hpositions : (fun k : Fin 8 => d2FlowTreeRootDeficit (children k)) =
        (fun _ : Fin 8 => U) := funext hchildRoot
    rw [hpositions] at hdef
    rw [hchildRoot j] at hdef
    rw [hquotaHalf, htotalConst] at hdef
    rw [hdef]
    have hs := hcutShape j
    have hargs : 8 * U - high - half = 8 * U - (high + half) := by omega
    rw [hargs]
    have hproj := congrArg Prod.fst hs
    by_cases hj0 : j.val = 0
    · simpa [hj0] using hproj
    · by_cases hj7 : j.val = 7
      · simpa [hj0, hj7] using hproj
      · simpa [hj0, hj7] using hproj
  have hcover : ∀ j : Fin 8,
      d2FlowTreeRootDeficit (d2FlowTreeChild after j) ≤ U := by
    intro j
    rw [hchildShape j]
    split_ifs <;> omega
  have hgrandAfter : ∀ j k : Fin 8,
      d2FlowTreeRootDeficit
        (d2FlowTreeChild (d2FlowTreeChild after j) k) = U / 8 := by
    intro j k
    have hstage := d2FlowStage_regular_child_grandchild_stage
      (active := activeOld) (role := roleOld) (quota := quotaOld)
      (h := h) (i := i) (G := G) (low := low) (high := high)
      children hactiveOld (Or.inr (Or.inr hroleOld)) hchildInactive j k
    have hroot := d2FlowStage_root_deficit_of_inactive
      (role := roleOld) (quota := quotaOld)
      (d2FlowTreeChild (children j) k) hgrandchildInactive
    dsimp [after] at hstage ⊢
    rw [hstage, hroot]
    exact hgrandchildRoot j k
  have htotalGrand : ∀ j : Fin 8,
      d2FlowTotal (fun k => d2FlowTreeRootDeficit
        (d2FlowTreeChild (d2FlowTreeChild after j) k)) = U := by
    intro j
    unfold d2FlowTotal
    simp_rw [hgrandAfter j]
    have hsum : (Finset.univ.sum fun _ : Fin 8 => U / 8) = 8 * (U / 8) := by
      norm_num [Fin.sum_univ_succ]
    rw [hsum]
    omega
  intro j
  cases hpost : d2FlowTreeChild after j with
  | node postG postLow postHigh postChildren =>
      have htotalPost := htotalGrand j
      rw [hpost] at htotalPost
      simp only [d2FlowTreeChild, d2FlowTreeRootDeficit] at htotalPost
      have htotalPost' : d2FlowTotal
          (fun k => d2FlowTreeRootDeficit (postChildren k)) = U := by
        change d2FlowTotal
          (fun k => d2FlowTreeRootDeficit (postChildren k)) = U
        exact htotalPost
      have hcoverPost : postG ≤ d2FlowTotal
          (fun k => d2FlowTreeRootDeficit (postChildren k)) := by
        have hjcover := hcover j
        rw [hpost] at hjcover
        have hjcover' : postG ≤ U := by
          simpa [d2FlowTreeRootDeficit] using hjcover
        omega
      have hport := d2FlowStage_botRise_actual_port
        (quota := quotaNext) (G := postG) (low := postLow) (high := postHigh)
        postChildren hnextActive hnextRole hcoverPost
      calc
        d2FlowStagePort activeNext roleNext quotaNext (h + 1) (i + 1)
            (D2FlowTree.node postG postLow postHigh postChildren) =
          d2FlowTotal (fun k => d2FlowTreeRootDeficit (postChildren k)) - postG := by
            simpa [d2FlowTreeRootDeficit] using hport
        _ = U - d2FlowTreeRootDeficit
              (D2FlowTree.node postG postLow postHigh postChildren) := by
            rw [htotalPost']
            rfl

end Chvatal.D2Reserve
