import D2ScheduleReserve

namespace Chvatal.D2Reserve

set_option maxHeartbeats 16000000
set_option maxRecDepth 4096
set_option linter.unusedVariables false

/-- The ordinary allocation guard is redundant: the left endpoint alone
contributes at least `cap/128`, while the parent deficit is at most
`cap/512` and the quota at most `cap/256`. -/
theorem d2Flow_quota_le_allocation_of_left_reserve
    {h : Nat} (children : Fin 8 → D2FlowTree h)
    {G cap q : Nat}
    (hdeficit : 512 * G ≤ cap)
    (hquota : 256 * q ≤ cap)
    (hleft : cap ≤ 128 * d2FlowTreeRootDeficit (children 0)) :
    q ≤ d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G := by
  let sizes : Fin 8 → Nat := fun j => d2FlowTreeRootDeficit (children j)
  have hleftTotal : sizes 0 ≤ d2FlowTotal sizes := d2FlowSize_le_total sizes 0
  have hcapTotal : cap ≤ 128 * d2FlowTotal sizes := by
    exact le_trans hleft (Nat.mul_le_mul_left 128 hleftTotal)
  have hGTotal : 4 * G ≤ d2FlowTotal sizes := by
    dsimp [sizes] at hleftTotal ⊢
    nlinarith
  have hqTotal : 2 * q ≤ d2FlowTotal sizes := by
    dsimp [sizes] at hleftTotal ⊢
    nlinarith
  have hsum : q + G ≤ d2FlowTotal sizes := by
    dsimp [sizes] at hGTotal hqTotal ⊢
    nlinarith
  have hsub : q ≤ d2FlowTotal sizes - G := Nat.le_sub_of_add_le hsum
  simpa [sizes] using hsub

/-- Recursive sender-input contract with the allocation conjunct omitted.
The omitted conjunct follows locally from the other numeric gates. -/
def d2FlowStageInvInputsNoAlloc (scale : Nat) (active : Nat → Bool)
    (role : Nat → D2Role) (quota : Nat → D2Role → Nat)
    (cap : Nat → Nat) : {h : Nat} → Nat → D2FlowTree h → Prop
  | 0, _, .leaf _ _ _ => True
  | h + 1, i, .node G low high children =>
      (∀ j, d2FlowStageInvInputsNoAlloc scale active role quota cap
        (i + 1) (children j)) ∧
      (if active i then
        low + high = G ∧
          match role i with
          | .topDesc => G = 0
          | .botRise => True
          | r =>
              512 * G ≤ cap i ∧
              256 * quota i r ≤ cap i ∧
              quota i r % 2 = 0 ∧
              cap i ≤ 128 * d2FlowTreeRootDeficit (children 0) ∧
              cap i ≤ 128 * d2FlowTreeRootDeficit (children 7)
       else True)

/-- The reduced contract implies the original one by deriving allocation
locally at each ordinary sender. -/
theorem d2FlowStageInvInputs_of_noAlloc
    {scale : Nat} {active : Nat → Bool} {role : Nat → D2Role}
    {quota : Nat → D2Role → Nat} {cap : Nat → Nat}
    {h i : Nat} (tree : D2FlowTree h)
    (hinputs : d2FlowStageInvInputsNoAlloc scale active role quota cap i tree) :
    d2FlowStageInvInputs scale active role quota cap i tree := by
  induction tree generalizing i with
  | leaf G low high =>
      trivial
  | @node h G low high children ih =>
      simp only [d2FlowStageInvInputsNoAlloc,
        d2FlowStageInvInputs] at hinputs ⊢
      rcases hinputs with ⟨hchildren, hlocal⟩
      refine ⟨?_, ?_⟩
      · intro j
        exact ih j (hchildren j)
      · by_cases ha : active i = true
        · simp only [ha, if_pos] at hlocal ⊢
          rcases hlocal with ⟨hbalance, hroleData⟩
          refine ⟨hbalance, ?_⟩
          cases hr : role i with
          | topDesc =>
              simpa [hr] using hroleData
          | botRise =>
              simp [hr] at hroleData ⊢
          | topRise =>
              simp only [hr] at hroleData
              rcases hroleData with ⟨hdeficit, hquota, heven, hleft, hright⟩
              have halloc := d2Flow_quota_le_allocation_of_left_reserve
                children hdeficit hquota hleft
              exact ⟨hdeficit, hquota, halloc, heven, hleft, hright⟩
          | mid =>
              simp only [hr] at hroleData
              rcases hroleData with ⟨hdeficit, hquota, heven, hleft, hright⟩
              have halloc := d2Flow_quota_le_allocation_of_left_reserve
                children hdeficit hquota hleft
              exact ⟨hdeficit, hquota, halloc, heven, hleft, hright⟩
          | botDesc =>
              simp only [hr] at hroleData
              rcases hroleData with ⟨hdeficit, hquota, heven, hleft, hright⟩
              have halloc := d2Flow_quota_le_allocation_of_left_reserve
                children hdeficit hquota hleft
              exact ⟨hdeficit, hquota, halloc, heven, hleft, hright⟩
        · simp only [ha] at hlocal ⊢
          trivial

/-- One-stage invariant preservation only needs the reduced sender-input
contract; the original allocation premise is recovered above. -/
theorem d2FlowStage_preserves_inv_of_noAlloc_inputs
    {h i scale : Nat} {active : Nat → Bool}
    {role : Nat → D2Role} {quota : Nat → D2Role → Nat}
    {cap : Nat → Nat} (tree : D2FlowTree h)
    (hinv : d2FlowTreeInv scale tree)
    (hinputs : d2FlowStageInvInputsNoAlloc scale active role quota cap i tree) :
    d2FlowTreeInv scale (d2FlowStage active role quota h i tree) := by
  exact d2FlowStage_preserves_inv_of_inputs tree hinv
    (d2FlowStageInvInputs_of_noAlloc tree hinputs)

end Chvatal.D2Reserve
