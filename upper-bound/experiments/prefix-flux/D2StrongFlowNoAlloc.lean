import D2AllocationFromEndpointReserve
import D2StrongFlowStage

namespace Chvatal.D2Reserve

set_option linter.unusedVariables false

/-- The affine sender contract with its allocation conjunct omitted. The
left endpoint reserve and affine deficit/quota bounds already force enough
total child mass to pay the quota. -/
def d2FlowStageAffineInputsNoAlloc (active : Nat -> Bool)
    (role : Nat -> D2Role) (quota : Nat -> D2Role -> Nat)
    (cap : Nat -> Nat) : {h : Nat} -> Nat -> D2FlowTree h -> Prop
  | 0, _, .leaf _ _ _ => True
  | h + 1, i, .node G low high children =>
      (forall j, d2FlowStageAffineInputsNoAlloc active role quota cap
        (i + 1) (children j)) /\
      (if active i then
        low + high = G /\
          match role i with
          | .topDesc => G = 0
          | .botRise => True
          | .topRise =>
              G = 0 /\ 256 * quota i .topRise <= cap i /\
                quota i .topRise % 2 = 0 /\
                cap i <= 128 * d2FlowTreeRootDeficit (children 0) /\
                cap i <= 128 * d2FlowTreeRootDeficit (children 7)
          | .mid | .botDesc =>
              8192 * G + 7 <= 15 * cap i /\
                4096 * quota i (role i) <= 15 * cap i /\
                quota i (role i) % 2 = 0 /\
                cap i <= 128 * d2FlowTreeRootDeficit (children 0) /\
                cap i <= 128 * d2FlowTreeRootDeficit (children 7)
       else True)

/-- A recursively stated no-allocation input contract restricts to every
selected subtree, with the callback level advanced by the path length. -/
theorem d2FlowStageAffineInputsNoAlloc_atPath
    {active : Nat -> Bool} {role : Nat -> D2Role}
    {quota : Nat -> D2Role -> Nat} {cap : Nat -> Nat}
    {h n i : Nat} (tree : D2FlowTree (h + n))
    (path : D2FlowPath n)
    (hinputs : d2FlowStageAffineInputsNoAlloc active role quota cap i tree) :
    d2FlowStageAffineInputsNoAlloc active role quota cap (i + n)
      (d2FlowTreeAtPath n tree path) := by
  induction path generalizing h i with
  | nil => simpa [d2FlowTreeAtPath] using hinputs
  | @cons n j tail ih =>
      cases tree with
      | node G low high children =>
          simp only [d2FlowStageAffineInputsNoAlloc] at hinputs ⊢
          rcases hinputs with ⟨hchildren, _⟩
          change d2FlowStageAffineInputsNoAlloc active role quota cap
            (i + (n + 1)) (d2FlowTreeAtPath n (children j) tail)
          have hselected := ih (h := h) (i := i + 1)
            (tree := children j) (hchildren j)
          simpa only [show i + 1 + n = i + (n + 1) by omega] using hselected

/-- Recover the affine contract's allocation field locally from the left
reserve. -/
theorem d2FlowStageAffineInputs_of_noAlloc
    {active : Nat -> Bool} {role : Nat -> D2Role}
    {quota : Nat -> D2Role -> Nat} {cap : Nat -> Nat}
    {h i : Nat} (tree : D2FlowTree h)
    (hinputs : d2FlowStageAffineInputsNoAlloc active role quota cap i tree) :
    d2FlowStageAffineInputs active role quota cap i tree := by
  induction tree generalizing i with
  | leaf G low high =>
      trivial
  | @node h G low high children ih =>
      simp only [d2FlowStageAffineInputsNoAlloc,
        d2FlowStageAffineInputs] at hinputs ⊢
      rcases hinputs with ⟨hchildren, hlocal⟩
      refine ⟨?_, ?_⟩
      · intro j
        exact ih j (hchildren j)
      · by_cases ha : active i = true
        · simp only [ha, if_pos] at hlocal ⊢
          rcases hlocal with ⟨hbalance, hroleData⟩
          refine ⟨hbalance, ?_⟩
          cases hr : role i with
          | topDesc => simpa [hr] using hroleData
          | botRise => simp [hr] at hroleData ⊢
          | topRise =>
              simp only [hr] at hroleData
              rcases hroleData with ⟨hGzero, hquota, heven, hleft, hright⟩
              have hdeficit : 512 * G <= cap i := by omega
              have halloc := d2Flow_quota_le_allocation_of_left_reserve
                children hdeficit hquota hleft
              exact ⟨hGzero, hquota, halloc, heven, hleft, hright⟩
          | mid =>
              simp only [hr] at hroleData
              rcases hroleData with ⟨hprofile, hquotaProfile, heven,
                hleft, hright⟩
              have hcaps := d2_affine_profile_implies_existing_local_caps
                (G := G) (pi := quota i .mid) (c := cap i)
                (Or.inr ⟨hprofile, hquotaProfile⟩)
              have halloc := d2Flow_quota_le_allocation_of_left_reserve
                children hcaps.1 hcaps.2 hleft
              exact ⟨hprofile, hquotaProfile, halloc, heven, hleft, hright⟩
          | botDesc =>
              simp only [hr] at hroleData
              rcases hroleData with ⟨hprofile, hquotaProfile, heven,
                hleft, hright⟩
              have hcaps := d2_affine_profile_implies_existing_local_caps
                (G := G) (pi := quota i .botDesc) (c := cap i)
                (Or.inr ⟨hprofile, hquotaProfile⟩)
              have halloc := d2Flow_quota_le_allocation_of_left_reserve
                children hcaps.1 hcaps.2 hleft
              exact ⟨hprofile, hquotaProfile, halloc, heven, hleft, hright⟩
        · simp only [ha] at hlocal ⊢
          exact True.intro

/-- Stage preservation can consume the reduced affine contract directly. -/
theorem d2FlowStage_preserves_inv_of_affine_noAlloc_inputs
    {h i scale : Nat} {active : Nat -> Bool} {role : Nat -> D2Role}
    {quota : Nat -> D2Role -> Nat} {cap : Nat -> Nat}
    (tree : D2FlowTree h) (hinv : d2FlowTreeInv scale tree)
    (hinputs : d2FlowStageAffineInputsNoAlloc active role quota cap i tree) :
    d2FlowTreeInv scale (d2FlowStage active role quota h i tree) :=
  d2FlowStage_preserves_inv_of_affine_inputs tree hinv
    (d2FlowStageAffineInputs_of_noAlloc tree hinputs)

/-- The reduced affine provider still suffices for any finite candidate run. -/
theorem d2FlowCandidateRun_preserves_inv_of_affine_noAlloc_all_inputs
    (d n : Nat) (initial : D2FlowTree d)
    (hinitial : d2FlowTreeInv 8192 initial)
    (hinputs : forall t, t < n ->
      d2FlowStageAffineInputsNoAlloc
        (d2FlowCandidateActive d t)
        (d2FlowCandidateRole d t)
        (d2FlowCandidateQuota d t)
        (fun i => d2FlowCandidateCapacity d i t) 0
        (d2FlowCandidateRun d initial t)) :
    d2FlowTreeInv 8192 (d2FlowCandidateRun d initial n) := by
  apply d2FlowCandidateRun_preserves_inv_of_affine_all_inputs
    d n initial hinitial
  intro t ht
  exact d2FlowStageAffineInputs_of_noAlloc
    (d2FlowCandidateRun d initial t) (hinputs t ht)

end Chvatal.D2Reserve
