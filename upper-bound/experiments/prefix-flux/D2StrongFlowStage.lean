import D2StrongDeficitPropagation

namespace Chvatal.D2Reserve

/-- The sharp affine sender envelope composes with the actual recursive-flow
cut: every child root after an ordinary update satisfies the same envelope at
the doubled capacity. This is the concrete tree-level version of the local
arithmetic preservation lemma. -/
theorem d2FlowStage_regular_child_affine_deficit
    {active : Nat → Bool} {role : Nat → D2Role}
    {quota : Nat → D2Role → Nat} {h i G low high allocation c : Nat}
    (children : Fin 8 → D2FlowTree h)
    (ha : active i = true)
    (hr : role i = .topRise ∨ role i = .mid ∨ role i = .botDesc)
    (hcpos : 0 < c)
    (hbalance : low + high = G)
    (hconserve : allocation + G =
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)))
    (hpiAlloc : quota i (role i) ≤ allocation)
    (heven : quota i (role i) = 2 * (quota i (role i) / 2))
    (hlow : low ≤ G) (hhigh : high ≤ G)
    (hprofileCap :
      (G = 0 ∧ 256 * quota i (role i) ≤ c) ∨
      (8192 * G + 7 ≤ 15 * c ∧ 4096 * quota i (role i) ≤ 15 * c))
    (hleftReserve : c ≤ 128 * d2FlowTreeRootDeficit (children 0))
    (hrightReserve : c ≤ 128 * d2FlowTreeRootDeficit (children 7)) :
    ∀ j, 8192 * d2FlowTreeRootDeficit
      (d2FlowTreeChild (d2FlowStage active role quota (h + 1) i
        (.node G low high children)) j) + 7 ≤ 30 * c := by
  have hG : 4096 * G ≤ 23 * c := by
    rcases hprofileCap with ⟨hG, _⟩ | ⟨hG, _⟩ <;> nlinarith
  have hpi : 256 * quota i (role i) ≤ c := by
    rcases hprofileCap with ⟨_, hpi⟩ | ⟨_, hpi⟩ <;> nlinarith
  have hshape := d2FlowStage_regular_child_profile_tolerant
    children ha hr hbalance hconserve hpiAlloc heven hG hlow hhigh hpi
    hleftReserve hrightReserve
  rcases hshape with ⟨hfirst, hlast, hmiddle⟩
  intro j
  by_cases hj0 : j = 0
  · subst j
    rw [hfirst]
    have hhalf : 8192 * (quota i (role i) / 2) =
        4096 * quota i (role i) := by omega
    rcases hprofileCap with ⟨hGzero, hquota⟩ | ⟨hGbound, hquota⟩
    · have hlowzero : low = 0 := by omega
      rw [hlowzero]
      nlinarith
    · have hlowbound : 8192 * low ≤ 8192 * G :=
        Nat.mul_le_mul_left 8192 hlow
      nlinarith
  · by_cases hj7 : j.val = 7
    · have hj : j = 7 := Fin.ext hj7
      subst j
      rw [hlast]
      have hhalf : 8192 * (quota i (role i) / 2) =
          4096 * quota i (role i) := by omega
      rcases hprofileCap with ⟨hGzero, hquota⟩ | ⟨hGbound, hquota⟩
      · have hhighzero : high = 0 := by omega
        rw [hhighzero]
        nlinarith
      · have hhighbound : 8192 * high ≤ 8192 * G :=
          Nat.mul_le_mul_left 8192 hhigh
        nlinarith
    · have hjlo : 0 < j.val := by omega
      have hjhi : j.val < 7 := by omega
      rw [hmiddle j hjlo hjhi]
      omega

/-- The candidate's middle and bottom-descending quotas attain, rather than
merely satisfy, the affine profile's exact `15/4096` scaled quota budget. -/
theorem d2FlowCandidateQuota_mid_botDesc_affine_eq
    {d i t : Nat} (hd : 7 ≤ d)
    (ha : active d (tfD2 d) i t) {r : D2Role}
    (hr : r = .mid ∨ r = .botDesc) :
    4096 * d2FlowCandidateQuota d t i r =
      15 * d2FlowCandidateCapacity d i t := by
  rcases hr with hmid | hbot
  · subst r
    have hquota := d2FlowCandidateQuota_eq_portSize hd ha .mid (by decide)
    have hcap := d2FlowCandidateCapacity_eq hd ha
    have hrat : (4096 : Rat) * d2FlowCandidateQuota d t i .mid =
        15 * d2FlowCandidateCapacity d i t := by
      rw [hquota, hcap]
      norm_num [d2PortSize]
      ring
    exact_mod_cast hrat
  · subst r
    have hquota := d2FlowCandidateQuota_eq_portSize hd ha .botDesc (by decide)
    have hcap := d2FlowCandidateCapacity_eq hd ha
    have hrat : (4096 : Rat) * d2FlowCandidateQuota d t i .botDesc =
        15 * d2FlowCandidateCapacity d i t := by
      rw [hquota, hcap]
      norm_num [d2PortSize]
      ring
    exact_mod_cast hrat

/-- Recursive sender-input contract using the sharp affine deficit envelope.
Apart from replacing the loose root/quota caps, it keeps exactly the balance,
allocation, parity and endpoint-reserve fields used by the ordinary stage. -/
def d2FlowStageAffineInputs (active : Nat → Bool)
    (role : Nat → D2Role) (quota : Nat → D2Role → Nat)
    (cap : Nat → Nat) : {h : Nat} → Nat → D2FlowTree h → Prop
  | 0, _, .leaf _ _ _ => True
  | h + 1, i, .node G low high children =>
      (∀ j, d2FlowStageAffineInputs active role quota cap
        (i + 1) (children j)) ∧
      (if active i then
        low + high = G ∧
          match role i with
          | .topDesc => G = 0
          | .botRise => True
          | .topRise =>
              G = 0 ∧ 256 * quota i .topRise ≤ cap i ∧
                quota i .topRise ≤
                  d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G ∧
                quota i .topRise % 2 = 0 ∧
                cap i ≤ 128 * d2FlowTreeRootDeficit (children 0) ∧
                cap i ≤ 128 * d2FlowTreeRootDeficit (children 7)
          | .mid | .botDesc =>
              8192 * G + 7 ≤ 15 * cap i ∧
                4096 * quota i (role i) ≤ 15 * cap i ∧
                quota i (role i) ≤
                  d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G ∧
                quota i (role i) % 2 = 0 ∧
                cap i ≤ 128 * d2FlowTreeRootDeficit (children 0) ∧
                cap i ≤ 128 * d2FlowTreeRootDeficit (children 7)
        else True)

/-- The affine sender-input contract supplies the existing reserve invariant
inputs, so the checked recursive stage-preservation theorem can be reused. -/
theorem d2FlowStageAffineInputs.to_d2FlowStageInvInputs
    {scale : Nat} {active : Nat → Bool} {role : Nat → D2Role}
    {quota : Nat → D2Role → Nat} {cap : Nat → Nat} :
    ∀ {h i : Nat} (tree : D2FlowTree h),
      d2FlowStageAffineInputs active role quota cap i tree →
      d2FlowStageInvInputs scale active role quota cap i tree := by
  intro h
  induction h with
  | zero =>
      intro i tree hinputs
      cases tree <;> simp [d2FlowStageAffineInputs, d2FlowStageInvInputs] at *
  | succ h ih =>
      intro i tree hinputs
      cases tree with
      | node G low high children =>
          simp only [d2FlowStageAffineInputs, d2FlowStageInvInputs] at hinputs ⊢
          rcases hinputs with ⟨hchildren, hlocal⟩
          refine ⟨?_, ?_⟩
          · intro j
            exact ih (i := i + 1) (children j) (hchildren j)
          · by_cases ha : active i = true
            · simp only [ha, if_pos] at hlocal ⊢
              rcases hlocal with ⟨hbalance, hroleInput⟩
              refine ⟨hbalance, ?_⟩
              cases hr : role i with
              | topDesc => simpa [hr] using hroleInput
              | botRise => simp [hr]
              | topRise =>
                  simp only [hr] at hroleInput
                  rcases hroleInput with
                    ⟨hGzero, hquota, halloc, heven, hleft, hright⟩
                  have hG : 512 * G ≤ cap i := by omega
                  exact ⟨hG, hquota, halloc, heven, hleft, hright⟩
              | mid =>
                  simp only [hr] at hroleInput
                  rcases hroleInput with
                    ⟨hG, hquota, halloc, heven, hleft, hright⟩
                  have hG' : 512 * G ≤ cap i := by nlinarith
                  have hquota' : 256 * quota i .mid ≤ cap i := by nlinarith
                  exact ⟨hG', hquota', halloc, heven, hleft, hright⟩
              | botDesc =>
                  simp only [hr] at hroleInput
                  rcases hroleInput with
                    ⟨hG, hquota, halloc, heven, hleft, hright⟩
                  have hG' : 512 * G ≤ cap i := by nlinarith
                  have hquota' : 256 * quota i .botDesc ≤ cap i := by nlinarith
                  exact ⟨hG', hquota', halloc, heven, hleft, hright⟩
            · simp [ha]

theorem d2FlowStage_preserves_inv_of_affine_inputs
    {h i scale : Nat} {active : Nat → Bool} {role : Nat → D2Role}
    {quota : Nat → D2Role → Nat} {cap : Nat → Nat}
    (tree : D2FlowTree h) (hinv : d2FlowTreeInv scale tree)
    (hinputs : d2FlowStageAffineInputs active role quota cap i tree) :
    d2FlowTreeInv scale (d2FlowStage active role quota h i tree) := by
  apply d2FlowStage_preserves_inv_of_inputs tree hinv
  exact d2FlowStageAffineInputs.to_d2FlowStageInvInputs tree hinputs

attribute [local irreducible] d2FlowStageAffineInputs d2FlowTreeInv
  d2FlowCandidateRun

/-- All-stage affine sender inputs are sufficient for the actual candidate
run to preserve the recursive reserve invariant for an arbitrary horizon. -/
theorem d2FlowCandidateRun_preserves_inv_of_affine_all_inputs
    (d n : Nat) (initial : D2FlowTree d)
    (hinitial : d2FlowTreeInv 8192 initial)
    (hinputs : ∀ t, t < n →
      d2FlowStageAffineInputs
        (d2FlowCandidateActive d t)
        (d2FlowCandidateRole d t)
        (d2FlowCandidateQuota d t)
        (fun i => d2FlowCandidateCapacity d i t) 0
        (d2FlowCandidateRun d initial t)) :
    d2FlowTreeInv 8192 (d2FlowCandidateRun d initial n) := by
  induction n with
  | zero => simpa [d2FlowCandidateRun] using hinitial
  | succ n ih =>
      have hprev : d2FlowTreeInv 8192 (d2FlowCandidateRun d initial n) := by
        apply ih
        intro t ht
        exact hinputs t (by omega)
      have hpres := d2FlowStage_preserves_inv_of_affine_inputs
        (d2FlowCandidateRun d initial n) hprev (hinputs n (by omega))
      simpa [d2FlowCandidateRun, d2FlowCandidateStage] using hpres

end Chvatal.D2Reserve
