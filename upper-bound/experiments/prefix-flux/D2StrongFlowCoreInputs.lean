import D2StrongFlowNoAlloc

namespace Chvatal.D2Reserve

set_option linter.unusedVariables false
set_option maxHeartbeats 12000000
set_option maxRecDepth 4096

/-- The actual tree-state portion of the affine sender contract. Candidate
quota size and parity are schedule formulas, so this contract retains only
balance, the affine deficit profile, and the endpoint reserves. -/
def d2FlowStageAffineCoreInputs (active : Nat -> Bool)
    (role : Nat -> D2Role) (cap : Nat -> Nat) : {h : Nat} -> Nat -> D2FlowTree h -> Prop
  | 0, _, .leaf _ _ _ => True
  | h + 1, i, .node G low high children =>
      (forall j, d2FlowStageAffineCoreInputs active role cap
        (i + 1) (children j)) /\
      (if active i then
        low + high = G /\
          match role i with
          | .topDesc => G = 0
          | .botRise => True
          | .topRise =>
              G = 0 /\
                cap i <= 128 * d2FlowTreeRootDeficit (children 0) /\
                cap i <= 128 * d2FlowTreeRootDeficit (children 7)
          | .mid | .botDesc =>
              8192 * G + 7 <= 15 * cap i /\
                cap i <= 128 * d2FlowTreeRootDeficit (children 0) /\
                cap i <= 128 * d2FlowTreeRootDeficit (children 7)
       else True)

/-- Project the recursive core contract to any selected subtree. This makes
the all-level provider usable at the path-local ordinary update interface. -/
theorem d2FlowStageAffineCoreInputs_atPath
    {active : Nat -> Bool} {role : Nat -> D2Role} {cap : Nat -> Nat}
    {h n i : Nat} (tree : D2FlowTree (h + n))
    (path : D2FlowPath n)
    (hcore : d2FlowStageAffineCoreInputs active role cap i tree) :
    d2FlowStageAffineCoreInputs active role cap (i + n)
      (d2FlowTreeAtPath n tree path) := by
  induction path generalizing h i with
  | nil => simpa [d2FlowTreeAtPath] using hcore
  | @cons n j tail ih =>
      cases tree with
      | node G low high children =>
          simp only [d2FlowStageAffineCoreInputs] at hcore ⊢
          rcases hcore with ⟨hchildren, _⟩
          change d2FlowStageAffineCoreInputs active role cap (i + (n + 1))
            (d2FlowTreeAtPath n (children j) tail)
          have hselected := ih (h := h) (i := i + 1)
            (tree := children j) (hchildren j)
          simpa only [show i + 1 + n = i + (n + 1) by omega] using hselected

/-- If the quota callback has the candidate's schedule sizes and parity, the
tree-state core contract implies the allocation-free affine input contract. -/
theorem d2FlowStageAffineCoreInputs_to_noAlloc
    {active : Nat -> Bool} {role : Nat -> D2Role}
    {quota : Nat -> D2Role -> Nat} {cap : Nat -> Nat} {h i : Nat}
    (tree : D2FlowTree h)
    (hcore : d2FlowStageAffineCoreInputs active role cap i tree)
    (htop : forall j, active j = true -> role j = .topRise ->
      256 * quota j .topRise <= cap j /\ quota j .topRise % 2 = 0)
    (hmidBot : forall j, active j = true ->
      (role j = .mid \/ role j = .botDesc) ->
      4096 * quota j (role j) <= 15 * cap j /\
        quota j (role j) % 2 = 0) :
    d2FlowStageAffineInputsNoAlloc active role quota cap i tree := by
  induction tree generalizing i with
  | leaf G low high => trivial
  | @node h G low high children ih =>
      simp only [d2FlowStageAffineCoreInputs,
        d2FlowStageAffineInputsNoAlloc] at hcore ⊢
      rcases hcore with ⟨hchildren, hlocal⟩
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
              rcases hroleData with ⟨hGzero, hleft, hright⟩
              rcases htop i ha hr with ⟨hquota, heven⟩
              exact ⟨hGzero, hquota, heven, hleft, hright⟩
          | mid =>
              simp only [hr] at hroleData
              rcases hroleData with ⟨hprofile, hleft, hright⟩
              have hq := hmidBot i ha (Or.inl hr)
              have hquota : 4096 * quota i .mid <= 15 * cap i := by
                simpa [hr] using hq.1
              have heven : quota i .mid % 2 = 0 := by simpa [hr] using hq.2
              exact ⟨hprofile, hquota, heven, hleft, hright⟩
          | botDesc =>
              simp only [hr] at hroleData
              rcases hroleData with ⟨hprofile, hleft, hright⟩
              have hq := hmidBot i ha (Or.inr hr)
              have hquota : 4096 * quota i .botDesc <= 15 * cap i := by
                simpa [hr] using hq.1
              have heven : quota i .botDesc % 2 = 0 := by simpa [hr] using hq.2
              exact ⟨hprofile, hquota, heven, hleft, hright⟩
        · simp only [ha] at hlocal ⊢
          exact True.intro

/-- The closed-form candidate quota supplies the schedule-only fields needed
by the core-to-affine adapter at every positive stage. -/
theorem d2FlowCandidateStageAffineCoreInputs_to_noAlloc
    {d t : Nat} (hd : 7 <= d) (ht : 0 < t)
    (tree : D2FlowTree d)
    (hcore : d2FlowStageAffineCoreInputs
      (fun i => d2FlowCandidateActive d t i)
      (fun i => d2FlowCandidateRole d t i)
      (fun i => d2FlowCandidateCapacity d i t) 0 tree) :
    d2FlowStageAffineInputsNoAlloc
      (d2FlowCandidateActive d t) (d2FlowCandidateRole d t)
      (d2FlowCandidateQuota d t) (fun i => d2FlowCandidateCapacity d i t)
      0 tree := by
  classical
  apply d2FlowStageAffineCoreInputs_to_noAlloc tree hcore
  · intro i hi hrole
    have hactiveBool := d2FlowCandidateActive_matches_schedule
      (d := d) (t := t) (i := i) ht
    have hactiveDec : decide (active d (tfD2 d) i t) = true := by
      rw [← hactiveBool]
      exact hi
    have hactive : active d (tfD2 d) i t := of_decide_eq_true hactiveDec
    have hroleSchedule : d2ScheduleRole d i t = .topRise := by
      rw [← d2FlowCandidateRole_matches_schedule (d := d) (t := t) (i := i) ht]
      exact hrole
    have hregular : d2ScheduleRole d i t = .topRise ∨
        d2ScheduleRole d i t = .mid ∨ d2ScheduleRole d i t = .botDesc :=
      Or.inl hroleSchedule
    have hcap := d2FlowCandidateQuota_le_capacity_div_256 hd hactive hregular
    have heven := d2FlowCandidateQuota_even hd hactive ht hregular
    rw [hroleSchedule] at hcap
    rw [hrole] at heven
    exact ⟨hcap, heven⟩
  · intro i hi hrole
    have hactiveBool := d2FlowCandidateActive_matches_schedule
      (d := d) (t := t) (i := i) ht
    have hactiveDec : decide (active d (tfD2 d) i t) = true := by
      rw [← hactiveBool]
      exact hi
    have hactive : active d (tfD2 d) i t := of_decide_eq_true hactiveDec
    have hroleCandidate := d2FlowCandidateRole_matches_schedule
      (d := d) (t := t) (i := i) ht
    have hroleSchedule : d2ScheduleRole d i t = .mid \/
        d2ScheduleRole d i t = .botDesc := by
      rw [← hroleCandidate]
      exact hrole
    have heven := d2FlowCandidateQuota_even hd hactive ht
      (hroleSchedule.elim (fun hm => Or.inr (Or.inl hm))
        (fun hb => Or.inr (Or.inr hb)))
    have hquota := d2FlowCandidateQuota_mid_botDesc_affine_eq hd hactive
      hroleSchedule
    rw [← hroleCandidate] at hquota
    exact ⟨le_of_eq hquota, heven⟩

/-- Restrict a positive-stage full-tree core provider to any actual path. -/
theorem d2FlowCandidateRun_core_provider_noAlloc_atPath
    {h i t : Nat} (hd : 7 ≤ h + i) (ht : 0 < t)
    (path : D2FlowPath i)
    (hcore : d2FlowStageAffineCoreInputs
      (fun k => d2FlowCandidateActive (h + i) t k)
      (fun k => d2FlowCandidateRole (h + i) t k)
      (fun k => d2FlowCandidateCapacity (h + i) k t) 0
      (d2FlowCandidateRun (h + i)
        (d2FlowTreeInitial 8192 (h + i)) t)) :
    d2FlowStageAffineInputsNoAlloc
      (d2FlowCandidateActive (h + i) t)
      (d2FlowCandidateRole (h + i) t)
      (d2FlowCandidateQuota (h + i) t)
      (fun k => d2FlowCandidateCapacity (h + i) k t) i
      (d2FlowTreeAtPath i
        (d2FlowCandidateRun (h + i)
          (d2FlowTreeInitial 8192 (h + i)) t) path) := by
  let d := h + i
  have hnoalloc := d2FlowCandidateStageAffineCoreInputs_to_noAlloc
    (d := d) hd ht (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) t) hcore
  simpa [d] using d2FlowStageAffineInputsNoAlloc_atPath
    (active := d2FlowCandidateActive d t)
    (role := d2FlowCandidateRole d t)
    (quota := d2FlowCandidateQuota d t)
    (cap := fun k => d2FlowCandidateCapacity d k t)
    (h := h) (n := i) (i := 0)
    (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) t) path hnoalloc

/-- The path-restricted core provider also gives the full affine contract,
including the allocation bound recovered from the left endpoint reserve. -/
theorem d2FlowCandidateRun_core_provider_affine_atPath
    {h i t : Nat} (hd : 7 <= h + i) (ht : 0 < t)
    (path : D2FlowPath i)
    (hcore : d2FlowStageAffineCoreInputs
      (fun k => d2FlowCandidateActive (h + i) t k)
      (fun k => d2FlowCandidateRole (h + i) t k)
      (fun k => d2FlowCandidateCapacity (h + i) k t) 0
      (d2FlowCandidateRun (h + i)
        (d2FlowTreeInitial 8192 (h + i)) t)) :
    d2FlowStageAffineInputs
      (d2FlowCandidateActive (h + i) t)
      (d2FlowCandidateRole (h + i) t)
      (d2FlowCandidateQuota (h + i) t)
      (fun k => d2FlowCandidateCapacity (h + i) k t) i
      (d2FlowTreeAtPath i
        (d2FlowCandidateRun (h + i)
          (d2FlowTreeInitial 8192 (h + i)) t) path) := by
  exact d2FlowStageAffineInputs_of_noAlloc _
    (d2FlowCandidateRun_core_provider_noAlloc_atPath hd ht path hcore)

/-- Extract the numeric gates needed by the ordinary two-visit reserve lemma
from one active affine sender contract. -/
theorem d2FlowStageAffineInputs_ordinary_fields
    {active : Nat -> Bool} {role : Nat -> D2Role}
    {quota : Nat -> D2Role -> Nat} {cap : Nat -> Nat}
    {h i G low high : Nat} (children : Fin 8 -> D2FlowTree h)
    (hinputs : d2FlowStageAffineInputs active role quota cap i
      (.node G low high children))
    (ha : active i = true)
    (hr : role i = .topRise \/ role i = .mid \/ role i = .botDesc) :
    low + high = G /\
      quota i (role i) <= d2FlowTotal (fun j =>
        d2FlowTreeRootDeficit (children j)) - G /\
      quota i (role i) % 2 = 0 /\
      512 * G <= cap i /\ 256 * quota i (role i) <= cap i /\
      cap i <= 128 * d2FlowTreeRootDeficit (children 0) /\
      cap i <= 128 * d2FlowTreeRootDeficit (children 7) /\
      ((G = 0 /\ 256 * quota i (role i) <= cap i) \/
        (8192 * G + 7 <= 15 * cap i /\
          4096 * quota i (role i) <= 15 * cap i)) := by
  simp only [d2FlowStageAffineInputs] at hinputs
  rcases hinputs with ⟨_, hlocal⟩
  simp only [ha, if_pos] at hlocal
  rcases hlocal with ⟨hbalance, hroleData⟩
  rcases hr with htop | hmid | hbot
  · simp only [htop] at hroleData
    rcases hroleData with ⟨hzero, hqcap, halloc, heven, hleft, hright⟩
    have hdeficit : 512 * G <= cap i := by omega
    exact ⟨hbalance, by simpa [htop] using halloc,
      by simpa [htop] using heven,
      hdeficit, by simpa [htop] using hqcap, hleft, hright,
      Or.inl ⟨hzero, by simpa [htop] using hqcap⟩⟩
  · simp only [hmid] at hroleData
    rcases hroleData with ⟨hprofile, hqprofile, halloc, heven, hleft, hright⟩
    have hcaps := d2_affine_profile_implies_existing_local_caps
      (G := G) (pi := quota i .mid) (c := cap i)
      (Or.inr ⟨hprofile, by simpa [hmid] using hqprofile⟩)
    exact ⟨hbalance, by simpa [hmid] using halloc,
      by simpa [hmid] using heven,
      hcaps.1, by simpa [hmid] using hcaps.2, hleft, hright,
      Or.inr ⟨hprofile, by simpa [hmid] using hqprofile⟩⟩
  · simp only [hbot] at hroleData
    rcases hroleData with ⟨hprofile, hqprofile, halloc, heven, hleft, hright⟩
    have hcaps := d2_affine_profile_implies_existing_local_caps
      (G := G) (pi := quota i .botDesc) (c := cap i)
      (Or.inr ⟨hprofile, by simpa [hbot] using hqprofile⟩)
    exact ⟨hbalance, by simpa [hbot] using halloc,
      by simpa [hbot] using heven,
      hcaps.1, by simpa [hbot] using hcaps.2, hleft, hright,
      Or.inr ⟨hprofile, by simpa [hbot] using hqprofile⟩⟩

private theorem d2FlowStageAffineInputsNoAlloc_of_inactive_tail
    {active : Nat -> Bool} {role : Nat -> D2Role}
    {quota : Nat -> D2Role -> Nat} {cap : Nat -> Nat} {h i : Nat}
    (tree : D2FlowTree h)
    (hinactive : forall j, i <= j -> active j = false) :
    d2FlowStageAffineInputsNoAlloc active role quota cap i tree := by
  induction h generalizing i with
  | zero =>
      cases tree
      trivial
  | succ h ih =>
      cases tree with
      | node G low high children =>
          simp only [d2FlowStageAffineInputsNoAlloc]
          constructor
          case left =>
            intro j
            exact ih (i := i + 1) (children j) (by
              intro k hk
              exact hinactive k (by omega))
          case right =>
            simp [hinactive i (by omega)]

/-- Stage zero is the explicit top-descending root reset, with all proper
descendants inactive. -/
theorem d2FlowCandidateRun_stage0_affine_noAlloc (d : Nat) :
    d2FlowStageAffineInputsNoAlloc
      (d2FlowCandidateActive d 0) (d2FlowCandidateRole d 0)
      (d2FlowCandidateQuota d 0) (fun i => d2FlowCandidateCapacity d i 0)
      0 (d2FlowTreeInitial 8192 d) := by
  cases d with
  | zero => simp [d2FlowStageAffineInputsNoAlloc, d2FlowTreeInitial]
  | succ d =>
      have hchildren : forall j : Fin 8,
          d2FlowStageAffineInputsNoAlloc
            (d2FlowCandidateActive (d + 1) 0)
            (d2FlowCandidateRole (d + 1) 0)
            (d2FlowCandidateQuota (d + 1) 0)
            (fun i => d2FlowCandidateCapacity (d + 1) i 0) 1
            (d2FlowTreeFull 8192 d) := by
        intro j
        apply d2FlowStageAffineInputsNoAlloc_of_inactive_tail
        intro k hk
        exact d2FlowCandidateActive_nonroot_at_zero (by omega)
      simp only [d2FlowStageAffineInputsNoAlloc, d2FlowTreeInitial,
        d2FlowCandidateActive_root_at_zero, if_pos, d2FlowCandidateRole]
      exact ⟨hchildren, True.intro, True.intro⟩

/-- Thus a schedule-parametric proof of the actual tree core would immediately
provide every allocation-free affine sender input at all positive stages. -/
theorem d2FlowCandidateRun_core_provider_to_affine_noAlloc_all_inputs
    {d n : Nat} (hd : 7 <= d)
    (hcore : forall t, 0 < t -> t < n ->
      d2FlowStageAffineCoreInputs
        (fun i => d2FlowCandidateActive d t i)
        (fun i => d2FlowCandidateRole d t i)
        (fun i => d2FlowCandidateCapacity d i t) 0
        (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) t)) :
    forall t, t < n ->
      d2FlowStageAffineInputsNoAlloc
        (d2FlowCandidateActive d t) (d2FlowCandidateRole d t)
        (d2FlowCandidateQuota d t)
        (fun i => d2FlowCandidateCapacity d i t) 0
        (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) t) := by
  intro t htn
  by_cases ht : t = 0
  · subst t
    exact d2FlowCandidateRun_stage0_affine_noAlloc d
  · have htpos : 0 < t := by omega
    exact d2FlowCandidateStageAffineCoreInputs_to_noAlloc hd htpos _
      (hcore t htpos htn)

/-- A positive-stage tree-core provider would imply the reserve invariant at
every candidate-run horizon; the bootstrap stage is discharged separately. -/
theorem d2FlowCandidateRun_preserves_inv_of_core_provider
    {d n : Nat} (hd : 7 <= d)
    (hcore : forall t, 0 < t -> t < n ->
      d2FlowStageAffineCoreInputs
        (fun i => d2FlowCandidateActive d t i)
        (fun i => d2FlowCandidateRole d t i)
        (fun i => d2FlowCandidateCapacity d i t) 0
        (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) t)) :
    d2FlowTreeInv 8192
      (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) n) := by
  apply d2FlowCandidateRun_preserves_inv_of_affine_noAlloc_all_inputs
    d n (d2FlowTreeInitial 8192 d) (d2FlowTreeInitial_inv 8192 d)
  exact d2FlowCandidateRun_core_provider_to_affine_noAlloc_all_inputs
    hd hcore

end Chvatal.D2Reserve
