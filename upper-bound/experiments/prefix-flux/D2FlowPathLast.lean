import D2TopDescHistory
import D2RootFrontierCase

namespace Chvatal.D2Reserve

set_option linter.unusedVariables false

/-- A current affine core provider supplies the one-stage invariant inputs, so
the existing invariant preservation theorem yields the next run snapshot. -/
theorem d2FlowCandidateRun_preserves_inv_next_of_affine_core
    {d t : Nat} (hd : 7 <= d) (ht : 0 < t)
    (hinv : d2FlowTreeInv 8192
      (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) t))
    (hcore : d2FlowStageAffineCoreInputs
      (fun k => d2FlowCandidateActive d t k)
      (fun k => d2FlowCandidateRole d t k)
      (fun k => d2FlowCandidateCapacity d k t) 0
      (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) t)) :
    d2FlowTreeInv 8192
      (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) (t + 1)) := by
  let tree := d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) t
  have hnoAlloc := d2FlowCandidateStageAffineCoreInputs_to_noAlloc
    (d := d) hd ht tree (by simpa [tree] using hcore)
  have hinputs := d2FlowStageAffineInputs_of_noAlloc tree hnoAlloc
  have hpres := d2FlowStage_preserves_inv_of_affine_inputs tree
    (by simpa [tree] using hinv) hinputs
  change d2FlowTreeInv 8192
    (d2FlowCandidateStage d t (d2FlowCandidateRun d
      (d2FlowTreeInitial 8192 d) t))
  simpa only [d2FlowCandidateRun] using hpres

/-- Append a final port to a root-first path. -/
def d2FlowPathSnoc : {n : Nat} → D2FlowPath n → Fin 8 → D2FlowPath (n + 1)
  | 0, .nil, j => .cons j .nil
  | n + 1, .cons j tail, k => .cons j (d2FlowPathSnoc tail k)

theorem d2FlowTreeChild_cast {a b : Nat} (e : a + 1 = b + 1)
    (f : a = b) (tree : D2FlowTree (a + 1)) (port : Fin 8) :
    cast (congrArg D2FlowTree f) (d2FlowTreeChild tree port) =
      d2FlowTreeChild (cast (congrArg D2FlowTree e) tree) port := by
  have hab : a = b := by omega
  subst b
  cases e
  rfl

/-- Appending a final port to a path agrees with taking a child after the
path projection. The cast only reconciles the two associated height sums. -/
theorem d2FlowTreeAtPath_snoc {h n : Nat}
    (tree : D2FlowTree (h + (n + 1))) (path : D2FlowPath n) (port : Fin 8) :
    d2FlowTreeAtPath (n + 1) tree (d2FlowPathSnoc path port) =
      d2FlowTreeChild
        (d2FlowTreeAtPath n
          (cast (congrArg D2FlowTree (show h + (n + 1) = (h + 1) + n by omega)) tree)
          path) port := by
  induction path generalizing h with
  | nil => rfl
  | @cons n first tail ih =>
      cases tree with
      | node G low high children =>
          simp only [d2FlowTreeAtPath, d2FlowPathSnoc]
          have hcast := d2FlowTreeChild_cast
            (e := show (h + (n + 1)) + 1 = ((h + 1) + n) + 1 by omega)
            (f := show h + (n + 1) = (h + 1) + n by omega)
            (.node G low high children) first
          rw [← hcast]
          exact ih (h := h)
            (tree := d2FlowTreeChild (.node G low high children) first)

theorem d2FlowCandidateRun_initial_cast {d₁ d₂ : Nat} (hd : d₁ = d₂)
    (stage : Nat) :
    cast (congrArg D2FlowTree hd)
      (d2FlowCandidateRun d₁ (d2FlowTreeInitial 8192 d₁) stage) =
        d2FlowCandidateRun d₂ (d2FlowTreeInitial 8192 d₂) stage := by
  cases hd
  rfl

theorem d2FlowCandidateRun_affine_core_transport {d₁ d₂ t : Nat}
    (hd : d₁ = d₂)
    (hcore : d2FlowStageAffineCoreInputs
      (fun k => d2FlowCandidateActive d₁ t k)
      (fun k => d2FlowCandidateRole d₁ t k)
      (fun k => d2FlowCandidateCapacity d₁ k t) 0
      (d2FlowCandidateRun d₁ (d2FlowTreeInitial 8192 d₁) t)) :
    d2FlowStageAffineCoreInputs
      (fun k => d2FlowCandidateActive d₂ t k)
      (fun k => d2FlowCandidateRole d₂ t k)
      (fun k => d2FlowCandidateCapacity d₂ k t) 0
      (d2FlowCandidateRun d₂ (d2FlowTreeInitial 8192 d₂) t) := by
  cases hd
  exact hcore

/-- Every positive-length root-first path has a unique last-edge
decomposition. -/
theorem d2FlowPath_exists_snoc {n : Nat} (path : D2FlowPath (n + 1)) :
    ∃ parent : D2FlowPath n, ∃ port : Fin 8,
      d2FlowPathSnoc parent port = path := by
  induction n with
  | zero =>
      cases path with
      | cons port tail =>
          cases tail with
          | nil => exact ⟨.nil, port, rfl⟩
  | succ n ih =>
      cases path with
      | cons first tail =>
          cases htail : tail with
          | cons second rest =>
              obtain ⟨parent, port, hparent⟩ := ih (.cons second rest)
              exact ⟨.cons first parent, port, by
                simp [d2FlowPathSnoc, hparent]⟩

theorem d2FlowCandidateRun_active_child_endpoint_reserves
    {h i t : Nat} (hd : 7 <= h + 2 + i) (ht : 3 <= t)
    (path : D2FlowPath i) (port : Fin 8)
    (hchildActive : active (h + 2 + i) (tfD2 (h + 2 + i)) (i + 1) (t + 1))
    (hregular : d2ScheduleRole (h + 2 + i) (i + 1) (t + 1) = .topRise \/
      d2ScheduleRole (h + 2 + i) (i + 1) (t + 1) = .mid \/
      d2ScheduleRole (h + 2 + i) (i + 1) (t + 1) = .botDesc)
    (hcorePrev : d2FlowStageAffineCoreInputs
      (fun k => d2FlowCandidateActive (h + 2 + i) (t - 1) k)
      (fun k => d2FlowCandidateRole (h + 2 + i) (t - 1) k)
      (fun k => d2FlowCandidateCapacity (h + 2 + i) k (t - 1)) 0
      (d2FlowCandidateRun (h + 2 + i)
        (d2FlowTreeInitial 8192 (h + 2 + i)) (t - 1))) :
    d2FlowCandidateCapacity (h + 2 + i) (i + 1) (t + 1) <=
      128 * d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeAtPath i
              (d2FlowCandidateRun (h + 2 + i)
                (d2FlowTreeInitial 8192 (h + 2 + i)) (t + 1)) path) port) 0) /\
    d2FlowCandidateCapacity (h + 2 + i) (i + 1) (t + 1) <=
      128 * d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeAtPath i
              (d2FlowCandidateRun (h + 2 + i)
                (d2FlowTreeInitial 8192 (h + 2 + i)) (t + 1)) path) port) 7) := by
  let d := h + 2 + i
  have hdepth : d = h + 1 + (i + 1) := by omega
  have htf : t + 1 <= tfD2 d := by
    have ha := (active_iff_frontiers (d := d) (tf := tfD2 d)
      (i := i + 1) (t := t + 1) (by omega)).1 hchildActive
    exact ha.1
  have hactive' : active (h + 1 + (i + 1))
      (tfD2 (h + 1 + (i + 1))) (i + 1) (t + 1) := by
    rw [← hdepth]
    exact hchildActive
  have hregular' : d2ScheduleRole (h + 1 + (i + 1)) (i + 1) (t + 1) = .topRise \/
      d2ScheduleRole (h + 1 + (i + 1)) (i + 1) (t + 1) = .mid \/
      d2ScheduleRole (h + 1 + (i + 1)) (i + 1) (t + 1) = .botDesc := by
    rw [← hdepth]
    exact hregular
  have hcorePrev' := d2FlowCandidateRun_affine_core_transport hdepth hcorePrev
  have hres := d2FlowCandidateRun_core_provider_endpoint_reserves_at_active_path
    (h := h) (i := i + 1) (t := t + 1) (by omega) (by omega)
    (by rw [← hdepth]; exact htf) (d2FlowPathSnoc path port)
    hactive' hregular' hcorePrev'
  have hheight : (h + 1) + (i + 1) = ((h + 1) + 1) + i := by omega
  have hassoc : (h + 1) + 1 + i = h + 2 + i := by omega
  have hrun := d2FlowCandidateRun_initial_cast hheight (t + 1)
  have hproject := d2FlowTreeAtPath_snoc (h := h + 1) (n := i)
    (tree := d2FlowCandidateRun (h + 1 + (i + 1))
      (d2FlowTreeInitial 8192 (h + 1 + (i + 1))) (t + 1)) path port
  rw [hproject, hrun] at hres
  simpa [d2FlowTreeAtPath, d, hdepth, hassoc] using hres

/-- The child root fields required by the affine core now share one actual
tree node: balance and role profile use the child adapters, and the endpoint
reserves use the cast-aware path projection above. -/
theorem d2FlowCandidateRun_active_child_affine_local_contract
    {h i t : Nat} (hd : 7 <= h + 2 + i) (ht : 3 <= t)
    (path : D2FlowPath i) (port : Fin 8)
    (hchildActive : active (h + 2 + i) (tfD2 (h + 2 + i)) (i + 1) (t + 1))
    (hcorePrev : d2FlowStageAffineCoreInputs
      (fun k => d2FlowCandidateActive (h + 2 + i) (t - 1) k)
      (fun k => d2FlowCandidateRole (h + 2 + i) (t - 1) k)
      (fun k => d2FlowCandidateCapacity (h + 2 + i) k (t - 1)) 0
      (d2FlowCandidateRun (h + 2 + i)
        (d2FlowTreeInitial 8192 (h + 2 + i)) (t - 1)))
    (hcoreNow : d2FlowStageAffineCoreInputs
      (fun k => d2FlowCandidateActive (h + 2 + i) t k)
      (fun k => d2FlowCandidateRole (h + 2 + i) t k)
      (fun k => d2FlowCandidateCapacity (h + 2 + i) k t) 0
      (d2FlowCandidateRun (h + 2 + i)
        (d2FlowTreeInitial 8192 (h + 2 + i)) t))
    (hinvNow : d2FlowTreeInv 8192
      (d2FlowCandidateRun (h + 2 + i)
        (d2FlowTreeInitial 8192 (h + 2 + i)) t)) :
    let child := d2FlowTreeChild
      (d2FlowTreeAtPath i
        (d2FlowCandidateRun (h + 2 + i)
          (d2FlowTreeInitial 8192 (h + 2 + i)) (t + 1)) path) port
    (d2FlowTreeRootData child).2.1 + (d2FlowTreeRootData child).2.2 =
      d2FlowTreeRootDeficit child /\
    (let root := d2FlowTreeRootDeficit child
      match d2ScheduleRole (h + 2 + i) (i + 1) (t + 1) with
      | .topDesc => root = 0
      | .botRise => True
      | .topRise => root = 0 /\
          8192 * root + 7 <= 15 * d2FlowCandidateCapacity
            (h + 2 + i) (i + 1) (t + 1)
      | .mid | .botDesc =>
          8192 * root + 7 <= 15 * d2FlowCandidateCapacity
            (h + 2 + i) (i + 1) (t + 1)) /\
    ((d2ScheduleRole (h + 2 + i) (i + 1) (t + 1) = .topRise \/
      d2ScheduleRole (h + 2 + i) (i + 1) (t + 1) = .mid \/
      d2ScheduleRole (h + 2 + i) (i + 1) (t + 1) = .botDesc) ->
      d2FlowCandidateCapacity (h + 2 + i) (i + 1) (t + 1) <=
        128 * d2FlowTreeRootDeficit (d2FlowTreeChild child 0) /\
      d2FlowCandidateCapacity (h + 2 + i) (i + 1) (t + 1) <=
        128 * d2FlowTreeRootDeficit (d2FlowTreeChild child 7)) := by
  classical
  let d := h + 2 + i
  let child := d2FlowTreeChild
    (d2FlowTreeAtPath i
      (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) (t + 1)) path) port
  have hinvNext := d2FlowCandidateRun_preserves_inv_next_of_affine_core
    (d := d) (t := t) (by simpa [d] using hd) (by omega)
    (by simpa [d] using hinvNow) (by simpa [d] using hcoreNow)
  have hbalance := d2FlowCandidateRun_active_child_balanced_of_prior_core
    (h := h) (i := i) (t := t) hd ht path port hchildActive
    (by simpa [d] using hcorePrev) (by simpa [d] using hinvNext)
  have hprofile := d2FlowCandidateRun_active_child_role_root_contract
    (h := h) (i := i) (t := t) hd ht path port hchildActive
    (by simpa [d] using hcorePrev) (by simpa [d] using hcoreNow)
  refine ⟨?_, ?_, ?_⟩
  · simpa [child, d] using hbalance
  · simpa [child, d] using hprofile
  · intro hregular
    simpa [child, d] using
      d2FlowCandidateRun_active_child_endpoint_reserves
        hd ht path port hchildActive hregular hcorePrev

/-- At the root, the invariant supplies balance and the moving-root history
supplies exact zero. This is the root-local case complementary to the
active-child contract. -/
theorem d2FlowCandidateRun_active_root_affine_local_contract
    {d t : Nat} (hd : 7 <= d) (ht : 4 <= t)
    (hrootActive : active d (tfD2 d) 0 t)
    (hcorePrev : d2FlowStageAffineCoreInputs
      (fun k => d2FlowCandidateActive d (t - 2) k)
      (fun k => d2FlowCandidateRole d (t - 2) k)
      (fun k => d2FlowCandidateCapacity d k (t - 2)) 0
      (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) (t - 2)))
    (hinvNow : d2FlowTreeInv 8192
      (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) t)) :
    (d2FlowTreeRootData (d2FlowCandidateRun d
      (d2FlowTreeInitial 8192 d) t)).2.1 +
    (d2FlowTreeRootData (d2FlowCandidateRun d
      (d2FlowTreeInitial 8192 d) t)).2.2 =
      d2FlowTreeRootDeficit (d2FlowCandidateRun d
        (d2FlowTreeInitial 8192 d) t) /\
    d2FlowTreeRootDeficit (d2FlowCandidateRun d
      (d2FlowTreeInitial 8192 d) t) = 0 /\
    d2ScheduleRole d 0 t = .topDesc := by
  cases d with
  | zero => omega
  | succ d =>
    have hzero := d2FlowCandidate_active_root_zero_of_prior_core
      (d := d + 1) hd ht hrootActive hcorePrev
    have hrole := d2FlowCandidate_root_active_is_topDesc
      (d := d + 1) (by omega) (by omega) hrootActive
    cases htree : d2FlowCandidateRun (d + 1)
        (d2FlowTreeInitial 8192 (d + 1)) t with
    | node G low high children =>
      have hinv := hinvNow
      simp [htree, d2FlowTreeInv] at hinv
      rcases hinv with ⟨_, _, hbalance, _⟩
      have hGzero : G = 0 := by
        simpa [htree, d2FlowTreeRootDeficit] using hzero
      have hcapacity : G < 8192 * 8 ^ (d + 1) := by
        rw [hGzero]
        positivity
      refine ⟨?_, ?_, hrole⟩
      · simpa [htree, d2FlowTreeRootData, d2FlowTreeRootDeficit] using
          hbalance hcapacity
      · simpa [htree, d2FlowTreeRootDeficit] using hGzero

end Chvatal.D2Reserve
