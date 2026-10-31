import D2Stage17LevelTwoInputs
import D2Stage17LevelOneRootZero
import D2Stage16RootInputs
import D2Stage14Contract

namespace Chvatal.D2Reserve

attribute [local irreducible] d2FlowStageInvInputs
attribute [local irreducible] d2FlowTreeInv
attribute [local irreducible] d2FlowCandidateRun

set_option maxHeartbeats 12000000
set_option maxRecDepth 4096

private theorem d2FlowTreeInv_child_stage17
    {h scale : Nat} (tree : D2FlowTree (h + 1))
    (hinv : d2FlowTreeInv scale tree) (j : Fin 8) :
    d2FlowTreeInv scale (d2FlowTreeChild tree j) := by
  cases tree with
  | node G low high children =>
      have hx := hinv
      simp only [d2FlowTreeInv] at hx
      simpa using hx.2.2.2 j

/-- Exact scale relation between the Stage-16 level-two middle reserve and
the Stage-17 level-one top-rise quota. -/
theorem d2FlowCandidateStage17_levelOne_quota_arithmetic
    {d : Nat} (hd : 16 <= d) :
    256 * d2FlowCandidateQuota d 17 1 .topRise =
        d2FlowCandidateCapacity d 1 17 /\
    128 * d2FlowCandidateQuota d 16 2 .mid =
        15 * d2FlowCandidateCapacity d 1 17 /\
    d2FlowCandidateQuota d 17 1 .topRise <=
        8 * d2FlowCandidateQuota d 16 2 .mid /\
    d2FlowCandidateCapacity d 1 17 <=
        128 * d2FlowCandidateQuota d 16 2 .mid /\
    d2FlowCandidateQuota d 17 1 .topRise % 2 = 0 := by
  have he17 : d2FlowCandidateCapacityExponent d 1 17 = 3 * d - 22 := by
    simp [d2FlowCandidateCapacityExponent]
    omega
  have he16 : d2FlowCandidateCapacityExponent d 2 16 = 3 * d - 17 := by
    simp [d2FlowCandidateCapacityExponent]
    omega
  have hq17 : d2FlowCandidateQuota d 17 1 .topRise = 2 ^ (3 * d - 30) := by
    change 2 ^ (d2FlowCandidateCapacityExponent d 1 17 - 8) = _
    rw [he17]
    congr 1 <;> omega
  have hq16 : d2FlowCandidateQuota d 16 2 .mid = 15 * 2 ^ (3 * d - 29) := by
    change 15 * 2 ^ (d2FlowCandidateCapacityExponent d 2 16 - 12) = _
    rw [he16]
    congr 1 <;> omega
  have hcap : d2FlowCandidateCapacity d 1 17 = 2 ^ (3 * d - 22) := by
    change 2 ^ d2FlowCandidateCapacityExponent d 1 17 = _
    rw [he17]
  have hp17 : 256 * d2FlowCandidateQuota d 17 1 .topRise =
      d2FlowCandidateCapacity d 1 17 := by
    rw [hq17, hcap]
    have hexp : 8 + (3 * d - 30) = 3 * d - 22 := by omega
    rw [show 256 = 2 ^ 8 by norm_num, ← pow_add, hexp]
  have hp16 : 128 * d2FlowCandidateQuota d 16 2 .mid =
      15 * d2FlowCandidateCapacity d 1 17 := by
    rw [hq16, hcap]
    have hexp : 7 + (3 * d - 29) = 3 * d - 22 := by omega
    rw [show 128 = 2 ^ 7 by norm_num]
    rw [show 2 ^ 7 * (15 * 2 ^ (3 * d - 29)) =
      15 * (2 ^ 7 * 2 ^ (3 * d - 29)) by ring]
    rw [← pow_add, hexp]
  have hcover : d2FlowCandidateQuota d 17 1 .topRise <=
      8 * d2FlowCandidateQuota d 16 2 .mid := by
    nlinarith [hp17, hp16]
  have hreserve : d2FlowCandidateCapacity d 1 17 <=
      128 * d2FlowCandidateQuota d 16 2 .mid := by
    rw [hp16]
    omega
  have heven : d2FlowCandidateQuota d 17 1 .topRise % 2 = 0 := by
    rw [hq17]
    have hexp : 3 * d - 30 = (3 * d - 31) + 1 := by omega
    rw [hexp, pow_succ]
    omega
  exact ⟨hp17, hp16, hcover, hreserve, heven⟩

/-- Every level-two child root has received its Stage-16 middle quota by the
time the Stage-17 top-rise sender starts. This is the native reserve needed
for the later level-one allocation gate. -/
theorem d2FlowCandidateRun_stage17_levelOne_child_quota_floor
    (childDepth : Nat) (hd : 9 <= childDepth) (j k : Fin 8) :
    d2FlowCandidateQuota (childDepth + 7) 16 2 .mid <=
      d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowCandidateRun (childDepth + 7)
              (d2FlowTreeInitial 8192 (childDepth + 7)) 17) j) k) := by
  let d := childDepth + 7
  let initial := d2FlowTreeInitial 8192 d
  let run16 := d2FlowCandidateRun d initial 16
  let run17 := d2FlowCandidateRun d initial 17
  have hd14 : 14 <= d := by dsimp [d]; omega
  have hrun17 : run17 = d2FlowCandidateStage d 16 run16 := by
    change d2FlowCandidateRun d initial 17 =
      d2FlowCandidateStage d 16 (d2FlowCandidateRun d initial 16)
    rw [d2FlowCandidateRun.eq_def]
  have hfalse1 : d2FlowCandidateActive d 16 1 = false := by
    apply Bool.eq_false_of_not_eq_true
    intro ht
    have hlevels := (d2FlowCandidateActive_stage16_iff (d := d) (i := 1) hd14).mp ht
    have hneq : d ≠ 14 := by dsimp [d]; omega
    simp [hneq] at hlevels
  have hactive2 : d2FlowCandidateActive d 16 2 = true := by
    have hneq : d ≠ 14 := by dsimp [d]; omega
    have hlevels := (d2FlowCandidateActive_stage16_iff
      (d := d) (i := 2) hd14).mpr (by simp [hneq])
    exact hlevels
  have hrole2 : d2FlowCandidateRole d 16 2 = .mid :=
    d2FlowCandidateRole_stage16_internal_mid (d := d) (i := 2)
      (by omega) (Or.inl rfl)
  have hfloor :
      d2FlowCandidateQuota d 16 2 .mid <=
        d2FlowTreeRootDeficit
          (d2FlowTreeChild
            (d2FlowStage (d2FlowCandidateActive d 16)
              (d2FlowCandidateRole d 16) (d2FlowCandidateQuota d 16)
              (childDepth + 6) 1 (d2FlowTreeChild run16 j)) k) := by
    cases hp : d2FlowTreeChild run16 j with
    | node G low high children =>
      rw [d2FlowStage_inactive_child
        (active := d2FlowCandidateActive d 16)
        (role := d2FlowCandidateRole d 16)
        (quota := d2FlowCandidateQuota d 16)
        (h := childDepth + 5) (i := 1) (G := G)
        (low := low) (high := high) children hfalse1 k]
      cases hc : children k with
      | node G2 low2 high2 grandchildren =>
        rw [d2FlowStage_active_node_deficit
          (active := d2FlowCandidateActive d 16)
          (role := d2FlowCandidateRole d 16)
          (quota := d2FlowCandidateQuota d 16)
          (h := childDepth + 4) (i := 2)
          (G := G2) (low := low2) (high := high2)
          grandchildren hactive2]
        simp only [hrole2]
        omega
  change d2FlowCandidateQuota d 16 2 .mid <=
    d2FlowTreeRootDeficit (d2FlowTreeChild (d2FlowTreeChild run17 j) k)
  rw [hrun17]
  calc
    d2FlowCandidateQuota d 16 2 .mid <=
        d2FlowTreeRootDeficit
          (d2FlowTreeChild
            (d2FlowStage (d2FlowCandidateActive d 16)
              (d2FlowCandidateRole d 16) (d2FlowCandidateQuota d 16)
              (childDepth + 6) 1 (d2FlowTreeChild run16 j)) k) := hfloor
    _ = d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowStage (d2FlowCandidateActive d 16)
              (d2FlowCandidateRole d 16) (d2FlowCandidateQuota d 16)
              (childDepth + 7) 0 run16) j) k) := by
          rw [d2FlowStage_child_child_projection]

/-- At the two startup depths, Stage 17's level-one sender is a top-descending
reset. Its child contracts come from the checked level-two wrapper; the
Stage-16 invariant supplies balance, while the Stage-17 root-zero lemma
supplies the reset condition. -/
theorem d2FlowCandidateRun_stage17_levelOne_startup_inputs
    (childDepth : Nat) (hd : 7 <= childDepth) (hstartup : childDepth <= 8)
    (j : Fin 8) :
    let d := childDepth + 7
    let run17 := d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 17
    let tree := d2FlowTreeChild run17 j
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 17) (d2FlowCandidateRole d 17)
      (d2FlowCandidateQuota d 17)
      (fun x => d2FlowCandidateCapacity d x 17) 1 tree := by
  have hchild : childDepth = 7 \/ childDepth = 8 := by omega
  rcases hchild with h7 | h8
  · subst childDepth
    let d := 14
    let initial := d2FlowTreeInitial 8192 d
    let run17 := d2FlowCandidateRun d initial 17
    let tree := d2FlowTreeChild run17 j
    have hactive : d2FlowCandidateActive d 17 1 = true := by
      have hf := d2FlowCandidateActive_stage17_iff (d := d) (i := 1) (by omega)
      apply hf.mpr
      simp
    have hrole : d2FlowCandidateRole d 17 1 = .topDesc := by
      exact d2FlowCandidateRole_stage17_top (d := d) (by omega)
    have hchildren : forall k : Fin 8,
        d2FlowStageInvInputs 8192
          (d2FlowCandidateActive d 17) (d2FlowCandidateRole d 17)
          (d2FlowCandidateQuota d 17)
          (fun x => d2FlowCandidateCapacity d x 17) 2
          (d2FlowTreeChild tree k) := by
      intro k
      exact d2FlowCandidateRun_stage17_levelTwo_inputs 7 (by omega) j k
    have hinvRun := d2FlowCandidateStage16_preserves_inv 7 (by omega)
    have hinvTree := d2FlowTreeInv_child_stage17 run17 hinvRun j
    have hzero : d2FlowTreeRootDeficit tree = 0 := by
      exact d2FlowCandidateRun_stage17_levelOne_root_zero 7 (by omega) j
    have hbalance := d2FlowTreeInv_root_balance_of_zero tree hinvTree (by omega) hzero
    exact d2FlowStageInvInputs_topDesc_of_contract
      8192 1 tree hactive hrole hchildren hbalance hzero
  · subst childDepth
    let d := 15
    let initial := d2FlowTreeInitial 8192 d
    let run17 := d2FlowCandidateRun d initial 17
    let tree := d2FlowTreeChild run17 j
    have hactive : d2FlowCandidateActive d 17 1 = true := by
      have hf := d2FlowCandidateActive_stage17_iff (d := d) (i := 1) (by omega)
      apply hf.mpr
      simp
    have hrole : d2FlowCandidateRole d 17 1 = .topDesc := by
      exact d2FlowCandidateRole_stage17_top (d := d) (by omega)
    have hchildren : forall k : Fin 8,
        d2FlowStageInvInputs 8192
          (d2FlowCandidateActive d 17) (d2FlowCandidateRole d 17)
          (d2FlowCandidateQuota d 17)
          (fun x => d2FlowCandidateCapacity d x 17) 2
          (d2FlowTreeChild tree k) := by
      intro k
      exact d2FlowCandidateRun_stage17_levelTwo_inputs 8 (by omega) j k
    have hinvRun := d2FlowCandidateStage16_preserves_inv 8 (by omega)
    have hinvTree := d2FlowTreeInv_child_stage17 run17 hinvRun j
    have hzero : d2FlowTreeRootDeficit tree = 0 := by
      exact d2FlowCandidateRun_stage17_levelOne_root_zero 8 (by omega) j
    have hbalance := d2FlowTreeInv_root_balance_of_zero tree hinvTree (by omega) hzero
    exact d2FlowStageInvInputs_topDesc_of_contract
      8192 1 tree hactive hrole hchildren hbalance hzero

/-- At every non-startup depth, the Stage-17 level-one top-rise sender has
enough total fresh reserve and both endpoint reserves from the Stage-16
level-two middle quotas. -/
theorem d2FlowCandidateRun_stage17_levelOne_late_inputs
    (childDepth : Nat) (hd : 9 <= childDepth) (j : Fin 8) :
    let d := childDepth + 7
    let run17 := d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 17
    let tree := d2FlowTreeChild run17 j
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 17) (d2FlowCandidateRole d 17)
      (d2FlowCandidateQuota d 17)
      (fun x => d2FlowCandidateCapacity d x 17) 1 tree := by
  classical
  let d := childDepth + 7
  let initial := d2FlowTreeInitial 8192 d
  let run17 := d2FlowCandidateRun d initial 17
  let tree := d2FlowTreeChild run17 j
  have hd14 : 14 <= d := by dsimp [d]; omega
  have hlate : 15 < d := by dsimp [d]; omega
  have hactive : d2FlowCandidateActive d 17 1 = true :=
    (d2FlowCandidateActive_stage17_iff hd14).2 (Or.inl rfl)
  have hrole : d2FlowCandidateRole d 17 1 = .topRise := by
    rw [d2FlowCandidateRole_stage17_top hd14]
    simp [show ¬ d <= 15 by omega]
  have hchildren : forall k : Fin 8,
      d2FlowStageInvInputs 8192
        (d2FlowCandidateActive d 17) (d2FlowCandidateRole d 17)
        (d2FlowCandidateQuota d 17)
        (fun x => d2FlowCandidateCapacity d x 17) 2
        (d2FlowTreeChild tree k) := by
    intro k
    exact d2FlowCandidateRun_stage17_levelTwo_inputs childDepth
      (by omega) j k
  have hzero : d2FlowTreeRootDeficit tree = 0 :=
    d2FlowCandidateRun_stage17_levelOne_root_zero childDepth (by omega) j
  have hinvRun := d2FlowCandidateStage16_preserves_inv childDepth (by omega)
  have hinvTree : d2FlowTreeInv 8192 tree := by
    exact d2FlowTreeInv_child_stage17 run17 hinvRun j
  have hbalance := d2FlowTreeInv_root_balance_of_zero
    tree hinvTree (by omega) hzero
  have harith := d2FlowCandidateStage17_levelOne_quota_arithmetic
    (d := d) (by omega)
  have hquotaCap : 256 * d2FlowCandidateQuota d 17 1 .topRise <=
      d2FlowCandidateCapacity d 1 17 := by
    rw [harith.1]
  have heven : d2FlowCandidateQuota d 17 1 .topRise % 2 = 0 :=
    harith.2.2.2.2
  have hfloor : forall k : Fin 8,
      d2FlowCandidateQuota d 16 2 .mid <=
        d2FlowTreeRootDeficit (d2FlowTreeChild tree k) := by
    intro k
    simpa [d, initial, run17, tree] using
      d2FlowCandidateRun_stage17_levelOne_child_quota_floor
        childDepth (by omega) j k
  have htotal : 8 * d2FlowCandidateQuota d 16 2 .mid <=
      d2FlowTotal (fun k =>
        d2FlowTreeRootDeficit (d2FlowTreeChild tree k)) := by
    change 8 * d2FlowCandidateQuota d 16 2 .mid <=
      Finset.univ.sum (fun k : Fin 8 =>
        d2FlowTreeRootDeficit (d2FlowTreeChild tree k))
    calc
      8 * d2FlowCandidateQuota d 16 2 .mid =
          Finset.univ.sum (fun _ : Fin 8 =>
            d2FlowCandidateQuota d 16 2 .mid) := by simp
      _ <= Finset.univ.sum (fun k : Fin 8 =>
          d2FlowTreeRootDeficit (d2FlowTreeChild tree k)) := by
        apply Finset.sum_le_sum
        intro k hk
        exact hfloor k
  have halloc : d2FlowCandidateQuota d 17 1 .topRise <=
      d2FlowTotal (fun k =>
        d2FlowTreeRootDeficit (d2FlowTreeChild tree k)) -
        d2FlowTreeRootDeficit tree := by
    rw [hzero]
    omega
  have hleft : d2FlowCandidateCapacity d 1 17 <=
      128 * d2FlowTreeRootDeficit
        (d2FlowTreeChild tree (Fin.mk 0 (by omega))) := by
    have hf := hfloor (Fin.mk 0 (by omega))
    nlinarith [harith.2.2.2.1]
  have hright : d2FlowCandidateCapacity d 1 17 <=
      128 * d2FlowTreeRootDeficit
        (d2FlowTreeChild tree (Fin.mk 7 (by omega))) := by
    have hf := hfloor (Fin.mk 7 (by omega))
    nlinarith [harith.2.2.2.1]
  exact d2FlowStageInvInputs_topRise_of_contract
    8192 1 tree hactive hrole hchildren hbalance (by simp [hzero])
    hquotaCap halloc heven hleft hright

/-- Complete the level-one input contract at every Stage-17 depth by joining
the two startup resets to the later top-rise reserve argument. -/
theorem d2FlowCandidateRun_stage17_levelOne_inputs
    (childDepth : Nat) (hd : 7 <= childDepth) (j : Fin 8) :
    let d := childDepth + 7
    let run17 := d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 17
    let tree := d2FlowTreeChild run17 j
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 17) (d2FlowCandidateRole d 17)
      (d2FlowCandidateQuota d 17)
      (fun x => d2FlowCandidateCapacity d x 17) 1 tree := by
  by_cases hstartup : childDepth <= 8
  · exact d2FlowCandidateRun_stage17_levelOne_startup_inputs
      childDepth hd hstartup j
  · have hd9 : 9 <= childDepth := by omega
    exact d2FlowCandidateRun_stage17_levelOne_late_inputs
      childDepth hd9 j

/-- The inactive Stage-17 root gathers the completed level-one contracts. -/
theorem d2FlowCandidateRun_stage17_root_inputs
    (childDepth : Nat) (hd : 7 <= childDepth) :
    let d := childDepth + 7
    let run17 := d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 17
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 17) (d2FlowCandidateRole d 17)
      (d2FlowCandidateQuota d 17)
      (fun x => d2FlowCandidateCapacity d x 17) 0 run17 := by
  classical
  let d := childDepth + 7
  let initial := d2FlowTreeInitial 8192 d
  let run17 := d2FlowCandidateRun d initial 17
  have hd14 : 14 <= d := by dsimp [d]; omega
  have hfalse : d2FlowCandidateActive d 17 0 = false := by
    apply Bool.eq_false_of_not_eq_true
    intro ht
    have hlevels := (d2FlowCandidateActive_stage17_iff
      (d := d) (i := 0) hd14).mp ht
    rcases hlevels with h | h | h | h <;> omega
  have hchildren : forall j : Fin 8,
      d2FlowStageInvInputs 8192
        (d2FlowCandidateActive d 17) (d2FlowCandidateRole d 17)
        (d2FlowCandidateQuota d 17)
        (fun x => d2FlowCandidateCapacity d x 17) 1
        (d2FlowTreeChild run17 j) := by
    intro j
    have hj := d2FlowCandidateRun_stage17_levelOne_inputs childDepth hd j
    simpa [d, initial, run17] using hj
  exact d2FlowStageInvInputs_inactive_of_children
    (active := d2FlowCandidateActive d 17)
    (role := d2FlowCandidateRole d 17)
    (quota := d2FlowCandidateQuota d 17)
    (cap := fun x => d2FlowCandidateCapacity d x 17)
    8192 0 run17 hfalse hchildren

/-- Stage 17 preserves the recursive flow invariant for every eligible depth. -/
theorem d2FlowCandidateStage17_preserves_inv
    (childDepth : Nat) (hd : 7 <= childDepth) :
    d2FlowTreeInv 8192
      (d2FlowCandidateRun (childDepth + 7)
        (d2FlowTreeInitial 8192 (childDepth + 7)) 18) := by
  let d := (childDepth + 6) + 1
  let initial := d2FlowTreeInitial 8192 d
  let before := d2FlowCandidateRun d initial 17
  have hinv : d2FlowTreeInv 8192 before := by
    simpa [d, initial, before] using
      d2FlowCandidateStage16_preserves_inv childDepth hd
  have hinputs : d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 17) (d2FlowCandidateRole d 17)
      (d2FlowCandidateQuota d 17)
      (fun x => d2FlowCandidateCapacity d x 17) 0 before := by
    simpa [d, initial, before] using
      d2FlowCandidateRun_stage17_root_inputs childDepth hd
  have hpres := d2FlowStage_preserves_inv_of_inputs
    (active := d2FlowCandidateActive d 17)
    (role := d2FlowCandidateRole d 17)
    (quota := d2FlowCandidateQuota d 17)
    (cap := fun x => d2FlowCandidateCapacity d x 17)
    (i := 0) before hinv hinputs
  change d2FlowTreeInv 8192 (d2FlowCandidateRun d initial 18)
  rw [d2FlowCandidateRun.eq_def]
  exact hpres

end Chvatal.D2Reserve
