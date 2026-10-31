import D2Stage19LevelSevenBalance
import D2Stage18LevelSixInputs
import D2Stage14Contract

namespace Chvatal.D2Reserve

attribute [local irreducible] d2FlowStageInvInputs
attribute [local irreducible] d2FlowTreeInv
attribute [local irreducible] d2FlowCandidateRun

set_option maxHeartbeats 20000000
set_option maxRecDepth 4096

private theorem d2FlowStageInvInputs_inactive_tail_stage19
    {scale : Nat} {active : Nat → Bool} {role : Nat → D2Role}
    {quota : Nat → D2Role → Nat} {cap : Nat → Nat}
    (i : Nat) : ∀ {h : Nat} (tree : D2FlowTree h),
      (∀ t, i ≤ t → active t = false) →
      d2FlowStageInvInputs scale active role quota cap i tree := by
  intro h
  induction h generalizing i with
  | zero => intro tree _; cases tree <;> simp [d2FlowStageInvInputs]
  | succ h ih =>
      intro tree hinactive
      cases tree with
      | node G low high children =>
          have hfalse : active i = false := hinactive i (Nat.le_refl i)
          simp only [d2FlowStageInvInputs, hfalse]
          refine ⟨?_, trivial⟩
          intro j
          exact ih (i + 1) (children j) (by
            intro t ht
            exact hinactive t (by omega))

/-- The complete Stage-19 level-seven bottom-descending input contract. The
preceding Stage-18 level-six middle sender supplies the root cap; the
bottom-rise refresh makes all eight level-eight roots native and full. -/
theorem d2FlowCandidateRun_stage19_levelSeven_inputs
    (childDepth : Nat) (hd : 7 <= childDepth)
    (j k m l q r s : Fin 8) :
    let d := childDepth + 9
    let run19 := d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 19
    let tree := d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild run19 j) k) m) l) q) r) s
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 19) (d2FlowCandidateRole d 19)
      (d2FlowCandidateQuota d 19)
      (fun x => d2FlowCandidateCapacity d x 19) 7 tree := by
  let d := childDepth + 9
  let initial := d2FlowTreeInitial 8192 d
  let run18 := d2FlowCandidateRun d initial 18
  let run19 := d2FlowCandidateRun d initial 19
  let parent := d2FlowTreeChild
    (d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild run18 j) k) m) l) q) r
  let tree := d2FlowTreeChild
    (d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild run19 j) k) m) l) q) r) s
  classical
  have hd14 : 14 <= d := by dsimp [d]; omega
  have hactive19 : d2FlowCandidateActive d 19 7 = true := by
    apply (d2FlowCandidateActive_stage19_iff hd14).2
    by_cases hsmall : d <= 15 <;> simp [hsmall]
  have hrole19 : d2FlowCandidateRole d 19 7 = .botDesc :=
    d2FlowCandidateRole_stage19_bottom hd14
  have hactive18 : d2FlowCandidateActive d 18 6 = true := by
    apply (d2FlowCandidateActive_stage18_iff hd14).2
    by_cases hsmall : d <= 15 <;> simp [hsmall]
  have hrole18 : d2FlowCandidateRole d 18 6 = .mid :=
    d2FlowCandidateRole_stage18_mid46 hd14 6 (Or.inr rfl)
  have hregular18 : d2FlowCandidateRole d 18 6 = .topRise \/
      d2FlowCandidateRole d 18 6 = .mid \/
      d2FlowCandidateRole d 18 6 = .botDesc := Or.inr (Or.inl hrole18)
  have hrunInv : d2FlowTreeInv 8192 run18 := by
    simpa [d, initial, run18] using
      d2FlowCandidateStage17_preserves_inv (childDepth + 2) (by omega)
  have hinv2 : d2FlowTreeInv 8192
      (d2FlowTreeChild (d2FlowTreeChild run18 j) k) :=
    d2FlowTreeInv_grandchild (h := childDepth + 7) run18 hrunInv j k
  have hinv4 : d2FlowTreeInv 8192
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild run18 j) k) m) l) :=
    d2FlowTreeInv_grandchild (h := childDepth + 5)
      (d2FlowTreeChild (d2FlowTreeChild run18 j) k) hinv2 m l
  have hinv6 : d2FlowTreeInv 8192 parent := by
    simpa [parent] using
      d2FlowTreeInv_grandchild (h := childDepth + 3)
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild run18 j) k) m) l) hinv4 q r
  have hparentInputs : d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 18) (d2FlowCandidateRole d 18)
      (d2FlowCandidateQuota d 18)
      (fun x => d2FlowCandidateCapacity d x 18) 6 parent := by
    have hp := d2FlowCandidateRun_stage18_levelSix_inputs
      (childDepth + 2) (by omega) j k m l q r
    simpa [d, initial, run18, parent] using hp
  have hrun19 : run19 = d2FlowCandidateStage d 18 run18 := by
    change d2FlowCandidateRun d initial 19 =
      d2FlowCandidateStage d 18 (d2FlowCandidateRun d initial 18)
    rw [d2FlowCandidateRun.eq_def]
  have htreeEq : tree = d2FlowTreeChild
      (d2FlowStage (d2FlowCandidateActive d 18)
        (d2FlowCandidateRole d 18) (d2FlowCandidateQuota d 18)
        (childDepth + 3) 6 parent) s := by
    dsimp only [tree]
    rw [hrun19]
    simp only [d2FlowCandidateStage]
    exact d2FlowStage_path7_child_projection
      (active := d2FlowCandidateActive d 18)
      (role := d2FlowCandidateRole d 18)
      (quota := d2FlowCandidateQuota d 18)
      (h := childDepth + 2) (i := 0) run18 j k m l q r s
  have hchildBound := d2FlowStage_regular_child_g_bound_of_tree_inputs
    (active := d2FlowCandidateActive d 18)
    (role := d2FlowCandidateRole d 18)
    (quota := d2FlowCandidateQuota d 18)
    (cap := fun x => d2FlowCandidateCapacity d x 18)
    (stageDepth := childDepth + 2) (i := 6) parent
    hactive18 hregular18 hinv6 hparentInputs
  have hcapShift : d2FlowCandidateCapacity d 7 19 =
      2 * d2FlowCandidateCapacity d 6 18 :=
    d2FlowCandidateCapacity_succ_level_next_stage d 6 18 (by omega)
  have hrootcap : 512 * d2FlowTreeRootDeficit tree <=
      d2FlowCandidateCapacity d 7 19 := by
    have hc := hchildBound s
    rw [htreeEq, hcapShift]
    exact hc
  have hbalance : (d2FlowTreeRootData tree).2.1 +
      (d2FlowTreeRootData tree).2.2 = d2FlowTreeRootDeficit tree := by
    simpa [d, initial, run19, tree] using
      d2FlowCandidateRun_stage19_levelSeven_balanced
        (childDepth + 2) (by omega) j k m l q r s
  have hquotaActive : d2FlowCandidateActive d 19 7 = true := hactive19
  have hmatch := d2FlowCandidateActive_matches_schedule
    (d := d) (i := 7) (t := 19) (by omega)
  rw [hquotaActive] at hmatch
  have hschedActive : active d (tfD2 d) 7 19 := of_decide_eq_true hmatch.symm
  have hschedRole : d2ScheduleRole d 7 19 = .botDesc := by
    simpa [d2FlowCandidateRole] using hrole19
  have hqcap := d2FlowCandidateQuota_le_capacity_div_256
    (by omega) hschedActive (Or.inr (Or.inr hschedRole))
  have heven := d2FlowCandidateQuota_even
    (by omega) hschedActive (by omega) (Or.inr (Or.inr hschedRole))
  have hquotaCap : 256 * d2FlowCandidateQuota d 19 7 .botDesc <=
      d2FlowCandidateCapacity d 7 19 := by
    simpa [hschedRole, hrole19] using hqcap
  have heven' : d2FlowCandidateQuota d 19 7 .botDesc % 2 = 0 := by
    simpa [hrole19] using heven
  have hcapMass : d2FlowCandidateCapacity d 7 19 =
      8192 * 8 ^ (childDepth + 2) := by
    have hexp : d2FlowCandidateCapacityExponent d 7 19 =
        13 + 3 * (childDepth + 2) := by
      unfold d2FlowCandidateCapacityExponent
      dsimp [d]
      omega
    rw [d2FlowCandidateCapacity, hexp]
    rw [show (8192 : Nat) = 2 ^ 13 by norm_num,
      show (8 : Nat) = 2 ^ 3 by norm_num]
    rw [pow_add, ← Nat.pow_mul]
  have hrootfull : ∀ v : Fin 8,
      d2FlowTreeRootDeficit (d2FlowTreeChild tree v) =
        8192 * 8 ^ (childDepth + 1) := by
    intro v
    simpa [d, initial, run19, tree] using
      d2FlowCandidateRun_stage19_levelEight_root_full
        childDepth hd j k m l q r s v
  have htotal : d2FlowTotal (fun v : Fin 8 =>
      d2FlowTreeRootDeficit (d2FlowTreeChild tree v)) =
        8192 * 8 ^ (childDepth + 2) := by
    unfold d2FlowTotal
    calc
      (Finset.univ.sum fun v : Fin 8 =>
          d2FlowTreeRootDeficit (d2FlowTreeChild tree v)) =
        Finset.univ.sum (fun _ : Fin 8 => 8192 * 8 ^ (childDepth + 1)) := by
          apply Finset.sum_congr rfl
          intro v hv
          rw [hrootfull v]
      _ = 8 * (8192 * 8 ^ (childDepth + 1)) := by simp
      _ = 8192 * 8 ^ (childDepth + 2) := by
        rw [Nat.pow_succ]
        ring
  have halloc : d2FlowCandidateQuota d 19 7 .botDesc <=
      d2FlowTotal (fun v =>
        d2FlowTreeRootDeficit (d2FlowTreeChild tree v)) -
        d2FlowTreeRootDeficit tree := by
    have hsum : d2FlowCandidateQuota d 19 7 .botDesc +
        d2FlowTreeRootDeficit tree <= d2FlowCandidateCapacity d 7 19 := by
      nlinarith [hrootcap, hquotaCap,
        Nat.zero_le (d2FlowCandidateCapacity d 7 19)]
    rw [htotal, ← hcapMass]
    omega
  have hmassNonneg : 0 <= 8192 * 8 ^ (childDepth + 1) := Nat.zero_le _
  have hleft : d2FlowCandidateCapacity d 7 19 <=
      128 * d2FlowTreeRootDeficit
        (d2FlowTreeChild tree (Fin.mk 0 (by omega))) := by
    rw [hcapMass, hrootfull]
    rw [show childDepth + 2 = (childDepth + 1) + 1 by omega, Nat.pow_succ]
    nlinarith [hmassNonneg]
  have hright : d2FlowCandidateCapacity d 7 19 <=
      128 * d2FlowTreeRootDeficit
        (d2FlowTreeChild tree (Fin.mk 7 (by omega))) := by
    rw [hcapMass, hrootfull]
    rw [show childDepth + 2 = (childDepth + 1) + 1 by omega, Nat.pow_succ]
    nlinarith [hmassNonneg]
  have hchildren : ∀ v : Fin 8,
      d2FlowStageInvInputs 8192
        (d2FlowCandidateActive d 19) (d2FlowCandidateRole d 19)
        (d2FlowCandidateQuota d 19)
        (fun x => d2FlowCandidateCapacity d x 19) 8
        (d2FlowTreeChild tree v) := by
    intro v
    apply d2FlowStageInvInputs_inactive_tail_stage19
      (scale := 8192) (active := d2FlowCandidateActive d 19)
      (role := d2FlowCandidateRole d 19)
      (quota := d2FlowCandidateQuota d 19)
      (cap := fun x => d2FlowCandidateCapacity d x 19) 8
    intro t ht
    cases h : d2FlowCandidateActive d 19 t with
    | false => rfl
    | true =>
        have hs := (d2FlowCandidateActive_stage19_iff hd14).mp h
        by_cases hsmall : d <= 15 <;> simp [hsmall] at hs <;> omega
  have hcontract := d2FlowStageInvInputs_botDesc_of_contract
    (scale := 8192) (i := 7) tree hactive19 hrole19 hchildren
    hbalance hrootcap hquotaCap halloc heven' hleft hright
  simpa [d, initial, run19, tree] using hcontract
