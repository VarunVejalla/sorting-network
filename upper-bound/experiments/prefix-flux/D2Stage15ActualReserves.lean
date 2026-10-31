import D2Stage15Frontier
import D2Stage15LevelThreeRootCap

namespace Chvatal.D2Reserve

set_option maxHeartbeats 2000000

/-- If the level-three ancestor is inactive, projecting a four-edge path
through a stage gives exactly the level-four node's own recursive stage
output. Earlier ancestor overwrites cannot affect that deeper root. -/
theorem d2FlowStage_path4_root_of_inactive_parent
    {active : Nat -> Bool} {role : Nat -> D2Role}
    {quota : Nat -> D2Role -> Nat} {h i : Nat}
    (tree : D2FlowTree (h + 4)) (j k m l : Fin 8)
    (hinactive : active (i + 3) = false) :
    d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowStage active role quota (h + 4) i tree) j) k) m) l) =
    d2FlowTreeRootDeficit
      (d2FlowStage active role quota h (i + 4)
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild tree j) k) m) l)) := by
  rw [d2FlowStage_path4_projection]
  cases htree : d2FlowTreeChild
      (d2FlowTreeChild (d2FlowTreeChild tree j) k) m with
  | node G low high children =>
      rw [d2FlowStage_inactive_child
        (active := active) (role := role) (quota := quota)
        (i := i + 3) children hinactive l]
      rfl

/-- Tree-valued version of the four-edge projection. -/
theorem d2FlowStage_path4_tree_of_inactive_parent
    {active : Nat -> Bool} {role : Nat -> D2Role}
    {quota : Nat -> D2Role -> Nat} {h i : Nat}
    (tree : D2FlowTree (h + 4)) (j k m l : Fin 8)
    (hinactive : active (i + 3) = false) :
    d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowStage active role quota (h + 4) i tree) j) k) m) l =
    d2FlowStage active role quota h (i + 4)
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild tree j) k) m) l) := by
  rw [d2FlowStage_path4_projection]
  cases htree : d2FlowTreeChild
      (d2FlowTreeChild (d2FlowTreeChild tree j) k) m with
  | node G low high children =>
      rw [d2FlowStage_inactive_child
        (active := active) (role := role) (quota := quota)
        (i := i + 3) children hinactive l]
      rfl

private theorem d2FlowCandidateActive_stage14_level_one_false
    {d : Nat} (_hd : 14 <= d) :
    d2FlowCandidateActive d 14 1 = false := by
  classical
  have hmatch := d2FlowCandidateActive_matches_schedule
    (d := d) (i := 1) (t := 14) (by omega)
  rw [hmatch]
  simp only [decide_eq_false_iff_not, active,
    if_neg (by decide : ¬ ((14 : Nat) = 1))]
  omega
private theorem d2FlowCandidateActive_stage14_level_three_false
    {d : Nat} (_hd : 14 <= d) :
    d2FlowCandidateActive d 14 3 = false := by
  classical
  have hmatch := d2FlowCandidateActive_matches_schedule
    (d := d) (i := 3) (t := 14) (by omega)
  rw [hmatch]
  simp only [decide_eq_false_iff_not, active,
    if_neg (by decide : ¬ ((14 : Nat) = 1))]
  omega

/-- The level-four root after the actual Stage-14 run is exactly its local
Stage-14 transition output, for every branch of the tree. -/
theorem d2FlowCandidateRun_stage15_levelFour_root_eq_local
    (h : Nat) (hd : 14 <= h + 5) (j k m l : Fin 8) :
    d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowCandidateRun (h + 5)
                (d2FlowTreeInitial 8192 (h + 5)) 15) j) k) m) l) =
    d2FlowTreeRootDeficit
      (d2FlowStage (d2FlowCandidateActive (h + 5) 14)
        (d2FlowCandidateRole (h + 5) 14)
        (d2FlowCandidateQuota (h + 5) 14)
        (h + 1) 4
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowCandidateRun (h + 5)
                  (d2FlowTreeInitial 8192 (h + 5)) 14) j) k) m) l)) := by
  let d := h + 5
  let before := d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 14
  have hinactive := d2FlowCandidateActive_stage14_level_three_false
    (d := d) (by omega)
  have hprojection := d2FlowStage_path4_root_of_inactive_parent
    (active := d2FlowCandidateActive d 14)
    (role := d2FlowCandidateRole d 14)
    (quota := d2FlowCandidateQuota d 14)
    (h := h + 1) (i := 0) before j k m l hinactive
  change d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowCandidateStage d 14 before) j) k) m) l) = _
  simpa [d, d2FlowCandidateStage] using hprojection

/-- The complete level-four subtree after Stage 15 equals the local output
of its active Stage-14 sender, not just its root deficit. -/
theorem d2FlowCandidateRun_stage15_levelFour_tree_eq_local
    (h : Nat) (hd : 14 <= h + 5) (j k m l : Fin 8) :
    d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowCandidateRun (h + 5)
              (d2FlowTreeInitial 8192 (h + 5)) 15) j) k) m) l =
    d2FlowStage (d2FlowCandidateActive (h + 5) 14)
      (d2FlowCandidateRole (h + 5) 14)
      (d2FlowCandidateQuota (h + 5) 14) (h + 1) 4
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowCandidateRun (h + 5)
                (d2FlowTreeInitial 8192 (h + 5)) 14) j) k) m) l) := by
  let d := h + 5
  let before := d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 14
  have hinactive := d2FlowCandidateActive_stage14_level_three_false
    (d := d) (by omega)
  have hprojection := d2FlowStage_path4_tree_of_inactive_parent
    (active := d2FlowCandidateActive d 14)
    (role := d2FlowCandidateRole d 14)
    (quota := d2FlowCandidateQuota d 14)
    (h := h + 1) (i := 0) before j k m l hinactive
  have hrun : d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 15 =
      d2FlowCandidateStage d 14 before := rfl
  change d2FlowTreeChild
    (d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowCandidateStage d 14 before) j) k) m) l = _
  simpa [d, before, d2FlowCandidateStage] using hprojection

/-- The actual Stage-15 level-three sender has its endpoint reserve, supplied
by the active Stage-14 level-four sender below it. -/
theorem d2FlowCandidateRun_stage15_levelThree_endpoint_reserve
    (h : Nat) (hd : 14 <= h + 5) (j k m l : Fin 8) :
    d2FlowCandidateCapacity (h + 5) 3 15 <=
      128 * d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowCandidateRun (h + 5)
                  (d2FlowTreeInitial 8192 (h + 5)) 15) j) k) m) l) := by
  rw [d2FlowCandidateRun_stage15_levelFour_root_eq_local h hd j k m l]
  let d := h + 5
  let before := d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 14
  let node := d2FlowTreeChild (d2FlowTreeChild
    (d2FlowTreeChild (d2FlowTreeChild before j) k) m) l
  cases hnode : node with
  | node G low high children =>
      have hlocal := d2FlowCandidateStage14_levelFour_funds_stage15_levelThree_reserve
        (d := d) (h := h) (G := G) (low := low) (high := high)
        (by omega) children
      simpa [d, before, node, hnode] using hlocal

/-- Six-edge analogue of the inactive-ancestor root projection. -/
theorem d2FlowStage_path6_root_of_inactive_parent
    {active : Nat -> Bool} {role : Nat -> D2Role}
    {quota : Nat -> D2Role -> Nat} {h i : Nat}
    (tree : D2FlowTree (h + 6)) (j k m l q s : Fin 8)
    (hinactive : active (i + 5) = false) :
    d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild
                  (d2FlowStage active role quota (h + 6) i tree) j) k) m) l) q) s) =
    d2FlowTreeRootDeficit
      (d2FlowStage active role quota h (i + 6)
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild
                  (d2FlowTreeChild tree j) k) m) l) q) s)) := by
  rw [d2FlowStage_path6_projection]
  cases htree : d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild tree j) k) m) l) q with
  | node G low high children =>
      rw [d2FlowStage_inactive_child
        (active := active) (role := role) (quota := quota)
        (i := i + 5) children hinactive s]
      rfl

private theorem d2FlowCandidateActive_stage14_level_five_false
    {d : Nat} (_hd : 14 <= d) :
    d2FlowCandidateActive d 14 5 = false := by
  classical
  have hmatch := d2FlowCandidateActive_matches_schedule
    (d := d) (i := 5) (t := 14) (by omega)
  rw [hmatch]
  simp only [decide_eq_false_iff_not, active,
    if_neg (by decide : ¬ ((14 : Nat) = 1))]
  omega

/-- The actual level-six root after Stage 14 equals the local transition at
that sender because its level-five parent is inactive. -/
theorem d2FlowCandidateRun_stage15_levelSix_root_eq_local
    (h : Nat) (hd : 14 <= h + 7) (j k m l q s : Fin 8) :
    d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild
                  (d2FlowCandidateRun (h + 7)
                    (d2FlowTreeInitial 8192 (h + 7)) 15) j) k) m) l) q) s) =
    d2FlowTreeRootDeficit
      (d2FlowStage (d2FlowCandidateActive (h + 7) 14)
        (d2FlowCandidateRole (h + 7) 14)
        (d2FlowCandidateQuota (h + 7) 14)
        (h + 1) 6
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild
                  (d2FlowTreeChild
                    (d2FlowCandidateRun (h + 7)
                      (d2FlowTreeInitial 8192 (h + 7)) 14) j) k) m) l) q) s)) := by
  let d := h + 7
  let before := d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 14
  have hinactive := d2FlowCandidateActive_stage14_level_five_false
    (d := d) (by omega)
  have hprojection := d2FlowStage_path6_root_of_inactive_parent
    (active := d2FlowCandidateActive d 14)
    (role := d2FlowCandidateRole d 14)
    (quota := d2FlowCandidateQuota d 14)
    (h := h + 1) (i := 0) before j k m l q s hinactive
  change d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild
                  (d2FlowCandidateStage d 14 before) j) k) m) l) q) s) = _
  simpa [d, d2FlowCandidateStage] using hprojection

/-- The actual Stage-15 level-five sender receives its endpoint reserve from
its active Stage-14 level-six child sender. -/
theorem d2FlowCandidateRun_stage15_levelFive_endpoint_reserve
    (h : Nat) (hd : 14 <= h + 7) (j k m l q s : Fin 8) :
    d2FlowCandidateCapacity (h + 7) 5 15 <=
      128 * d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild
                  (d2FlowTreeChild
                    (d2FlowCandidateRun (h + 7)
                      (d2FlowTreeInitial 8192 (h + 7)) 15) j) k) m) l) q) s) := by
  rw [d2FlowCandidateRun_stage15_levelSix_root_eq_local h hd j k m l q s]
  let d := h + 7
  let before := d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 14
  let node := d2FlowTreeChild (d2FlowTreeChild
    (d2FlowTreeChild (d2FlowTreeChild
      (d2FlowTreeChild (d2FlowTreeChild before j) k) m) l) q) s
  cases hnode : node with
  | node G low high children =>
      have hlocal := d2FlowCandidateStage14_levelSix_funds_stage15_levelFive_reserve
        (d := d) (h := h) (G := G) (low := low) (high := high)
        (by omega) children
      simpa [d, before, node, hnode] using hlocal
/-- The inactive Stage-14 level-three parent retains its old deficit, while
all eight active level-four children add their Stage-14 quota. This supplies
the aggregate fresh mass needed for a Stage-15 level-three allocation. -/
theorem d2FlowStage_stage15_levelThree_allocation_from_child_quotas
    {h G low high qNext : Nat}
    {active : Nat -> Bool} {role : Nat -> D2Role}
    {quota : Nat -> D2Role -> Nat}
    (children : Fin 8 -> D2FlowTree (h + 1))
    (hinv : G <= d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)))
    (hinactive : active 3 = false)
    (hactive : active 4 = true)
    (hrole : role 4 = .mid)
    (hq : qNext <= 8 * quota 4 .mid) :
    qNext <= d2FlowTotal (fun j =>
      d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowStage active role quota (h + 2) 3
            (.node G low high children)) j)) - G := by
  have hroot (j : Fin 8) :
      d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowStage active role quota (h + 2) 3
            (.node G low high children)) j) =
        d2FlowTreeRootDeficit (children j) + quota 4 .mid := by
    rw [d2FlowStage_inactive_child children hinactive j]
    cases hc : children j with
    | node G' low' high' grandchildren =>
        rw [d2FlowStage_active_node_deficit grandchildren hactive, hrole]
        rfl
  have hsum : d2FlowTotal (fun j =>
      d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowStage active role quota (h + 2) 3
            (.node G low high children)) j)) =
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) +
        8 * quota 4 .mid := by
    change (Finset.univ.sum fun j : Fin 8 =>
        d2FlowTreeRootDeficit
          (d2FlowTreeChild
            (d2FlowStage active role quota (h + 2) 3
              (.node G low high children)) j)) =
      (Finset.univ.sum fun j : Fin 8 => d2FlowTreeRootDeficit (children j)) +
        8 * quota 4 .mid
    calc
      (Finset.univ.sum fun j : Fin 8 =>
          d2FlowTreeRootDeficit
            (d2FlowTreeChild
              (d2FlowStage active role quota (h + 2) 3
                (.node G low high children)) j)) =
          Finset.univ.sum (fun j : Fin 8 =>
            d2FlowTreeRootDeficit (children j) + quota 4 .mid) := by
              apply Finset.sum_congr rfl
              intro j hj
              exact hroot j
      _ = (Finset.univ.sum fun j : Fin 8 => d2FlowTreeRootDeficit (children j)) +
            Finset.univ.sum (fun _ : Fin 8 => quota 4 .mid) := by
              rw [Finset.sum_add_distrib]
      _ = (Finset.univ.sum fun j : Fin 8 => d2FlowTreeRootDeficit (children j)) +
            8 * quota 4 .mid := by simp
  rw [hsum]
  omega

/-- In the concrete schedule, eight Stage-14 level-four mid quotas dominate
the Stage-15 level-three quota by a large margin. -/
theorem d2FlowCandidateStage14_eight_levelFour_quotas_cover_stage15_levelThree
    {d : Nat} (hd : 14 <= d) :
    d2FlowCandidateQuota d 15 3 .mid <=
      8 * d2FlowCandidateQuota d 14 4 .mid := by
  have hscale := d2FlowCandidateCapacity_stage14_child_eq_32_stage15_parent
    (d := d) (i := 3) hd
  have h14 := d2FlowCandidateStage14_quota_exact_ratio
    (d := d) (i := 3) hd (r := .mid) (Or.inl rfl)
  have h15 : 4096 * d2FlowCandidateQuota d 15 3 .mid =
      15 * d2FlowCandidateCapacity d 3 15 := by
    let e := d2FlowCandidateCapacityExponent d 3 15
    have he : 12 <= e := by dsimp [e, d2FlowCandidateCapacityExponent]; omega
    have hp : 2 ^ 12 * 2 ^ (e - 12) = 2 ^ e := by
      rw [← pow_add]
      congr 1
      omega
    change 4096 * (15 * 2 ^ (e - 12)) = 15 * 2 ^ e
    calc
      4096 * (15 * 2 ^ (e - 12)) = 15 * (2 ^ 12 * 2 ^ (e - 12)) := by ring
      _ = 15 * 2 ^ e := by rw [hp]
  rw [hscale] at h14
  nlinarith
/-- The Stage-14 level-four mid quota is exactly 32 times the Stage-15
level-three mid quota. -/
theorem d2FlowCandidateStage14_levelFour_quota_eq_32_stage15_levelThree
    {d : Nat} (hd : 14 <= d) :
    d2FlowCandidateQuota d 14 4 .mid =
      32 * d2FlowCandidateQuota d 15 3 .mid := by
  have hscale := d2FlowCandidateCapacity_stage14_child_eq_32_stage15_parent
    (d := d) (i := 3) hd
  have h14 := d2FlowCandidateStage14_quota_exact_ratio
    (d := d) (i := 3) hd (r := .mid) (Or.inl rfl)
  have h15 : 4096 * d2FlowCandidateQuota d 15 3 .mid =
      15 * d2FlowCandidateCapacity d 3 15 := by
    let e := d2FlowCandidateCapacityExponent d 3 15
    have he : 12 <= e := by dsimp [e, d2FlowCandidateCapacityExponent]; omega
    have hp : 2 ^ 12 * 2 ^ (e - 12) = 2 ^ e := by
      rw [← pow_add]
      congr 1
      omega
    change 4096 * (15 * 2 ^ (e - 12)) = 15 * 2 ^ e
    calc
      4096 * (15 * 2 ^ (e - 12)) = 15 * (2 ^ 12 * 2 ^ (e - 12)) := by ring
      _ = 15 * 2 ^ e := by rw [hp]
  rw [hscale] at h14
  nlinarith

/-- If the level-three root is within its scheduled sender cap and each of
eight children receives the fresh Stage-14 level-four quota, the resulting
child mass funds the Stage-15 level-three quota. This is the local allocation
interface; the actual parent-cut transfer must still supply its hypotheses. -/
theorem d2FlowCandidateStage15_levelThree_allocation_from_child_floor
    {d G : Nat} (hd : 14 <= d) (childDeficit : Fin 8 -> Nat)
    (hfloor : forall j, d2FlowCandidateQuota d 14 4 .mid <= childDeficit j)
    (hG : 512 * G <= d2FlowCandidateCapacity d 3 15) :
    d2FlowCandidateQuota d 15 3 .mid <= d2FlowTotal childDeficit - G := by
  have hsum : 8 * d2FlowCandidateQuota d 14 4 .mid <=
      d2FlowTotal childDeficit := by
    change 8 * d2FlowCandidateQuota d 14 4 .mid <=
      Finset.univ.sum childDeficit
    calc
      8 * d2FlowCandidateQuota d 14 4 .mid =
          Finset.univ.sum (fun _ : Fin 8 => d2FlowCandidateQuota d 14 4 .mid) := by simp
      _ <= Finset.univ.sum childDeficit := by
        apply Finset.sum_le_sum
        intro j hj
        exact hfloor j
  have hquotaScale := d2FlowCandidateCapacity_stage14_child_eq_32_stage15_parent
    (d := d) (i := 3) hd
  have hquota14 := d2FlowCandidateStage14_quota_exact_ratio
    (d := d) (i := 3) hd (r := .mid) (Or.inl rfl)
  rw [hquotaScale] at hquota14
  have hquotaRelation :=
    d2FlowCandidateStage14_levelFour_quota_eq_32_stage15_levelThree hd
  have hrate : 4096 * d2FlowCandidateQuota d 15 3 .mid =
      15 * d2FlowCandidateCapacity d 3 15 := by
    nlinarith [hquota14, hquotaRelation]
  have hGsmall : G <= d2FlowCandidateQuota d 15 3 .mid := by
    nlinarith [hG, hrate]
  have hmargin : d2FlowCandidateQuota d 15 3 .mid + G <=
      8 * d2FlowCandidateQuota d 14 4 .mid := by
    nlinarith [hquotaRelation, hGsmall]
  omega

/-- Each actual Stage-15 level-four root is produced by an active Stage-14
level-four sender and therefore receives that sender's quota. -/
theorem d2FlowCandidateRun_stage15_levelThree_child_quota
    (h : Nat) (hd : 14 <= h + 5) (j k m l : Fin 8) :
    d2FlowCandidateQuota (h + 5) 14 4 .mid <=
      d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowCandidateRun (h + 5)
                  (d2FlowTreeInitial 8192 (h + 5)) 15) j) k) m) l) := by
  rw [d2FlowCandidateRun_stage15_levelFour_root_eq_local h hd j k m l]
  have hroles := d2FlowCandidateStage14_reserve_sender_roles
    (d := h + 5) (by omega)
  let input := d2FlowTreeChild
    (d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowCandidateRun (h + 5)
            (d2FlowTreeInitial 8192 (h + 5)) 14) j) k) m) l
  cases hnode : input with
  | node G low high children =>
      change d2FlowCandidateQuota (h + 5) 14 4 .mid <=
        d2FlowTreeRootDeficit
          (d2FlowStage (d2FlowCandidateActive (h + 5) 14)
            (d2FlowCandidateRole (h + 5) 14)
            (d2FlowCandidateQuota (h + 5) 14) (h + 1) 4 input)
      rw [hnode, d2FlowStage_active_node_deficit children hroles.1]
      simp only [hroles.2.1]
      omega

attribute [local irreducible] d2FlowTreeRootDeficit

/-- The actual Stage-15 level-three sender satisfies its allocation field:
eight fresh level-four quotas cover the next quota and its root deficit. -/
theorem d2FlowCandidateRun_stage15_levelThree_allocation
    (childDepth : Nat) (hd : 7 <= childDepth) (j k m : Fin 8) :
    d2FlowCandidateQuota (childDepth + 7) 15 3 .mid <=
      d2FlowTotal (fun s =>
        d2FlowTreeRootDeficit
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild
                  (d2FlowCandidateRun (childDepth + 7)
                    (d2FlowTreeInitial 8192 (childDepth + 7)) 15) j) k) m) s)) -
      d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowCandidateRun (childDepth + 7)
                (d2FlowTreeInitial 8192 (childDepth + 7)) 15) j) k) m) := by
  have hrootCap := d2FlowCandidateRun_stage15_levelThree_root_cap
    childDepth hd j k m
  have hfloor : forall s : Fin 8,
      d2FlowCandidateQuota (childDepth + 7) 14 4 .mid <=
        d2FlowTreeRootDeficit
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild
                  (d2FlowCandidateRun (childDepth + 7)
                    (d2FlowTreeInitial 8192 (childDepth + 7)) 15) j) k) m) s) := by
    intro s
    have hs := d2FlowCandidateRun_stage15_levelThree_child_quota
      (childDepth + 2) (by omega) j k m s
    simpa [Nat.add_assoc] using hs
  exact d2FlowCandidateStage15_levelThree_allocation_from_child_floor
    (d := childDepth + 7) (by omega)
    (fun s => d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowCandidateRun (childDepth + 7)
                (d2FlowTreeInitial 8192 (childDepth + 7)) 15) j) k) m) s))
    hfloor hrootCap


end Chvatal.D2Reserve
