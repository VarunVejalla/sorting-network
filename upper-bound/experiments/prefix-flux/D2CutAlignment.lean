import D2ScheduleReserve

namespace Chvatal.D2Reserve

/-- Scheduled child boundaries and fronts on the 2048-grid yield cuts on that
same grid. The result is independent of the schedule's paired-front argument. -/
theorem d2_leftCut_dvd_2048
    {pos size left : Nat}
    (hpos : 2048 ∣ pos) (hsize : 2048 ∣ size)
    (hleft : 2048 ∣ left) :
    2048 ∣ d2LeftCut pos size left := by
  obtain ⟨p, rfl⟩ := hpos
  obtain ⟨s, rfl⟩ := hsize
  obtain ⟨l, rfl⟩ := hleft
  unfold d2LeftCut
  by_cases hend : 2048 * p + 2048 * s ≤ 2048 * l
  · rw [Nat.min_eq_left hend]
    omega
  · by_cases hleftEnd : 2048 * l ≤ 2048 * p + 2048 * s
    · rw [Nat.min_eq_right hleftEnd]
      by_cases hposLeft : 2048 * p ≤ 2048 * l
      · omega
      · omega
    · omega

/-- The symmetric right cut is also on the 2048-grid. -/
theorem d2_rightCut_dvd_2048
    {pos size right : Nat}
    (hpos : 2048 ∣ pos) (hsize : 2048 ∣ size)
    (hright : 2048 ∣ right) :
    2048 ∣ d2RightCut pos size right := by
  obtain ⟨p, rfl⟩ := hpos
  obtain ⟨s, rfl⟩ := hsize
  obtain ⟨r, rfl⟩ := hright
  unfold d2RightCut
  by_cases hmax : max (2048 * p) (2048 * r) ≤ 2048 * p + 2048 * s
  · by_cases hpr : 2048 * p ≤ 2048 * r
    · rw [max_eq_right hpr]
      omega
    · rw [max_eq_left (by omega : 2048 * r ≤ 2048 * p)]
      omega
  · omega

theorem d2_leftCut_dvd_4096
    {pos size left : Nat}
    (hpos : 4096 ∣ pos) (hsize : 4096 ∣ size)
    (hleft : 4096 ∣ left) :
    4096 ∣ d2LeftCut pos size left := by
  obtain ⟨p, rfl⟩ := hpos
  obtain ⟨s, rfl⟩ := hsize
  obtain ⟨l, rfl⟩ := hleft
  unfold d2LeftCut
  by_cases hend : 4096 * p + 4096 * s ≤ 4096 * l
  · rw [Nat.min_eq_left hend]
    omega
  · by_cases hleftEnd : 4096 * l ≤ 4096 * p + 4096 * s
    · rw [Nat.min_eq_right hleftEnd]
      by_cases hposLeft : 4096 * p ≤ 4096 * l
      · omega
      · omega
    · omega

theorem d2_rightCut_dvd_4096
    {pos size right : Nat}
    (hpos : 4096 ∣ pos) (hsize : 4096 ∣ size)
    (hright : 4096 ∣ right) :
    4096 ∣ d2RightCut pos size right := by
  obtain ⟨p, rfl⟩ := hpos
  obtain ⟨s, rfl⟩ := hsize
  obtain ⟨r, rfl⟩ := hright
  unfold d2RightCut
  by_cases hmax : max (4096 * p) (4096 * r) ≤ 4096 * p + 4096 * s
  · by_cases hpr : 4096 * p ≤ 4096 * r
    · rw [max_eq_right hpr]
      omega
    · rw [max_eq_left (by omega : 4096 * r ≤ 4096 * p)]
      omega
  · omega

/-- Two end cuts on the 2048-grid have a 4096-aligned sum when their residues
modulo 4096 agree. The scheduler-specific task is to prove that residue
agreement for the two cuts of each child. -/
theorem d2_cut_sum_dvd_of_equal_cut_residues
    {pos size left right : Nat}
    (hleft : 2048 ∣ d2LeftCut pos size left)
    (hright : 2048 ∣ d2RightCut pos size right)
    (hcuts : d2LeftCut pos size left % 4096 =
      d2RightCut pos size right % 4096) :
    4096 ∣ d2LeftCut pos size left + d2RightCut pos size right := by
  omega

/-- The coupled arithmetic invariant needed by the fixed row-major core:
native deficits and allocations stay on the 4096 grid, while boundary fronts
stay on the 2048 grid. -/
def d2FlowTileAligned : {h : Nat} → D2FlowTree h → Prop
  | 0, .leaf G low high =>
      4096 ∣ G ∧ 2048 ∣ low ∧ 2048 ∣ high
  | _ + 1, .node G low high children =>
      4096 ∣ G ∧ 2048 ∣ low ∧ 2048 ∣ high ∧
        ∀ j, d2FlowTileAligned (children j)

theorem d2FlowTileAligned_root_dvd {h : Nat} (tree : D2FlowTree h)
    (htree : d2FlowTileAligned tree) :
    4096 ∣ d2FlowTreeRootDeficit tree := by
  cases tree <;> simpa [d2FlowTileAligned, d2FlowTreeRootDeficit] using htree.1

theorem d2_dvd_sub_trunc {k a b : Nat}
    (ha : k ∣ a) (hb : k ∣ b) : k ∣ a - b := by
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨y, rfl⟩ := hb
  by_cases hyx : y ≤ x
  · refine ⟨x - y, ?_⟩
    rw [← Nat.mul_sub_left_distrib]
  · have hxy : x ≤ y := by omega
    have hmul : k * x ≤ k * y := Nat.mul_le_mul_left k hxy
    simp [Nat.sub_eq_zero_of_le hmul]

theorem d2FlowTotal_dvd {sizes : Fin 8 → Nat} {k : Nat}
    (hsizes : ∀ j, k ∣ sizes j) : k ∣ d2FlowTotal sizes := by
  unfold d2FlowTotal
  apply Finset.dvd_sum
  intro j hj
  exact hsizes j

theorem d2FlowPosition_dvd {sizes : Fin 8 → Nat} {k : Nat} (j : Fin 8)
    (hsizes : ∀ j, k ∣ sizes j) : k ∣ d2FlowPosition sizes j := by
  unfold d2FlowPosition
  apply Finset.dvd_sum
  intro i hi
  exact hsizes i

theorem d2FlowTileAligned_setRoot {h : Nat} (tree : D2FlowTree h)
    {G low high : Nat} (htree : d2FlowTileAligned tree)
    (hG : 4096 ∣ G) (hL : 2048 ∣ low) (hH : 2048 ∣ high) :
    d2FlowTileAligned (d2FlowTreeSetRoot tree G low high) := by
  cases tree with
  | leaf oldG oldLow oldHigh =>
      simpa [d2FlowTileAligned, d2FlowTreeSetRoot] using ⟨hG, hL, hH⟩
  | @node h oldG oldLow oldHigh children =>
      rcases htree with ⟨_, _, _, hchildren⟩
      simpa [d2FlowTileAligned, d2FlowTreeSetRoot] using
        (show 4096 ∣ G ∧ 2048 ∣ low ∧ 2048 ∣ high ∧
          ∀ j, d2FlowTileAligned (children j) from
          ⟨hG, hL, hH, hchildren⟩)

def d2OrdinaryRole (r : D2Role) : Prop :=
  r = .topRise ∨ r = .mid ∨ r = .botDesc

/-- An ordinary D2 sender writes 4096-aligned endpoint data to each child,
provided its own two fronts and all child blocks lie on that grid. -/
theorem d2FlowStage_ordinary_child_rootAligned
    {active : Nat → Bool} {role : Nat → D2Role}
    {quota : Nat → D2Role → Nat}
    {h i G low high : Nat} (children : Fin 8 → D2FlowTree h)
    (ha : active i = true)
    (hr : d2OrdinaryRole (role i))
    (hquota : 8192 ∣ quota i (role i))
    (hlow : 4096 ∣ low) (hhigh : 4096 ∣ high)
    (hchildren : ∀ j, d2FlowTileAligned (children j)) (j : Fin 8) :
    4096 ∣ (d2FlowTreeRootData
      (d2FlowTreeChild
        (d2FlowStage active role quota (h + 1) i
          (.node G low high children)) j)).1 ∧
    4096 ∣ (d2FlowTreeRootData
      (d2FlowTreeChild
        (d2FlowStage active role quota (h + 1) i
          (.node G low high children)) j)).2.1 ∧
    4096 ∣ (d2FlowTreeRootData
      (d2FlowTreeChild
        (d2FlowStage active role quota (h + 1) i
          (.node G low high children)) j)).2.2 := by
  let sizes : Fin 8 → Nat := fun k => d2FlowTreeRootDeficit (children k)
  have hsizes : ∀ k, 4096 ∣ sizes k := by
    intro k
    exact d2FlowTileAligned_root_dvd (children k) (hchildren k)
  have hpos : 4096 ∣ d2FlowPosition sizes j := d2FlowPosition_dvd j hsizes
  have htotal : 4096 ∣ d2FlowTotal sizes := d2FlowTotal_dvd hsizes
  obtain ⟨q, hq⟩ := hquota
  have hhalf : 4096 ∣ quota i (role i) / 2 := by
    refine ⟨q, ?_⟩
    rw [hq]
    omega
  have hleft : 4096 ∣ low + quota i (role i) / 2 := dvd_add hlow hhalf
  have hremain : 4096 ∣ quota i (role i) - quota i (role i) / 2 := by
    refine ⟨q, ?_⟩
    rw [hq]
    omega
  have hright : 4096 ∣ d2FlowTotal sizes - high - quota i (role i) / 2 := by
    apply d2_dvd_sub_trunc
    · exact d2_dvd_sub_trunc htotal hhigh
    · exact hhalf
  have hleftCut : 4096 ∣ d2LeftCut (d2FlowPosition sizes j) (sizes j)
      (low + quota i (role i) / 2) :=
    d2_leftCut_dvd_4096 hpos (hsizes j) hleft
  have hrightCut : 4096 ∣ d2RightCut (d2FlowPosition sizes j) (sizes j)
      (d2FlowTotal sizes - high - quota i (role i) / 2) :=
    d2_rightCut_dvd_4096 hpos (hsizes j) hright
  have hwrite :
      d2FlowTreeChild
        (d2FlowStage active role quota (h + 1) i
          (.node G low high children)) j =
        d2FlowTreeSetRoot
          (d2FlowStage active role quota h (i + 1) (children j))
          (d2FlowCutChild (d2FlowPosition sizes j) (sizes j)
            (low + quota i (role i) / 2)
            (d2FlowTotal sizes - high - quota i (role i) / 2)).1
          (d2FlowCutChild (d2FlowPosition sizes j) (sizes j)
            (low + quota i (role i) / 2)
            (d2FlowTotal sizes - high - quota i (role i) / 2)).2.1
          (d2FlowCutChild (d2FlowPosition sizes j) (sizes j)
            (low + quota i (role i) / 2)
            (d2FlowTotal sizes - high - quota i (role i) / 2)).2.2 := by
    rcases hr with htop | hmid | hbot
    · simp [d2FlowStage, d2FlowTreeChild, d2FlowTreeSetRoot, ha, htop,
        sizes, d2FlowCutChild]
    · simp [d2FlowStage, d2FlowTreeChild, d2FlowTreeSetRoot, ha, hmid,
        sizes, d2FlowCutChild]
    · simp [d2FlowStage, d2FlowTreeChild, d2FlowTreeSetRoot, ha, hbot,
        sizes, d2FlowCutChild]
  rw [hwrite, d2FlowTreeRootData_setRoot]
  simp only [d2FlowCutChild]
  exact ⟨dvd_add hleftCut hrightCut, hleftCut, hrightCut⟩

/-- The other non-exceptional parent case, `topDesc`, clears its child's root
data, so the same child-alignment conclusion is immediate. -/
theorem d2FlowStage_topDesc_child_rootAligned
    {active : Nat → Bool} {role : Nat → D2Role}
    {quota : Nat → D2Role → Nat}
    {h i G low high : Nat} (children : Fin 8 → D2FlowTree h)
    (ha : active i = true) (hr : role i = .topDesc) (j : Fin 8) :
    4096 ∣ (d2FlowTreeRootData
      (d2FlowTreeChild
        (d2FlowStage active role quota (h + 1) i
          (.node G low high children)) j)).1 ∧
    4096 ∣ (d2FlowTreeRootData
      (d2FlowTreeChild
        (d2FlowStage active role quota (h + 1) i
          (.node G low high children)) j)).2.1 ∧
    4096 ∣ (d2FlowTreeRootData
      (d2FlowTreeChild
        (d2FlowStage active role quota (h + 1) i
          (.node G low high children)) j)).2.2 := by
  have hwrite :
      d2FlowTreeChild
        (d2FlowStage active role quota (h + 1) i
          (.node G low high children)) j =
        d2FlowTreeSetRoot (d2FlowStage active role quota h (i + 1)
          (children j)) 0 0 0 := by
    simp [d2FlowStage, d2FlowTreeChild, ha, hr]
  rw [hwrite, d2FlowTreeRootData_setRoot]
  simp

/-- The actual frontier schedule supplies exactly the parent cases needed by
the local alignment lemmas: an active ordinary child has an active parent one
stage earlier, and that parent is either `topDesc` or an ordinary cut role.
In particular, the exceptional `botRise` parent is excluded. -/
theorem d2FlowCandidate_activeOrdinary_parent_cases
    {d t i : Nat} (ht : 3 ≤ t) (hi : 1 ≤ i)
    (ha : d2FlowCandidateActive d t i = true)
    (hr : d2OrdinaryRole (d2FlowCandidateRole d t i)) :
    d2FlowCandidateActive d (t - 1) (i - 1) = true ∧
      (d2FlowCandidateRole d (t - 1) (i - 1) = .topDesc ∨
       d2OrdinaryRole (d2FlowCandidateRole d (t - 1) (i - 1))) := by
  have ht0 : t ≠ 0 := by omega
  have ht1 : t ≠ 1 := by omega
  have hformula : 2 ≤ t ∧ t ≤ tfD2 d ∧ i % 2 = t % 2 ∧
      3 * i + 3 * d ≥ 2 * t + 11 ∧ 3 * i < t + 8 := by
    simpa only [d2FlowCandidateActive, if_neg ht0, if_neg ht1,
      decide_eq_true_eq] using ha
  have hactive : active d (tfD2 d) i t := by
    simpa only [active, if_neg ht1] using hformula
  have hroleEq : d2FlowCandidateRole d t i = d2ScheduleRole d i t := by
    simp only [d2FlowCandidateRole, if_neg ht0]
  have hnotTop : d2ScheduleRole d i t ≠ .topDesc := by
    intro htop
    have htop' : d2OrdinaryRole .topDesc := by
      simpa [hroleEq, htop] using hr
    simp [d2OrdinaryRole] at htop'
  have hcases := active_nonTop_parent_role_cases
    (d := d) (tf := tfD2 d) (i := i) (t := t) ht hi hactive hnotTop
  have hparent : d2FlowCandidateActive d (t - 1) (i - 1) = true := by
    have hp0 : t - 1 ≠ 0 := by omega
    have hp1 : t - 1 ≠ 1 := by omega
    simpa only [d2FlowCandidateActive, if_neg hp0, if_neg hp1,
      decide_eq_true_eq, active, if_neg hp1] using hcases.1
  have hparentRole : d2FlowCandidateRole d (t - 1) (i - 1) =
      d2ScheduleRole d (i - 1) (t - 1) := by
    simp only [d2FlowCandidateRole, if_neg (by omega : t - 1 ≠ 0)]
  rcases hcases.2 with htop | htopRise | hmid | hbotDesc
  · exact ⟨hparent, Or.inl (hparentRole.trans htop)⟩
  · exact ⟨hparent, Or.inr (Or.inl (hparentRole.trans htopRise))⟩
  · exact ⟨hparent, Or.inr (Or.inr (Or.inl (hparentRole.trans hmid)))⟩
  · exact ⟨hparent, Or.inr (Or.inr (Or.inr (hparentRole.trans hbotDesc)))⟩

/-- Startup exception for the parent classifier at stage two. The only active
ordinary node is the bottom boundary at level two; its stage-one parent is
the `topRise` sender at level one. -/
theorem d2FlowCandidate_activeOrdinary_parent_cases_stage2
    {d i : Nat} (hd : 7 ≤ d)
    (ha : d2FlowCandidateActive d 2 i = true)
    (hr : d2OrdinaryRole (d2FlowCandidateRole d 2 i)) :
    d2FlowCandidateActive d 1 (i - 1) = true ∧
      (d2FlowCandidateRole d 1 (i - 1) = .topDesc ∨
       d2OrdinaryRole (d2FlowCandidateRole d 1 (i - 1))) := by
  have hformula : 2 ≤ 2 ∧ 2 ≤ tfD2 d ∧ i % 2 = 0 ∧
      3 * i + 3 * d ≥ 15 ∧ 3 * i < 10 := by
    simpa only [d2FlowCandidateActive,
      if_neg (by decide : ¬ (2 : Nat) = 0),
      if_neg (by decide : ¬ (2 : Nat) = 1), decide_eq_true_eq] using ha
  have hi : i = 0 ∨ i = 2 := by rcases hformula with ⟨_, _, hp, _, hu⟩; omega
  have hA1 : alpha d 1 = 1 := by simp [alpha]
  have hA2 : alpha d 2 = 0 := by
    have hd15 : 15 ≤ 3 * d := by omega
    simp [alpha, alphaStar, ceilParity, hd15]
  have hA3 : alpha d 3 = 1 := by
    have hd17 : 17 ≤ 3 * d := by omega
    simp [alpha, alphaStar, ceilParity, hd17]
  rcases hi with hzero | htwo
  · subst i
    have hrole0 : d2FlowCandidateRole d 2 0 = .topDesc := by
      simp [d2FlowCandidateRole, d2ScheduleRole, hA2, hA3]
    have hfalse := hr
    rw [hrole0] at hfalse
    simp [d2OrdinaryRole] at hfalse
  · subst i
    have hparent : d2FlowCandidateActive d 1 1 = true := by
      simp [d2FlowCandidateActive]
    have hparentRole : d2FlowCandidateRole d 1 1 = .topRise := by
      simp [d2FlowCandidateRole, d2ScheduleRole, hA1, hA2]
    exact ⟨hparent, Or.inr (by rw [hparentRole]; simp [d2OrdinaryRole])⟩

/-- Parent classification for every transition into an active ordinary child,
including the one-stage startup exception. -/
theorem d2FlowCandidate_activeOrdinary_parent_cases_succ
    {d t i : Nat} (hd : 7 ≤ d) (ht : 2 ≤ t + 1)
    (ha : d2FlowCandidateActive d (t + 1) (i + 1) = true)
    (hr : d2OrdinaryRole (d2FlowCandidateRole d (t + 1) (i + 1))) :
    d2FlowCandidateActive d t i = true ∧
      (d2FlowCandidateRole d t i = .topDesc ∨
       d2OrdinaryRole (d2FlowCandidateRole d t i)) := by
  by_cases htOne : t = 1
  · subst t
    simpa using d2FlowCandidate_activeOrdinary_parent_cases_stage2 hd ha hr
  · have hregular := d2FlowCandidate_activeOrdinary_parent_cases
      (d := d) (t := t + 1) (i := i + 1) (by omega) (by omega) ha hr
    simpa using hregular

theorem d2_pow_dvd_8192 {n : Nat} (hn : 13 ≤ n) : 8192 ∣ 2 ^ n := by
  refine ⟨2 ^ (n - 13), ?_⟩
  rw [show n = 13 + (n - 13) by omega, pow_add]
  norm_num

theorem d2_fifteen_pow_dvd_8192 {n : Nat} (hn : 13 ≤ n) :
    8192 ∣ 15 * 2 ^ n := by
  refine ⟨15 * 2 ^ (n - 13), ?_⟩
  rw [show n = 13 + (n - 13) by omega, pow_add]
  norm_num
  ring

theorem d2Omega_ge_linear {t : Nat} (ht : 2 ≤ t) : t + 2 ≤ 3 * omega t := by
  have ht0 : t ≠ 0 := by omega
  have ht1 : t ≠ 1 := by omega
  simp only [omega, if_neg ht0, if_neg ht1]
  unfold ceilParity
  split_ifs <;> omega

theorem d2_dvd_4096_to_2048 {n : Nat} (h : 4096 ∣ n) : 2048 ∣ n := by
  obtain ⟨k, rfl⟩ := h
  exact ⟨2 * k, by omega⟩

theorem d2_dvd_8192_to_4096 {n : Nat} (h : 8192 ∣ n) : 4096 ∣ n := by
  obtain ⟨k, rfl⟩ := h
  exact ⟨2 * k, by omega⟩

theorem d2_dvd_half_of_dvd_4096 {n : Nat} (h : 4096 ∣ n) :
    2048 ∣ n / 2 := by
  obtain ⟨k, rfl⟩ := h
  refine ⟨k, ?_⟩
  omega

theorem d2_dvd_sub_half_of_dvd_4096 {n : Nat} (h : 4096 ∣ n) :
    2048 ∣ n - n / 2 := by
  obtain ⟨k, rfl⟩ := h
  refine ⟨k, ?_⟩
  omega

/-- Exact local hypotheses under which the recursive D2 update preserves the
coupled tile-address invariant. Ordinary quotas lie on the 4096-grid, while
their two fronts lie on that same grid. -/
def d2FlowStageTileContract (active : Nat → Bool) (role : Nat → D2Role)
    (quota : Nat → D2Role → Nat) : {h : Nat} → Nat → D2FlowTree h → Prop
  | 0, _, .leaf _ _ _ => True
  | h + 1, i, .node _ low high children =>
      (∀ j, d2FlowStageTileContract active role quota (h := h)
        (i + 1) (children j)) ∧
      (active i = true → d2OrdinaryRole (role i) →
        4096 ∣ quota i (role i)) ∧
      (active i = true → d2OrdinaryRole (role i) →
        let sizes : Fin 8 → Nat := fun j => d2FlowTreeRootDeficit (children j)
        let half := quota i (role i) / 2
        let left := low + half
        let right := d2FlowTotal sizes - high - half
        4096 ∣ left ∧ 4096 ∣ right)

/-- The scheduler-only part of the stage contract. Ordinary quota divisibility
is proved separately from the candidate's closed-form schedule. -/
def d2FlowStageFrontContract (active : Nat → Bool) (role : Nat → D2Role)
    (quota : Nat → D2Role → Nat) : {h : Nat} → Nat → D2FlowTree h → Prop
  | 0, _, .leaf _ _ _ => True
  | h + 1, i, .node _ low high children =>
      (∀ j, d2FlowStageFrontContract active role quota (h := h)
        (i + 1) (children j)) ∧
      (active i = true → d2OrdinaryRole (role i) →
        let sizes : Fin 8 → Nat := fun j => d2FlowTreeRootDeficit (children j)
        let half := quota i (role i) / 2
        let left := low + half
        let right := d2FlowTotal sizes - high - half
        4096 ∣ left ∧ 4096 ∣ right)

/-- Role-sensitive endpoint invariant: before a stage, every sender that is
active with an ordinary role has both stored end deficits on the 4096-grid. -/
def d2FlowStageOrdinaryEndpointsAligned (active : Nat → Bool)
    (role : Nat → D2Role) : {h : Nat} → Nat → D2FlowTree h → Prop
  | 0, i, .leaf _ low high =>
      active i = true → d2OrdinaryRole (role i) →
        4096 ∣ low ∧ 4096 ∣ high
  | h + 1, i, .node _ low high children =>
      (active i = true → d2OrdinaryRole (role i) →
        4096 ∣ low ∧ 4096 ∣ high) ∧
      ∀ j, d2FlowStageOrdinaryEndpointsAligned active role
        (h := h) (i + 1) (children j)

/-- Endpoint alignment for all proper descendants, leaving the current root
to be supplied separately by its parent. This matches the D2 update order:
descendants step first, then the parent overwrites its immediate child roots. -/
def d2FlowStageDescEndpointsAligned (active : Nat → Bool)
    (role : Nat → D2Role) : {h : Nat} → Nat → D2FlowTree h → Prop
  | 0, _, .leaf _ _ _ => True
  | h + 1, i, .node _ _ _ children =>
      ∀ j,
        (active (i + 1) = true → d2OrdinaryRole (role (i + 1)) →
          4096 ∣ (d2FlowTreeRootData (children j)).2.1 ∧
          4096 ∣ (d2FlowTreeRootData (children j)).2.2) ∧
        d2FlowStageDescEndpointsAligned active role
          (h := h) (i + 1) (children j)

theorem d2FlowStageDescEndpointsAligned_setRoot
    {active : Nat → Bool} {role : Nat → D2Role} {h i : Nat}
    (tree : D2FlowTree h)
    (hdesc : d2FlowStageDescEndpointsAligned active role i tree)
    (G low high : Nat) :
    d2FlowStageDescEndpointsAligned active role i
      (d2FlowTreeSetRoot tree G low high) := by
  cases tree with
  | leaf oldG oldLow oldHigh => exact True.intro
  | node oldG oldLow oldHigh children =>
      simpa [d2FlowStageDescEndpointsAligned, d2FlowTreeSetRoot] using hdesc

/-- If no sender at or below the current level is active, the recursive
stage leaves the entire subtree unchanged. -/
theorem d2FlowStage_eq_self_of_inactive
    {active : Nat → Bool} {role : Nat → D2Role}
    {quota : Nat → D2Role → Nat} {h : Nat} (i : Nat)
    (tree : D2FlowTree h)
    (hinactive : ∀ k, i ≤ k → active k = false) :
    d2FlowStage active role quota h i tree = tree := by
  induction h generalizing i with
  | zero => cases tree; rfl
  | succ h ih =>
      cases tree with
      | node G low high children =>
          simp only [d2FlowStage]
          rw [hinactive i (by omega)]
          simp
          funext j
          exact ih (i + 1) (children j) (by
            intro k hk
            exact hinactive k (by omega))

/-- The proper-descendant condition is automatic below a level from which
onward the schedule has no active senders. -/
theorem d2FlowStageDescEndpointsAligned_of_inactive_after
    {active : Nat → Bool} {role : Nat → D2Role} {h i : Nat}
    (tree : D2FlowTree h)
    (hinactive : ∀ k, i < k → active k = false) :
    d2FlowStageDescEndpointsAligned active role i tree := by
  induction h generalizing i with
  | zero => cases tree; exact True.intro
  | succ h ih =>
      cases tree with
      | node G low high children =>
          change ∀ j, _
          intro j
          constructor
          · intro ha _
            have hfalse : active (i + 1) = false := hinactive (i + 1) (by omega)
            rw [hfalse] at ha
            cases ha
          · exact ih (i := i + 1) (tree := children j) (by
              intro k hk
              exact hinactive k (by omega))

/-- The bootstrap stage is an explicit top-descendant reset: it leaves the
root counters unchanged and zeros the endpoint counters at each child. -/
theorem d2FlowCandidateStage_zero_initial_shape (h : Nat) :
    d2FlowCandidateStage (h + 1) 0
      (d2FlowTreeInitial 8192 (h + 1)) =
    .node 0 0 0 (fun _ =>
      d2FlowTreeSetRoot (d2FlowTreeFull 8192 h) 0 0 0) := by
  have hinactive : ∀ k, 1 ≤ k →
      d2FlowCandidateActive (h + 1) 0 k = false := by
    intro k hk
    simp [d2FlowCandidateActive]
    omega
  have hchild : ∀ j : Fin 8,
      d2FlowStage (d2FlowCandidateActive (h + 1) 0)
        (d2FlowCandidateRole (h + 1) 0)
        (d2FlowCandidateQuota (h + 1) 0) h 1
        (d2FlowTreeFull 8192 h) = d2FlowTreeFull 8192 h := by
    intro j
    exact d2FlowStage_eq_self_of_inactive 1 (d2FlowTreeFull 8192 h)
      (fun k hk => hinactive k (by omega))
  have hchild' := hchild 0
  simp [d2FlowCandidateStage, d2FlowCandidateActive,
    d2FlowCandidateRole, d2FlowTreeInitial, d2FlowStage, hchild']

/-- Stage zero has no ordinary sender, so its front contract is automatic on
every finite tree. -/
theorem d2FlowCandidate_stage0_frontContract {d h : Nat} (i : Nat)
    (tree : D2FlowTree h) :
    d2FlowStageFrontContract
      (fun j => d2FlowCandidateActive d 0 j)
      (fun j => d2FlowCandidateRole d 0 j)
      (d2FlowCandidateQuota d 0) i tree := by
  induction h generalizing i with
  | zero => cases tree; simp [d2FlowStageFrontContract]
  | succ h ih =>
      cases tree with
      | node G low high children =>
          change (∀ j, _) ∧ _
          constructor
          · intro j
            exact ih (i + 1) (children j)
          · intro _ hr
            simp [d2FlowCandidateRole, d2OrdinaryRole] at hr

/-- Root endpoint information together with the proper-descendant invariant
is exactly the full role-sensitive ordinary-endpoint invariant. -/
theorem d2FlowStageDescEndpointsAligned_to_ordinaryEndpoints
    {active : Nat → Bool} {role : Nat → D2Role} {h i : Nat}
    (tree : D2FlowTree h)
    (hroot : active i = true → d2OrdinaryRole (role i) →
      4096 ∣ (d2FlowTreeRootData tree).2.1 ∧
      4096 ∣ (d2FlowTreeRootData tree).2.2)
    (hdesc : d2FlowStageDescEndpointsAligned active role i tree) :
    d2FlowStageOrdinaryEndpointsAligned active role i tree := by
  induction h generalizing i with
  | zero =>
      cases tree
      exact hroot
  | succ h ih =>
      cases tree with
      | node G low high children =>
          change (active i = true → d2OrdinaryRole (role i) →
            4096 ∣ low ∧ 4096 ∣ high) ∧
            ∀ j, d2FlowStageOrdinaryEndpointsAligned active role
              (i + 1) (children j)
          change ∀ j, _ at hdesc
          refine ⟨?_, ?_⟩
          · intro ha hr
            exact hroot ha hr
          · intro j
            rcases hdesc j with ⟨hchildRoot, hchildDesc⟩
            exact ih (i := i + 1) (children j)
              (fun ha hr => hchildRoot ha hr) hchildDesc

/-- Conditional all-depth transfer theorem for scheduler-to-tile alignment.
The remaining scheduler input is the role-specific 4096-alignment of the
ordinary fronts, screened above but not yet proved for every stage. -/
theorem d2FlowStage_preserves_tileAligned
    {active : Nat → Bool} {role : Nat → D2Role}
    {quota : Nat → D2Role → Nat}
    {h : Nat} (i : Nat) (tree : D2FlowTree h)
    (hcontract : d2FlowStageTileContract active role quota (h := h) i tree) :
      d2FlowTileAligned tree →
      d2FlowTileAligned (d2FlowStage active role quota h i tree) := by
  induction h generalizing i with
  | zero =>
      intro ht
      cases tree with
      | leaf G low high =>
          simpa [d2FlowTileAligned, d2FlowStage] using ht
  | succ h ih =>
      intro ht
      cases tree with
      | node G low high children =>
          rcases ht with ⟨hG, hLow, hHigh, hchildren⟩
          rcases hcontract with ⟨hchildrenContract, hquotaContract,
            hpairedContract⟩
          have hstepped : ∀ j,
              d2FlowTileAligned
                (d2FlowStage active role quota h (i + 1) (children j)) := by
            intro j
            exact ih (i + 1) (children j) (hchildrenContract j) (hchildren j)
          cases ha : active i with
          | false =>
              simpa [d2FlowStage, ha, d2FlowTileAligned] using
                (show 4096 ∣ G ∧ 2048 ∣ low ∧ 2048 ∣ high ∧
                  ∀ j, d2FlowTileAligned
                    (d2FlowStage active role quota h (i + 1) (children j))
                  from ⟨hG, hLow, hHigh, hstepped⟩)
          | true =>
              cases hr : role i with
              | topDesc =>
                  have hzero : 4096 ∣ (0 : Nat) := dvd_zero 4096
                  have hzlow : 2048 ∣ (0 : Nat) := dvd_zero 2048
                  have hnewChildren : ∀ j,
                      d2FlowTileAligned
                        (d2FlowTreeSetRoot
                          (d2FlowStage active role quota h (i + 1) (children j))
                          0 0 0) := by
                    intro j
                    exact d2FlowTileAligned_setRoot _ (hstepped j)
                      hzero hzlow hzlow
                  simpa [d2FlowStage, ha, hr, d2FlowTileAligned] using
                    (show 4096 ∣ G ∧ 2048 ∣ low ∧ 2048 ∣ high ∧
                      ∀ j, d2FlowTileAligned
                        (d2FlowTreeSetRoot
                          (d2FlowStage active role quota h (i + 1) (children j))
                          0 0 0)
                      from ⟨hG, hLow, hHigh, hnewChildren⟩)
              | botRise =>
                  let sizes : Fin 8 → Nat := fun j =>
                    d2FlowTreeRootDeficit (children j)
                  have hsizes : ∀ j, 4096 ∣ sizes j := by
                    intro j
                    exact d2FlowTileAligned_root_dvd (children j) (hchildren j)
                  have htotal : 4096 ∣ d2FlowTotal sizes :=
                    d2FlowTotal_dvd hsizes
                  have halloc : 4096 ∣ d2FlowTotal sizes - G :=
                    d2_dvd_sub_trunc htotal hG
                  have hhalf : 2048 ∣ (d2FlowTotal sizes - G) / 2 :=
                    d2_dvd_half_of_dvd_4096 halloc
                  have hremain : 2048 ∣
                      (d2FlowTotal sizes - G) - (d2FlowTotal sizes - G) / 2 :=
                    d2_dvd_sub_half_of_dvd_4096 halloc
                  have hnewLow : 2048 ∣ low + (d2FlowTotal sizes - G) / 2 :=
                    dvd_add hLow hhalf
                  have hnewHigh : 2048 ∣
                      high + (d2FlowTotal sizes - G) -
                        (d2FlowTotal sizes - G) / 2 :=
                    by
                      have hh := dvd_add hHigh hremain
                      convert hh using 1
                      omega
                  have hnewRoot : 4096 ∣ G + (d2FlowTotal sizes - G) :=
                    dvd_add hG halloc
                  simpa [d2FlowStage, ha, hr, d2FlowTileAligned, sizes] using
                    (show 4096 ∣ G + (d2FlowTotal sizes - G) ∧
                      2048 ∣ low + (d2FlowTotal sizes - G) / 2 ∧
                      2048 ∣ high + (d2FlowTotal sizes - G) -
                        (d2FlowTotal sizes - G) / 2 ∧
                      ∀ j, d2FlowTileAligned
                        (d2FlowStage active role quota h (i + 1) (children j))
                      from ⟨hnewRoot, hnewLow, hnewHigh, hstepped⟩)
              | topRise | mid | botDesc =>
                  have hrole : d2OrdinaryRole (role i) := by
                    simp [d2OrdinaryRole, hr]
                  have hquota : 4096 ∣ quota i (role i) :=
                    hquotaContract ha hrole
                  have hhalf : 2048 ∣ quota i (role i) / 2 :=
                    d2_dvd_half_of_dvd_4096 hquota
                  have hremain : 2048 ∣
                      quota i (role i) - quota i (role i) / 2 :=
                    d2_dvd_sub_half_of_dvd_4096 hquota
                  have hnewLow : 2048 ∣ low + quota i (role i) / 2 :=
                    dvd_add hLow hhalf
                  have hnewHigh : 2048 ∣
                      high + quota i (role i) - quota i (role i) / 2 :=
                    by
                      have hh := dvd_add hHigh hremain
                      convert hh using 1
                      omega
                  let sizes : Fin 8 → Nat := fun j =>
                    d2FlowTreeRootDeficit (children j)
                  have hsizes : ∀ j, 4096 ∣ sizes j := by
                    intro j
                    exact d2FlowTileAligned_root_dvd (children j) (hchildren j)
                  have hpos : ∀ j, 4096 ∣ d2FlowPosition sizes j := by
                    intro j
                    exact d2FlowPosition_dvd j hsizes
                  have hsize : ∀ j, 4096 ∣ sizes j := hsizes
                  have htotal : 4096 ∣ d2FlowTotal sizes :=
                    d2FlowTotal_dvd hsizes
                  rcases hpairedContract ha hrole with ⟨hleft, hright⟩
                  have hchildAligned : ∀ j,
                      d2FlowTileAligned
                        (d2FlowTreeSetRoot
                          (d2FlowStage active role quota h (i + 1) (children j))
                          (d2LeftCut (d2FlowPosition sizes j) (sizes j)
                              (low + quota i (role i) / 2) +
                            d2RightCut (d2FlowPosition sizes j) (sizes j)
                              (d2FlowTotal sizes - high - quota i (role i) / 2))
                          (d2LeftCut (d2FlowPosition sizes j) (sizes j)
                            (low + quota i (role i) / 2))
                          (d2RightCut (d2FlowPosition sizes j) (sizes j)
                            (d2FlowTotal sizes - high - quota i (role i) / 2))) := by
                    intro j
                    have hleftCut : 4096 ∣
                        d2LeftCut (d2FlowPosition sizes j) (sizes j)
                          (low + quota i (role i) / 2) :=
                      d2_leftCut_dvd_4096 (hpos j) (hsize j) hleft
                    have hrightCut : 4096 ∣
                        d2RightCut (d2FlowPosition sizes j) (sizes j)
                          (d2FlowTotal sizes - high - quota i (role i) / 2) :=
                      d2_rightCut_dvd_4096 (hpos j) (hsize j) hright
                    have hnewG : 4096 ∣
                        d2LeftCut (d2FlowPosition sizes j) (sizes j)
                            (low + quota i (role i) / 2) +
                          d2RightCut (d2FlowPosition sizes j) (sizes j)
                            (d2FlowTotal sizes - high - quota i (role i) / 2) :=
                      dvd_add hleftCut hrightCut
                    exact d2FlowTileAligned_setRoot
                      (d2FlowStage active role quota h (i + 1) (children j))
                      (hstepped j) hnewG
                      (d2_dvd_4096_to_2048 hleftCut)
                      (d2_dvd_4096_to_2048 hrightCut)
                  have hright : 2048 ∣
                      d2FlowTotal sizes - high - quota i (role i) / 2 := by
                    apply d2_dvd_sub_trunc
                    · exact d2_dvd_sub_trunc
                        (d2_dvd_4096_to_2048 htotal) hHigh
                    · exact hhalf
                  have hnewRoot : 4096 ∣ G + quota i (role i) :=
                    dvd_add hG hquota
                  simpa [d2FlowStage, ha, hr, d2FlowTileAligned, sizes,
                    d2FlowCutChild] using
                    (show 4096 ∣ G + quota i (role i) ∧
                      2048 ∣ low + quota i (role i) / 2 ∧
                      2048 ∣ high + quota i (role i) -
                        quota i (role i) / 2 ∧
                      ∀ j, d2FlowTileAligned
                        (d2FlowTreeSetRoot
                          (d2FlowStage active role quota h (i + 1) (children j))
                          (d2LeftCut (d2FlowPosition sizes j) (sizes j)
                              (low + quota i (role i) / 2) +
                            d2RightCut (d2FlowPosition sizes j) (sizes j)
                              (d2FlowTotal sizes - high - quota i (role i) / 2))
                          (d2LeftCut (d2FlowPosition sizes j) (sizes j)
                            (low + quota i (role i) / 2))
                          (d2RightCut (d2FlowPosition sizes j) (sizes j)
                            (d2FlowTotal sizes - high - quota i (role i) / 2)))
                      from ⟨hnewRoot, hnewLow, hnewHigh, hchildAligned⟩)

/-- Any full initial state whose base scale is 4096-divisible satisfies the
coupled alignment invariant at every finite tree depth. -/
theorem d2FlowTreeFull_tileAligned (scale h : Nat) (hscale : 4096 ∣ scale) :
    d2FlowTileAligned (d2FlowTreeFull scale h) := by
  induction h with
  | zero => simpa [d2FlowTreeFull, d2FlowTileAligned] using hscale
  | succ h ih =>
      simp only [d2FlowTreeFull, d2FlowTileAligned]
      refine ⟨?_, dvd_zero _, dvd_zero _, ?_⟩
      · obtain ⟨k, hk⟩ := hscale
        refine ⟨k * 8 ^ (h + 1), ?_⟩
        rw [hk]
        ring
      · intro j
        exact ih

/-- The candidate's zero-deficit root with full scale-8192 subtrees starts
inside the coupled tile-alignment invariant. -/
theorem d2FlowTreeInitial_tileAligned (scale depth : Nat)
    (hscale : 4096 ∣ scale) :
    d2FlowTileAligned (d2FlowTreeInitial scale depth) := by
  cases depth with
  | zero => simp [d2FlowTreeInitial, d2FlowTileAligned]
  | succ h =>
      simp only [d2FlowTreeInitial, d2FlowTileAligned]
      refine ⟨dvd_zero _, dvd_zero _, dvd_zero _, ?_⟩
      intro j
      exact d2FlowTreeFull_tileAligned scale h hscale

/-- If every candidate stage satisfies the explicit quota and front-alignment
contract, the actual all-depth run keeps every recursive bag row-aligned. -/
theorem d2FlowCandidateRun_tileAligned_of_contracts {d : Nat}
    (hcontracts : ∀ t,
      d2FlowStageTileContract
        (fun i => d2FlowCandidateActive d t i)
        (fun i => d2FlowCandidateRole d t i)
        (d2FlowCandidateQuota d t) (h := d) 0
        (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) t)) :
    ∀ t, d2FlowTileAligned (d2FlowCandidateRun d
      (d2FlowTreeInitial 8192 d) t) := by
  intro t
  induction t with
  | zero => exact d2FlowTreeInitial_tileAligned 8192 d ⟨2, rfl⟩
  | succ t ih =>
      simpa [d2FlowCandidateRun, d2FlowCandidateStage] using
        (d2FlowStage_preserves_tileAligned 0
          (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) t)
          (hcontracts t) ih)

/-- Every active ordinary quota in the `(8,8,1/4)` candidate is divisible by
8192 once the active role is used. The role-sensitive exponent bounds are
stronger than the uniform active-capacity bound. -/
theorem d2FlowCandidateQuota_dvd_8192 {d t i : Nat}
    (hd : 7 ≤ d) (ht : 0 < t)
    (ha : d2FlowCandidateActive d t i = true)
    (hr : d2OrdinaryRole (d2FlowCandidateRole d t i)) :
    8192 ∣ d2FlowCandidateQuota d t i (d2FlowCandidateRole d t i) := by
  have hroleEq : d2FlowCandidateRole d t i = d2ScheduleRole d i t := by
    simp [d2FlowCandidateRole, Nat.ne_of_gt ht]
  have hr' : d2OrdinaryRole (d2ScheduleRole d i t) := by
    simpa [hroleEq] using hr
  rcases hr' with htop | hmid | hbot
  · by_cases htOne : t = 1
    · have hi : i = 1 := by
        simpa [d2FlowCandidateActive, htOne] using ha
      have hexp : 25 ≤ d2FlowCandidateCapacityExponent d i t := by
        simp [d2FlowCandidateCapacityExponent, htOne, hi]
        omega
      have hq : d2FlowCandidateQuota d t i (d2FlowCandidateRole d t i) =
          2 ^ (d2FlowCandidateCapacityExponent d i t - 8) := by
        simp [d2FlowCandidateQuota, hroleEq, htop]
      rw [hq]
      apply d2_pow_dvd_8192
      omega
    · have htge : 2 ≤ t := by omega
      have hformula : 2 ≤ t ∧ t ≤ tfD2 d ∧ i % 2 = t % 2 ∧
          3 * i + 3 * d ≥ 2 * t + 11 ∧ 3 * i < t + 8 := by
        have ht0 : t ≠ 0 := by omega
        simpa only [d2FlowCandidateActive, if_neg ht0, if_neg htOne,
          decide_eq_true_eq] using ha
      rcases hformula with ⟨_, htf, hpar, hlow, _⟩
      have heqNot : 3 * i + 3 * d ≠ 2 * t + 11 := by
        intro heq
        have hb := lower_boundary_is_topDesc htge hpar heq
        have hforced : d2ScheduleRole d i t = .topDesc := by
          simp [d2ScheduleRole, hb.1, hb.2]
        rw [htop] at hforced
        cases hforced
      have hexp : 21 ≤ d2FlowCandidateCapacityExponent d i t := by
        unfold d2FlowCandidateCapacityExponent
        omega
      have hq : d2FlowCandidateQuota d t i (d2FlowCandidateRole d t i) =
          2 ^ (d2FlowCandidateCapacityExponent d i t - 8) := by
        simp [d2FlowCandidateQuota, hroleEq, htop]
      rw [hq]
      apply d2_pow_dvd_8192
      omega
  · by_cases htOne : t = 1
    · have hi : i = 1 := by
        simpa [d2FlowCandidateActive, htOne] using ha
      have hexp : 25 ≤ d2FlowCandidateCapacityExponent d i t := by
        simp [d2FlowCandidateCapacityExponent, htOne, hi]
        omega
      have hq : d2FlowCandidateQuota d t i (d2FlowCandidateRole d t i) =
          15 * 2 ^ (d2FlowCandidateCapacityExponent d i t - 12) := by
        simp [d2FlowCandidateQuota, hroleEq, hmid]
      rw [hq]
      apply d2_fifteen_pow_dvd_8192
      omega
    · have htge : 2 ≤ t := by omega
      have hformula : 2 ≤ t ∧ t ≤ tfD2 d ∧ i % 2 = t % 2 ∧
          3 * i + 3 * d ≥ 2 * t + 11 ∧ 3 * i < t + 8 := by
        have ht0 : t ≠ 0 := by omega
        simpa only [d2FlowCandidateActive, if_neg ht0, if_neg htOne,
          decide_eq_true_eq] using ha
      rcases hformula with ⟨_, _, hpar, hlow, _⟩
      have hnotAlpha : i ≠ alpha d t := by
        intro heq
        subst i
        by_cases hm : alpha d t < alpha d (t + 1)
        · simp [d2ScheduleRole, hm] at hmid
        · simp [d2ScheduleRole, hm] at hmid
      have halpha : alpha d t ≤ i :=
        (alpha_le_iff_threshold htge hpar).2 (by omega)
      have hgap : alpha d t + 2 ≤ i := by
        have hAlphaPar := alpha_parity d t
        omega
      have hshiftPar : (i - 2) % 2 = t % 2 := by omega
      have hshiftLe : alpha d t ≤ i - 2 := by omega
      have hshift := (alpha_le_iff_threshold htge hshiftPar).1 hshiftLe
      have hexp : 25 ≤ d2FlowCandidateCapacityExponent d i t := by
        unfold d2FlowCandidateCapacityExponent
        omega
      have hq : d2FlowCandidateQuota d t i (d2FlowCandidateRole d t i) =
          15 * 2 ^ (d2FlowCandidateCapacityExponent d i t - 12) := by
        simp [d2FlowCandidateQuota, hroleEq, hmid]
      rw [hq]
      apply d2_fifteen_pow_dvd_8192
      omega
  · by_cases htOne : t = 1
    · have hi : i = 1 := by
        simpa [d2FlowCandidateActive, htOne] using ha
      have hexp : 25 ≤ d2FlowCandidateCapacityExponent d i t := by
        simp [d2FlowCandidateCapacityExponent, htOne, hi]
        omega
      have hq : d2FlowCandidateQuota d t i (d2FlowCandidateRole d t i) =
          15 * 2 ^ (d2FlowCandidateCapacityExponent d i t - 12) := by
        simp [d2FlowCandidateQuota, hroleEq, hbot]
      rw [hq]
      apply d2_fifteen_pow_dvd_8192
      omega
    · have htge : 2 ≤ t := by omega
      have hformula : 2 ≤ t ∧ t ≤ tfD2 d ∧ i % 2 = t % 2 ∧
          3 * i + 3 * d ≥ 2 * t + 11 ∧ 3 * i < t + 8 := by
        have ht0 : t ≠ 0 := by omega
        simpa only [d2FlowCandidateActive, if_neg ht0, if_neg htOne,
          decide_eq_true_eq] using ha
      rcases hformula with ⟨_, htf, _, _, _⟩
      have hiOmega : i = omega t := by
        by_cases hiAlpha : i = alpha d t
        · by_cases hm : alpha d t < alpha d (t + 1)
          · simp [d2ScheduleRole, hiAlpha, hm] at hbot
          · simp [d2ScheduleRole, hiAlpha, hm] at hbot
        · by_cases hiOmega : i = omega t
          · exact hiOmega
          · simp [d2ScheduleRole, hiAlpha, hiOmega] at hbot
      have hOmega := d2Omega_ge_linear htge
      have hexp : 25 ≤ d2FlowCandidateCapacityExponent d i t := by
        unfold d2FlowCandidateCapacityExponent tfD2 at *
        omega
      have hq : d2FlowCandidateQuota d t i (d2FlowCandidateRole d t i) =
          15 * 2 ^ (d2FlowCandidateCapacityExponent d i t - 12) := by
        simp [d2FlowCandidateQuota, hroleEq, hbot]
      rw [hq]
      apply d2_fifteen_pow_dvd_8192
      omega

/-- The root frontier can never be a `botRise` sender in this candidate
schedule; that exceptional boundary is always at positive level. -/
theorem d2FlowCandidate_root_not_botRise {d t : Nat}
    (ha : d2FlowCandidateActive d t 0 = true) :
    d2FlowCandidateRole d t 0 ≠ .botRise := by
  cases t with
  | zero => simp [d2FlowCandidateRole]
  | succ t =>
      by_cases ht : t + 1 = 1
      · have ht0 : t = 0 := by omega
        subst t
        simp [d2FlowCandidateActive] at ha
      · have htge : 2 ≤ t + 1 := by omega
        have hrole : d2FlowCandidateRole d (t + 1) 0 =
            d2ScheduleRole d 0 (t + 1) := by
          simp [d2FlowCandidateRole]
        intro hbot
        have hboundary := d2ScheduleRole_botRise_boundary htge
          (hrole.symm.trans hbot)
        omega

/-- The root's endpoint residues persist through every candidate stage. This
separates the root base case from the parent-driven descendant invariant. -/
theorem d2FlowCandidateStage_preserves_rootEndpointsAligned
    {d t depth : Nat} (hd : 7 ≤ d) (hdepth : 1 ≤ depth)
    (tree : D2FlowTree depth)
    (hroot : 4096 ∣ (d2FlowTreeRootData tree).2.1 ∧
      4096 ∣ (d2FlowTreeRootData tree).2.2) :
    4096 ∣ (d2FlowTreeRootData
      (d2FlowStage (fun i => d2FlowCandidateActive d t i)
        (fun i => d2FlowCandidateRole d t i)
        (d2FlowCandidateQuota d t) depth 0 tree)).2.1 ∧
    4096 ∣ (d2FlowTreeRootData
      (d2FlowStage (fun i => d2FlowCandidateActive d t i)
        (fun i => d2FlowCandidateRole d t i)
        (d2FlowCandidateQuota d t) depth 0 tree)).2.2 := by
  cases tree with
  | leaf G low high => omega
  | node G low high children =>
      change 4096 ∣ low ∧ 4096 ∣ high at hroot
      by_cases ha : d2FlowCandidateActive d t 0 = true
      · have hnotBot := d2FlowCandidate_root_not_botRise ha
        cases hr : d2FlowCandidateRole d t 0 with
        | botRise => exact False.elim (hnotBot hr)
        | topDesc =>
            simpa [d2FlowStage, ha, hr, d2FlowTreeRootData] using hroot
        | topRise | mid | botDesc =>
            have hrole : d2OrdinaryRole (d2FlowCandidateRole d t 0) := by
              simp [d2OrdinaryRole, hr]
            have hquota := d2FlowCandidateQuota_dvd_8192 hd
              (by
                by_contra ht
                have ht0 : t = 0 := by omega
                subst t
                have htop : d2FlowCandidateRole d 0 0 = .topDesc := by
                  simp [d2FlowCandidateRole]
                simp [htop] at hr) ha hrole
            obtain ⟨q, hq⟩ := hquota
            have hhalf : 4096 ∣
                d2FlowCandidateQuota d t 0 (d2FlowCandidateRole d t 0) / 2 := by
              refine ⟨q, ?_⟩
              rw [hq]
              omega
            have hremain : 4096 ∣ d2FlowCandidateQuota d t 0
                (d2FlowCandidateRole d t 0) -
                d2FlowCandidateQuota d t 0 (d2FlowCandidateRole d t 0) / 2 := by
              refine ⟨q, ?_⟩
              rw [hq]
              omega
            have hnewHigh : 4096 ∣ high +
                d2FlowCandidateQuota d t 0 (d2FlowCandidateRole d t 0) -
                d2FlowCandidateQuota d t 0 (d2FlowCandidateRole d t 0) / 2 := by
              have heq : high + d2FlowCandidateQuota d t 0
                    (d2FlowCandidateRole d t 0) -
                    d2FlowCandidateQuota d t 0 (d2FlowCandidateRole d t 0) / 2 =
                  high + (d2FlowCandidateQuota d t 0
                    (d2FlowCandidateRole d t 0) -
                    d2FlowCandidateQuota d t 0 (d2FlowCandidateRole d t 0) / 2) := by
                omega
              rw [heq]
              exact dvd_add hroot.2 hremain
            simpa [d2FlowStage, ha, hr, d2FlowTreeRootData] using
              And.intro (dvd_add hroot.1 hhalf)
                hnewHigh
      · simpa [d2FlowStage, ha, d2FlowTreeRootData] using hroot

/-- Tile alignment plus role-sensitive endpoint alignment implies the concrete
ordinary-front contract for the candidate. Thus the scheduler need only
maintain endpoint residues; front and quota divisibility are consequences. -/
theorem d2FlowCandidate_endpointsAligned_to_frontContract
    {d t h : Nat} (hd : 7 ≤ d) (i : Nat) (tree : D2FlowTree h)
    (htile : d2FlowTileAligned tree)
    (hends : d2FlowStageOrdinaryEndpointsAligned
      (fun j => d2FlowCandidateActive d t j)
      (fun j => d2FlowCandidateRole d t j) i tree) :
    d2FlowStageFrontContract
      (fun j => d2FlowCandidateActive d t j)
      (fun j => d2FlowCandidateRole d t j)
      (d2FlowCandidateQuota d t) i tree := by
  induction h generalizing i with
  | zero =>
      cases tree
      simp [d2FlowStageFrontContract]
  | succ h ih =>
      cases tree with
      | node G low high children =>
          rcases htile with ⟨_, hlow, hhigh, htileChildren⟩
          rcases hends with ⟨hroot, hendsChildren⟩
          refine ⟨?_, ?_⟩
          · intro j
            exact ih (i + 1) (children j) (htileChildren j)
              (hendsChildren j)
          · intro ha hr
            have htpos : 0 < t := by
              by_contra ht
              have htzero : t = 0 := by omega
              subst t
              have htop : d2FlowCandidateRole d 0 i = .topDesc := by
                simp [d2FlowCandidateRole]
              have hfalse : d2OrdinaryRole .topDesc := by
                simpa [htop] using hr
              simp [d2OrdinaryRole] at hfalse
            have hquota := d2FlowCandidateQuota_dvd_8192 hd htpos ha hr
            have hhalf : 4096 ∣
                d2FlowCandidateQuota d t i (d2FlowCandidateRole d t i) / 2 := by
              obtain ⟨q, hq⟩ := hquota
              refine ⟨q, ?_⟩
              rw [hq]
              omega
            have htotal : 4096 ∣ d2FlowTotal
                (fun j => d2FlowTreeRootDeficit (children j)) := by
              apply d2FlowTotal_dvd
              intro j
              exact d2FlowTileAligned_root_dvd (children j) (htileChildren j)
            rcases hroot ha hr with ⟨hlowEnds, hhighEnds⟩
            refine ⟨dvd_add hlowEnds hhalf, ?_⟩
            apply d2_dvd_sub_trunc
            · exact d2_dvd_sub_trunc htotal hhighEnds
            · exact hhalf

/-- The quota half of the recursive stage contract follows from the explicit
candidate schedule. This converts a front-only scheduler hypothesis into the
full contract required by the generic tree transition theorem. -/
theorem d2FlowStageFrontContract_to_tileContract {d t : Nat}
    (hd : 7 ≤ d) :
    ∀ {h : Nat} (i : Nat) (tree : D2FlowTree h),
      d2FlowStageFrontContract
        (fun j => d2FlowCandidateActive d t j)
        (fun j => d2FlowCandidateRole d t j)
        (d2FlowCandidateQuota d t) (h := h) i tree →
      d2FlowStageTileContract
        (fun j => d2FlowCandidateActive d t j)
        (fun j => d2FlowCandidateRole d t j)
        (d2FlowCandidateQuota d t) (h := h) i tree := by
  intro h i tree hfront
  induction h generalizing i with
  | zero =>
      cases tree
      simp [d2FlowStageTileContract]
  | succ h ih =>
      cases tree with
      | node G low high children =>
          rcases hfront with ⟨hchildren, hfronts⟩
          constructor
          · intro j
            exact ih (i + 1) (children j) (hchildren j)
          constructor
          · intro ha hrole
            have ht : 0 < t := by
              by_contra ht
              have ht0 : t = 0 := by omega
              subst t
              have htop : d2FlowCandidateRole d 0 i = .topDesc := by
                simp [d2FlowCandidateRole]
              simp [d2OrdinaryRole, htop] at hrole
            exact d2_dvd_8192_to_4096
              (d2FlowCandidateQuota_dvd_8192 hd ht ha hrole)
          · exact hfronts

/-- Combined schedule-to-flow step: if a child is an active ordinary sender
at the next stage, the actual previous-stage parent update gives it aligned
root data, assuming the parent's ordinary fronts and child blocks are aligned.
The schedule excludes `botRise`; `topDesc` clears the root instead. -/
theorem d2FlowCandidate_activeOrdinary_child_rootAligned_next
    {d t i h G low high : Nat} (children : Fin 8 → D2FlowTree h)
    (hd : 7 ≤ d) (ht : 2 ≤ t + 1)
    (haChild : d2FlowCandidateActive d (t + 1) (i + 1) = true)
    (hrChild : d2OrdinaryRole (d2FlowCandidateRole d (t + 1) (i + 1)))
    (hfront : 4096 ∣ low ∧ 4096 ∣ high)
    (hchildren : ∀ j, d2FlowTileAligned (children j)) (j : Fin 8) :
    4096 ∣ (d2FlowTreeRootData
      (d2FlowTreeChild
        (d2FlowStage
          (fun k => d2FlowCandidateActive d t k)
          (fun k => d2FlowCandidateRole d t k)
          (d2FlowCandidateQuota d t) (h + 1) i
          (.node G low high children)) j)).1 ∧
    4096 ∣ (d2FlowTreeRootData
      (d2FlowTreeChild
        (d2FlowStage
          (fun k => d2FlowCandidateActive d t k)
          (fun k => d2FlowCandidateRole d t k)
          (d2FlowCandidateQuota d t) (h + 1) i
          (.node G low high children)) j)).2.1 ∧
    4096 ∣ (d2FlowTreeRootData
      (d2FlowTreeChild
        (d2FlowStage
          (fun k => d2FlowCandidateActive d t k)
          (fun k => d2FlowCandidateRole d t k)
          (d2FlowCandidateQuota d t) (h + 1) i
          (.node G low high children)) j)).2.2 := by
  have hcases := d2FlowCandidate_activeOrdinary_parent_cases_succ
    hd ht haChild hrChild
  rcases hcases.2 with htop | hregular
  · exact d2FlowStage_topDesc_child_rootAligned children hcases.1 htop j
  · have hquota : 8192 ∣ d2FlowCandidateQuota d t i
        (d2FlowCandidateRole d t i) :=
      d2FlowCandidateQuota_dvd_8192 hd (by omega) hcases.1 hregular
    exact d2FlowStage_ordinary_child_rootAligned children hcases.1 hregular
      hquota hfront.1 hfront.2 hchildren j

/-- Descendant alignment propagates through one candidate stage once the
current root endpoints are aligned whenever that root is an ordinary sender. -/
theorem d2FlowCandidateStage_preserves_descEndpointsAligned
    {d t h : Nat} (hd : 7 ≤ d) (ht : 1 ≤ t) (i : Nat)
    (tree : D2FlowTree h) (htile : d2FlowTileAligned tree)
    (hroot : d2FlowCandidateActive d t i = true →
      d2OrdinaryRole (d2FlowCandidateRole d t i) →
      4096 ∣ (d2FlowTreeRootData tree).2.1 ∧
      4096 ∣ (d2FlowTreeRootData tree).2.2)
    (hdesc : d2FlowStageDescEndpointsAligned
      (fun j => d2FlowCandidateActive d t j)
      (fun j => d2FlowCandidateRole d t j) i tree) :
    d2FlowStageDescEndpointsAligned
      (fun j => d2FlowCandidateActive d (t + 1) j)
      (fun j => d2FlowCandidateRole d (t + 1) j) i
      (d2FlowStage (fun j => d2FlowCandidateActive d t j)
        (fun j => d2FlowCandidateRole d t j)
        (d2FlowCandidateQuota d t) h i tree) := by
  induction h generalizing i with
  | zero =>
      cases tree
      exact True.intro
  | succ h ih =>
      cases tree with
      | node G low high children =>
          rcases htile with ⟨_, _, _, htileChildren⟩
          cases hactive : d2FlowCandidateActive d t i
          · simp only [d2FlowStage, hactive] at ⊢
            change ∀ j, _
            intro j
            rcases hdesc j with ⟨hchildRoot, hchildDesc⟩
            have hstepped := ih (i + 1) (children j) (htileChildren j)
              hchildRoot hchildDesc
            refine ⟨?_, hstepped⟩
            intro haChild hrChild
            have hcases := d2FlowCandidate_activeOrdinary_parent_cases_succ
              hd (by omega) haChild hrChild
            have hparent : d2FlowCandidateActive d t i = true := by
              simpa using hcases.1
            rw [hactive] at hparent
            cases hparent
          · cases hrole : d2FlowCandidateRole d t i with
            | topDesc =>
                simp only [d2FlowStage, hactive, hrole] at ⊢
                change ∀ j, _
                intro j
                rcases hdesc j with ⟨hchildRoot, hchildDesc⟩
                have hstepped := ih (i + 1) (children j) (htileChildren j)
                  hchildRoot hchildDesc
                constructor
                · intro _ _
                  simp [d2FlowTreeRootData_setRoot]
                · exact d2FlowStageDescEndpointsAligned_setRoot
                    (d2FlowStage
                      (fun k => d2FlowCandidateActive d t k)
                      (fun k => d2FlowCandidateRole d t k)
                      (d2FlowCandidateQuota d t) h (i + 1) (children j))
                    hstepped 0 0 0
            | botRise =>
                simp only [d2FlowStage, hactive, hrole] at ⊢
                change ∀ j, _
                intro j
                rcases hdesc j with ⟨hchildRoot, hchildDesc⟩
                have hstepped := ih (i + 1) (children j) (htileChildren j)
                  hchildRoot hchildDesc
                refine ⟨?_, hstepped⟩
                intro haChild hrChild
                have hcases := d2FlowCandidate_activeOrdinary_parent_cases_succ
                  hd (by omega) haChild hrChild
                have hparentRole : d2FlowCandidateRole d t i = .topDesc ∨
                    d2OrdinaryRole (d2FlowCandidateRole d t i) := by
                  simpa using hcases.2
                rcases hparentRole with htop | hregular
                · rw [hrole] at htop
                  cases htop
                · have hfalse : d2OrdinaryRole .botRise := by
                    simpa [hrole] using hregular
                  simp [d2OrdinaryRole] at hfalse
            | topRise | mid | botDesc =>
                simp only [d2FlowStage, hactive, hrole] at ⊢
                let sizes : Fin 8 → Nat := fun k =>
                  d2FlowTreeRootDeficit (children k)
                let left := low + d2FlowCandidateQuota d t i
                  (d2FlowCandidateRole d t i) / 2
                let right := d2FlowTotal sizes - high -
                  d2FlowCandidateQuota d t i (d2FlowCandidateRole d t i) / 2
                change ∀ j, _
                intro j
                rcases hdesc j with ⟨hchildRoot, hchildDesc⟩
                have hstepped := ih (i + 1) (children j) (htileChildren j)
                  hchildRoot hchildDesc
                have hparentEnds := hroot hactive
                  (by simp [d2OrdinaryRole, hrole])
                constructor
                · intro haChild hrChild
                  have hnext := d2FlowCandidate_activeOrdinary_child_rootAligned_next
                    (d := d) (t := t) (i := i) (h := h) (G := G)
                    (low := low) (high := high) children hd (by omega)
                    haChild hrChild hparentEnds
                    htileChildren j
                  simpa [d2FlowStage, hactive, hrole, d2FlowTreeChild,
                    d2FlowTreeSetRoot, d2FlowCutChild, sizes, left, right]
                    using And.intro hnext.2.1 hnext.2.2
                · let outG := d2FlowCutChild (d2FlowPosition sizes j)
                    (sizes j) left right |>.1
                  let outLow := d2FlowCutChild (d2FlowPosition sizes j)
                    (sizes j) left right |>.2.1
                  let outHigh := d2FlowCutChild (d2FlowPosition sizes j)
                    (sizes j) left right |>.2.2
                  have hset := d2FlowStageDescEndpointsAligned_setRoot
                    (d2FlowStage
                      (fun k => d2FlowCandidateActive d t k)
                      (fun k => d2FlowCandidateRole d t k)
                      (d2FlowCandidateQuota d t) h (i + 1) (children j))
                    hstepped outG outLow outHigh
                  simpa [d2FlowStage, hactive, hrole, d2FlowTreeChild,
                    d2FlowTreeSetRoot, d2FlowCutChild, sizes, left, right,
                    outG, outLow, outHigh] using hset

/-- The full candidate run is 4096-aligned at every time if all actual active
ordinary senders have 4096-aligned fronts. Quota divisibility is discharged
by `d2FlowCandidateQuota_dvd_8192`. -/
theorem d2FlowCandidateRun_tileAligned_of_frontContracts {d : Nat}
    (hd : 7 ≤ d)
    (hfronts : ∀ t,
      d2FlowStageFrontContract
        (fun i => d2FlowCandidateActive d t i)
        (fun i => d2FlowCandidateRole d t i)
        (d2FlowCandidateQuota d t) (h := d) 0
        (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) t)) :
    ∀ t, d2FlowTileAligned (d2FlowCandidateRun d
      (d2FlowTreeInitial 8192 d) t) := by
  apply d2FlowCandidateRun_tileAligned_of_contracts
  intro t
  exact d2FlowStageFrontContract_to_tileContract hd
    0 (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) t) (hfronts t)

/-- One candidate stage advances the coupled alignment state: tile rows,
root endpoint residues, and every active ordinary descendant endpoint. This
is the reusable induction step for replacing the finite-depth alignment
screens by an all-depth invariant. -/
theorem d2FlowCandidateRun_alignment_step {d t : Nat} (hd : 7 ≤ d)
    (ht : 1 ≤ t)
    (htile : d2FlowTileAligned
      (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) t))
    (hroot : 4096 ∣ (d2FlowTreeRootData
      (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) t)).2.1 ∧
      4096 ∣ (d2FlowTreeRootData
      (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) t)).2.2)
    (hdesc : d2FlowStageDescEndpointsAligned
      (fun i => d2FlowCandidateActive d t i)
      (fun i => d2FlowCandidateRole d t i) 0
      (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) t)) :
    d2FlowTileAligned
        (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) (t + 1)) ∧
      (4096 ∣ (d2FlowTreeRootData
        (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) (t + 1))).2.1 ∧
       4096 ∣ (d2FlowTreeRootData
        (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) (t + 1))).2.2) ∧
      d2FlowStageDescEndpointsAligned
        (fun i => d2FlowCandidateActive d (t + 1) i)
        (fun i => d2FlowCandidateRole d (t + 1) i) 0
        (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) (t + 1)) := by
  let tree := d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) t
  have hrootOrd : d2FlowStageOrdinaryEndpointsAligned
      (fun i => d2FlowCandidateActive d t i)
      (fun i => d2FlowCandidateRole d t i) 0 tree :=
    d2FlowStageDescEndpointsAligned_to_ordinaryEndpoints tree
      (fun ha hr => hroot) hdesc
  have hfront := d2FlowCandidate_endpointsAligned_to_frontContract
    (d := d) (t := t) hd 0 tree htile hrootOrd
  have hcontract := d2FlowStageFrontContract_to_tileContract hd
    0 tree hfront
  have htileNext := d2FlowStage_preserves_tileAligned 0 tree hcontract htile
  have hrootNext := d2FlowCandidateStage_preserves_rootEndpointsAligned
    (d := d) (t := t) (depth := d) hd (by omega) tree hroot
  have hdescNext := d2FlowCandidateStage_preserves_descEndpointsAligned
    hd ht 0 tree htile (fun _ _ => hroot) hdesc
  refine ⟨?_, ?_, ?_⟩
  · simpa [tree, d2FlowCandidateRun, d2FlowCandidateStage] using htileNext
  · simpa [tree, d2FlowCandidateRun, d2FlowCandidateStage] using hrootNext
  · simpa [tree, d2FlowCandidateRun, d2FlowCandidateStage] using hdescNext

/-- The concrete candidate run enters the coupled alignment invariant after
its explicit bootstrap reset. -/
theorem d2FlowCandidateRun_alignment_base {d : Nat} (hd : 7 ≤ d) :
    d2FlowTileAligned
        (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 1) ∧
      (4096 ∣ (d2FlowTreeRootData
        (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 1)).2.1 ∧
       4096 ∣ (d2FlowTreeRootData
        (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 1)).2.2) ∧
      d2FlowStageDescEndpointsAligned
        (fun i => d2FlowCandidateActive d 1 i)
        (fun i => d2FlowCandidateRole d 1 i) 0
        (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 1) := by
  have htree0 : d2FlowTileAligned (d2FlowTreeInitial 8192 d) :=
    d2FlowTreeInitial_tileAligned 8192 d ⟨2, rfl⟩
  have hfront0 := d2FlowCandidate_stage0_frontContract (d := d) 0
    (d2FlowTreeInitial 8192 d)
  have hcontract0 := d2FlowStageFrontContract_to_tileContract hd
    0 (d2FlowTreeInitial 8192 d) hfront0
  have htile1 := d2FlowStage_preserves_tileAligned 0
    (d2FlowTreeInitial 8192 d) hcontract0 htree0
  have hroot0 : 4096 ∣ (d2FlowTreeRootData
      (d2FlowTreeInitial 8192 d)).2.1 ∧
      4096 ∣ (d2FlowTreeRootData
      (d2FlowTreeInitial 8192 d)).2.2 := by
    cases d with
    | zero => omega
    | succ d => simp [d2FlowTreeInitial, d2FlowTreeRootData]
  have hroot1 := d2FlowCandidateStage_preserves_rootEndpointsAligned
    (d := d) (t := 0) (depth := d) hd (by omega)
    (d2FlowTreeInitial 8192 d) hroot0
  have hdesc1 : d2FlowStageDescEndpointsAligned
      (fun i => d2FlowCandidateActive d 1 i)
      (fun i => d2FlowCandidateRole d 1 i) 0
      (d2FlowCandidateStage d 0 (d2FlowTreeInitial 8192 d)) := by
    cases d with
    | zero => omega
    | succ h =>
        rw [d2FlowCandidateStage_zero_initial_shape]
        change ∀ j, _
        intro j
        constructor
        · intro _ _
          simp [d2FlowTreeRootData_setRoot]
        · apply d2FlowStageDescEndpointsAligned_of_inactive_after
            (d2FlowTreeSetRoot (d2FlowTreeFull 8192 h) 0 0 0)
          intro k hk
          have hk2 : 2 ≤ k := by omega
          have hne : k ≠ 1 := by omega
          simp [d2FlowCandidateActive, hne]
  refine ⟨?_, ?_, ?_⟩
  · simpa [d2FlowCandidateRun, d2FlowCandidateStage] using htile1
  · simpa [d2FlowCandidateRun, d2FlowCandidateStage] using hroot1
  · simpa [d2FlowCandidateRun] using hdesc1

/-- The coupled alignment state holds at every positive candidate stage. -/
theorem d2FlowCandidateRun_alignment_all {d : Nat} (hd : 7 ≤ d) :
    ∀ t, 1 ≤ t →
      d2FlowTileAligned
          (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) t) ∧
        (4096 ∣ (d2FlowTreeRootData
          (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) t)).2.1 ∧
         4096 ∣ (d2FlowTreeRootData
          (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) t)).2.2) ∧
        d2FlowStageDescEndpointsAligned
          (fun i => d2FlowCandidateActive d t i)
          (fun i => d2FlowCandidateRole d t i) 0
          (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) t) := by
  have hsucc : ∀ k, d2FlowTileAligned
        (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) (k + 1)) ∧
      (4096 ∣ (d2FlowTreeRootData
        (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) (k + 1))).2.1 ∧
       4096 ∣ (d2FlowTreeRootData
        (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) (k + 1))).2.2) ∧
      d2FlowStageDescEndpointsAligned
        (fun i => d2FlowCandidateActive d (k + 1) i)
        (fun i => d2FlowCandidateRole d (k + 1) i) 0
        (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) (k + 1)) := by
    intro k
    induction k with
    | zero => simpa using d2FlowCandidateRun_alignment_base hd
    | succ k ih =>
        rcases ih with ⟨htile, hroot, hdesc⟩
        exact d2FlowCandidateRun_alignment_step hd (by omega)
          htile hroot hdesc
  intro t ht
  cases t with
  | zero => omega
  | succ t => simpa using hsucc t

/-- The actual candidate satisfies the recursive front contract at every
stage, including the nonordinary bootstrap stage. -/
theorem d2FlowCandidateRun_frontContract_all {d : Nat} (hd : 7 ≤ d) :
    ∀ t, d2FlowStageFrontContract
      (fun i => d2FlowCandidateActive d t i)
      (fun i => d2FlowCandidateRole d t i)
      (d2FlowCandidateQuota d t) (h := d) 0
      (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) t) := by
  intro t
  by_cases ht : t = 0
  · subst t
    exact d2FlowCandidate_stage0_frontContract (d := d) 0
      (d2FlowTreeInitial 8192 d)
  · have htpos : 1 ≤ t := by omega
    rcases d2FlowCandidateRun_alignment_all hd t htpos with
      ⟨htile, hroot, hdesc⟩
    let tree := d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) t
    have hends := d2FlowStageDescEndpointsAligned_to_ordinaryEndpoints tree
      (fun _ _ => hroot) hdesc
    exact d2FlowCandidate_endpointsAligned_to_frontContract
      (d := d) (t := t) hd 0 tree htile hends

/-- The actual scale-8192 candidate run is tile-aligned at every stage, with
all recursive front obligations discharged by the coupled induction above. -/
theorem d2FlowCandidateRun_tileAligned_all {d : Nat} (hd : 7 ≤ d) :
    ∀ t, d2FlowTileAligned (d2FlowCandidateRun d
      (d2FlowTreeInitial 8192 d) t) :=
  d2FlowCandidateRun_tileAligned_of_frontContracts hd
    (d2FlowCandidateRun_frontContract_all hd)

end Chvatal.D2Reserve
