import CandidateFrontier
import AKS.Chvatal.FlowSizes7
import AKS.Chvatal.WireFlow
import AKS.Chvatal.RealNets
import AKS.Chvatal.BadSendReal
import AKS.Chvatal.Lemma41Real
import AKS.Chvatal.RealInduction
import AKS.Chvatal.TwoRoundProof
import SignedReserve
import Mathlib.Tactic

namespace Tapered945

/-- Exact root size at the start of the two special initialization rounds. -/
def seedRootInput (d : Nat) : Nat := 64 ^ d

/-- Wires sent from the root to each level-one address at stage zero. -/
def seedRootDown (d : Nat) : Nat := 2 ^ (6 * d - 6)

/-- The even level-one up-flow chosen so that the root occupancy at stage two
is exactly its upper-frontier reference capacity. -/
def seedLevelOneUp (d : Nat) : Nat := 2 ^ (6 * d - 22)

/-- Level-one down-flow per child at stage one. -/
def seedLevelOneDown (d : Nat) : Nat :=
  2 ^ (6 * d - 12) - 2 ^ (6 * d - 28)

/-- Per-node counts during the two special initialization rounds and at the
stage-two frontier. -/
def seedNodeSize (d l t : Nat) : Nat :=
  if t = 0 then if l = 0 then seedRootInput d else 0
  else if t = 1 then if l = 1 then seedRootDown d else 0
  else if t = 2 then
    if l = 0 then 64 * seedLevelOneUp d
    else if l = 2 then seedLevelOneDown d else 0
  else 0

/-- Per-node up-flow for the two initialization rounds. -/
def seedUpAt (d l t : Nat) : Nat :=
  if t = 1 ∧ l = 1 then seedLevelOneUp d else 0

/-- Per-node down-flow for the two initialization rounds. -/
def seedDownAt (d l t : Nat) : Nat :=
  if t = 0 ∧ l = 0 then seedRootDown d
  else if t = 1 ∧ l = 1 then seedLevelOneDown d else 0

/-- Stage zero conserves the entire input root into 64 equal first-level
blocks. -/
theorem seed_root_conservation (d : Nat) (hd : 5 ≤ d) :
    seedRootInput d = 64 * seedRootDown d := by
  unfold seedRootInput seedRootDown
  calc
    64 ^ d = 2 ^ (6 * d) := by
      rw [show (64 : Nat) = 2 ^ 6 by norm_num, pow_mul]
    _ = 2 ^ 6 * 2 ^ (6 * d - 6) := by
      rw [← pow_add]
      congr 1
      omega
    _ = 64 * 2 ^ (6 * d - 6) := by norm_num

/-- The special stage-one node splits exactly into one up-flow and 64 equal
down-flows. -/
theorem seed_level_one_conservation (d : Nat) (hd : 5 ≤ d) :
    seedRootDown d = seedLevelOneUp d + 64 * seedLevelOneDown d := by
  unfold seedRootDown seedLevelOneUp seedLevelOneDown
  let x : Nat := 2 ^ (6 * d - 28)
  have hx : 2 ^ (6 * d - 6) = 2 ^ 22 * x := by
    dsimp [x]
    rw [show 6 * d - 6 = 22 + (6 * d - 28) by omega, pow_add]
    norm_num
  have hu : 2 ^ (6 * d - 22) = 2 ^ 6 * x := by
    dsimp [x]
    rw [show 6 * d - 22 = 6 + (6 * d - 28) by omega, pow_add]
    norm_num
  have hdw : 2 ^ (6 * d - 12) = 2 ^ 16 * x := by
    dsimp [x]
    rw [show 6 * d - 12 = 16 + (6 * d - 28) by omega, pow_add]
    norm_num
  rw [hx, hu, hdw]
  dsimp [x]
  omega

/-- The level-one up-flow is even, as required by the Chvatal node interface. -/
theorem seed_level_one_up_even (d : Nat) (hd : 5 ≤ d) :
    Even (seedLevelOneUp d) := by
  unfold seedLevelOneUp
  refine ⟨2 ^ (6 * d - 23), ?_⟩
  have hpow : 6 * d - 22 = (6 * d - 23) + 1 := by omega
  rw [hpow, pow_succ]
  omega

/-- After the two special stages the root receives exactly the candidate
upper-frontier capacity `C(d,0,2)`. -/
theorem seed_stage_two_root_matches_capacity (d : Nat) (hd : 5 ≤ d) :
    64 * seedLevelOneUp d = candidateReferenceCapacity d 0 2 := by
  have hcap : candidateCapacityExponent d 0 2 = 6 * d - 16 := by
    unfold candidateCapacityExponent
    omega
  unfold seedLevelOneUp candidateReferenceCapacity
  rw [hcap]
  push_cast
  rw [show (64 : Rat) = 2 ^ 6 by norm_num, ← pow_add]
  congr 1
  omega

/-- The level-two seed is the native block size minus the small bottom
frontier reserve `C(d,2,2)/cap`. -/
theorem seed_stage_two_bottom_reserve (d : Nat) (hd : 5 ≤ d) :
    seedLevelOneDown d + 2 ^ (6 * d - 28) = 2 ^ (6 * d - 12) := by
  unfold seedLevelOneDown
  exact Nat.sub_add_cancel (by
    have hpow : 6 * d - 12 = 16 + (6 * d - 28) := by omega
    rw [hpow, pow_add]
    omega)

/-- The reserve in the preceding theorem is exactly the candidate bottom
capacity divided by `Q=2^24`. -/
theorem seed_bottom_reserve_eq_capacity_div (d : Nat) (hd : 5 ≤ d) :
    (candidateReferenceCapacity d 2 2 : Rat) / cap =
      (2 ^ (6 * d - 28) : Nat) := by
  have hexp : candidateCapacityExponent d 2 2 = 24 + (6 * d - 28) := by
    unfold candidateCapacityExponent
    omega
  have hcap : cap = 2 ^ 24 := by norm_num [cap]
  rw [candidateReferenceCapacity, hexp, pow_add, hcap]
  push_cast
  have hpositive : 0 < (2 ^ (6 * d - 28) : Rat) := by positivity
  field_simp

/-- The lower-frontier seed is intentionally not an ordinary interior
occupancy. Its actual count is a native interval minus the small reserved
tail, whereas the reference capacity at `(level,time)=(2,2)` is 256 times
that interval. This exact gap rules out applying the ordinary
`LocalIntegerFlow` premise to the stage-two bottom frontier. -/
theorem seed_bottom_not_interior_occupancy (d : Nat) (hd : 14 ≤ d) :
    ((1 - 1 / cap) * candidateReferenceCapacity d 2 2) -
        (seedLevelOneDown d : Rat) =
      255 * (2 : Rat) ^ (6 * d - 12) := by
  let x : Nat := 2 ^ (6 * d - 12)
  let r : Nat := 2 ^ (6 * d - 28)
  have hxr : x = 2 ^ 16 * r := by
    dsimp [x, r]
    rw [show 6 * d - 12 = 16 + (6 * d - 28) by omega, pow_add]
    norm_num
  have hC : candidateReferenceCapacity d 2 2 = 256 * (x : Rat) := by
    have hexp : candidateCapacityExponent d 2 2 = 8 + (6 * d - 12) := by
      unfold candidateCapacityExponent
      omega
    unfold candidateReferenceCapacity
    rw [hexp, pow_add]
    norm_num [x]
  have hcap : cap = 2 ^ 24 := by norm_num [cap]
  have hrx : r ≤ x := by
    rw [hxr]
    exact Nat.le_mul_of_pos_left r (by norm_num)
  have hseed : (seedLevelOneDown d : Rat) = (x : Rat) - r := by
    unfold seedLevelOneDown
    rw [Nat.cast_sub hrx]
  have hquot : (1 / (2 ^ 24 : Rat)) * (256 * (x : Rat)) = r := by
    rw [hxr]
    norm_num
    ring
  have hxcast : (x : Rat) = (2 : Rat) ^ (6 * d - 12) := by
    simp [x]
  rw [hC, hcap, hseed]
  rw [show (1 - 1 / (2 ^ 24 : Rat)) * (256 * (x : Rat)) =
      256 * (x : Rat) - r by rw [sub_mul, one_mul, hquot]]
  rw [← hxcast]
  ring

/-- The seeded top root also lies outside the ordinary 69-wire occupancy
window: its special stage-two count is exactly `C`, rather than
`(1-1/Q)C + O(69)`. The ordinary induction must start below this frontier. -/
theorem seed_top_occupancy_defect_gt_69 (d : Nat) (hd : 14 ≤ d) :
    69 < |(seedNodeSize d 0 2 : Rat) -
      (1 - 1 / cap) * candidateReferenceCapacity d 0 2| := by
  have hd5 : 5 ≤ d := by omega
  have hseed : (seedNodeSize d 0 2 : Rat) = candidateReferenceCapacity d 0 2 := by
    simpa [seedNodeSize] using seed_stage_two_root_matches_capacity d hd5
  have hcap : cap = 2 ^ 24 := by norm_num [cap]
  have hexp : candidateCapacityExponent d 0 2 = 24 + (6 * d - 40) := by
    unfold candidateCapacityExponent
    omega
  have hratio : candidateReferenceCapacity d 0 2 / cap =
      (2 : Rat) ^ (6 * d - 40) := by
    unfold candidateReferenceCapacity
    rw [hexp, pow_add, hcap]
    ring
  have hexpLower : 44 ≤ 6 * d - 40 := by omega
  have hlarge : (69 : Rat) < 2 ^ 44 := by norm_num
  have hpow : (2 : Rat) ^ 44 ≤ (2 : Rat) ^ (6 * d - 40) :=
    pow_le_pow_right₀ (by norm_num : (1 : Rat) ≤ 2) hexpLower
  rw [hseed]
  have hdiff : candidateReferenceCapacity d 0 2 -
      (1 - 1 / cap) * candidateReferenceCapacity d 0 2 =
        candidateReferenceCapacity d 0 2 / cap := by ring
  have hCpos : 0 < candidateReferenceCapacity d 0 2 := by
    unfold candidateReferenceCapacity
    positivity
  rw [hdiff, abs_of_pos (div_pos
    hCpos (by rw [hcap]; positivity)), hratio]
  exact lt_of_lt_of_le hlarge hpow

/-- Every initialized node splits exactly into its up-flow and 64 equal
down-flows at stage zero. -/
def seedTopDown2 (d : Nat) : Nat := 2 ^ (6 * d - 22)

def seedBottomUp2 (d : Nat) : Nat := 255 * 2 ^ (6 * d - 28)

def seedBottomDown2 (d : Nat) : Nat :=
  2 ^ (6 * d - 18) - 2 ^ (6 * d - 26)

def seedStageThreeTopSize (d : Nat) : Nat := 2 ^ (6 * d - 14)

def seedStageThreeBottomSize (d : Nat) : Nat := seedBottomDown2 d

private theorem seed_down_as_common_mass (d : Nat) (hd : 14 ≤ d) :
    seedLevelOneDown d = 65535 * 2 ^ (6 * d - 28) := by
  unfold seedLevelOneDown
  rw [show 6 * d - 12 = 16 + (6 * d - 28) by omega, pow_add]
  norm_num only [show (2 : Nat) ^ 16 = 65536 by norm_num]
  omega

private theorem seed_bottom_down_as_common_mass (d : Nat) (hd : 14 ≤ d) :
    seedBottomDown2 d = 1020 * 2 ^ (6 * d - 28) := by
  unfold seedBottomDown2
  rw [show 6 * d - 18 = 10 + (6 * d - 28) by omega,
      show 6 * d - 26 = 2 + (6 * d - 28) by omega, pow_add, pow_add]
  norm_num only [show (2 : Nat) ^ 10 = 1024 by norm_num,
    show (2 : Nat) ^ 2 = 4 by norm_num]
  omega

theorem seed_top_frontier_split (d : Nat) (hd : 14 ≤ d) :
    seedNodeSize d 0 2 = 64 * seedTopDown2 d := by
  rfl

theorem seed_bottom_frontier_split (d : Nat) (hd : 14 ≤ d) :
    seedLevelOneDown d = seedBottomUp2 d + 64 * seedBottomDown2 d := by
  rw [seed_down_as_common_mass d hd, seed_bottom_down_as_common_mass d hd]
  unfold seedBottomUp2
  omega

theorem seed_stage_three_top_count (d : Nat) (hd : 14 ≤ d) :
    seedTopDown2 d + 64 * seedBottomUp2 d = seedStageThreeTopSize d := by
  unfold seedTopDown2 seedBottomUp2 seedStageThreeTopSize
  rw [show 6 * d - 22 = 6 + (6 * d - 28) by omega,
      show 6 * d - 14 = 14 + (6 * d - 28) by omega, pow_add, pow_add]
  norm_num
  ring

theorem seed_stage_three_bottom_reserve (d : Nat) (hd : 14 ≤ d) :
    seedStageThreeBottomSize d + 2 ^ (6 * d - 26) = 2 ^ (6 * d - 18) := by
  unfold seedStageThreeBottomSize seedBottomDown2
  exact Nat.sub_add_cancel (by
    have he : 6 * d - 18 = 8 + (6 * d - 26) := by omega
    rw [he, pow_add]
    omega)

theorem seed_stage_three_matches_frontiers (d : Nat) (hd : 14 ≤ d) :
    candidateAlpha d 3 = 1 ∧ candidateOmega 3 = 3 ∧
      (seedStageThreeTopSize d : Rat) = candidateReferenceCapacity d 1 3 ∧
      (candidateReferenceCapacity d 3 3 : Rat) / cap =
        (2 ^ (6 * d - 26) : Nat) := by
  have hAlpha : candidateAlpha d 3 = 1 := by
    unfold candidateAlpha candidateAlphaBase Chvatal.ceilParity
    simp only [show (2 * 3 + 23) / 3 = 9 by norm_num]
    have hd9 : 9 ≤ d := by omega
    simp [hd9]
  have hOmega : candidateOmega 3 = 3 := by
    norm_num [candidateOmega, candidateOmegaBase, Chvatal.ceilParity]
  have hTop : (seedStageThreeTopSize d : Rat) = candidateReferenceCapacity d 1 3 := by
    have he : candidateCapacityExponent d 1 3 = 6 * d - 14 := by
      unfold candidateCapacityExponent
      omega
    rw [show (seedStageThreeTopSize d : Rat) = (2 : Rat) ^ (6 * d - 14) by
      simp [seedStageThreeTopSize]]
    simp [candidateReferenceCapacity, he]
  have hBottom : (candidateReferenceCapacity d 3 3 : Rat) / cap =
      (2 ^ (6 * d - 26) : Nat) := by
    have he : candidateCapacityExponent d 3 3 = 24 + (6 * d - 26) := by
      unfold candidateCapacityExponent
      omega
    have hc : cap = 2 ^ 24 := by norm_num [cap]
    rw [candidateReferenceCapacity, he, pow_add, hc]
    push_cast
    field_simp
  exact ⟨hAlpha, hOmega, hTop, hBottom⟩

theorem seed_split_stage_zero (d : Nat) (hd : 5 ≤ d) (l : Nat) :
    seedNodeSize d l 0 = seedUpAt d l 0 + 64 * seedDownAt d l 0 := by
  by_cases hl : l = 0
  · subst l
    simpa [seedNodeSize, seedUpAt, seedDownAt] using
      seed_root_conservation d hd
  · simp [seedNodeSize, seedUpAt, seedDownAt, hl]

/-- The one nonzero node type at stage one splits by the exact seed equation. -/
theorem seed_split_stage_one (d : Nat) (hd : 5 ≤ d) (l : Nat) :
    seedNodeSize d l 1 = seedUpAt d l 1 + 64 * seedDownAt d l 1 := by
  by_cases hl : l = 1
  · subst l
    simpa [seedNodeSize, seedUpAt, seedDownAt] using
      seed_level_one_conservation d hd
  · simp [seedNodeSize, seedUpAt, seedDownAt, hl]

/-- The first special transition sends the root's equal blocks to level one. -/
theorem seed_transition_zero (d : Nat) (hd : 5 ≤ d) (l : Nat) :
    seedNodeSize d l 1 =
      (if 1 ≤ l then seedDownAt d (l - 1) 0 else 0) +
      (if l < d then 64 * seedUpAt d (l + 1) 0 else 0) := by
  by_cases h0 : l = 0
  · subst l
    have hpos : 0 < d := by omega
    simp [seedNodeSize, seedUpAt, hpos]
  · by_cases h1 : l = 1
    · subst l
      have hpos : 1 < d := by omega
      simp [seedNodeSize, seedDownAt, seedUpAt, hpos]
    · have hsub : l - 1 ≠ 0 := by omega
      simp [seedNodeSize, seedDownAt, seedUpAt, h0, h1, hsub]

/-- The second special transition creates the stage-two top and bottom
frontier counts from the level-one up/down flows. -/
theorem seed_transition_one (d : Nat) (hd : 5 ≤ d) (l : Nat) :
    seedNodeSize d l 2 =
      (if 1 ≤ l then seedDownAt d (l - 1) 1 else 0) +
      (if l < d then 64 * seedUpAt d (l + 1) 1 else 0) := by
  by_cases h0 : l = 0
  · subst l
    have hpos : 0 < d := by omega
    simp [seedNodeSize, seedUpAt, hpos]
  · by_cases h1 : l = 1
    · subst l
      have hpos : 1 < d := by omega
      simp [seedNodeSize, seedDownAt, seedUpAt, hpos]
    · by_cases h2 : l = 2
      · subst l
        have hpos : 2 < d := by omega
        simp [seedNodeSize, seedDownAt, seedUpAt, hpos]
      · have hsub : l - 1 ≠ 0 := by omega
        simp [seedNodeSize, seedDownAt, seedUpAt, h0, h2, hsub]

/-! The two special seed rounds form an actual finite Chvatal flow table.
This packages count conservation, root/leaf conditions, and even upward flow;
it still says nothing about which ranks the local networks route. -/

def candidateSeedFlowSizes (d : Nat) (hd : 14 ≤ d) : Chvatal.FlowSizes d 2 where
  a := seedNodeSize d
  up := seedUpAt d
  down := seedDownAt d
  ha_root := by simp [seedNodeSize, seedRootInput]
  ha_init := by
    intro l hl
    simp [seedNodeSize]
    omega
  hup_even := by
    intro l t ht
    have ht0 : t = 0 ∨ t = 1 := by omega
    rcases ht0 with rfl | rfl
    · simp [seedUpAt]
    · by_cases hl : l = 1
      · subst l
        exact (seed_level_one_up_even d (by omega)).two_dvd
      · simp [seedUpAt, hl]
  hup_root := by
    intro t ht
    simp [seedUpAt]
  hdown_leaf := by
    intro t ht
    have ht0 : t = 0 ∨ t = 1 := by omega
    rcases ht0 with rfl | rfl <;> simp [seedDownAt] <;> omega
  hsplit := by
    intro l t hld ht
    have ht0 : t = 0 ∨ t = 1 := by omega
    rcases ht0 with rfl | rfl
    · exact seed_split_stage_zero d (by omega) l
    · exact seed_split_stage_one d (by omega) l
  hcons := by
    intro l t hld ht
    have ht0 : t = 0 ∨ t = 1 := by omega
    rcases ht0 with rfl | rfl
    · exact seed_transition_zero d (by omega) l
    · exact seed_transition_one d (by omega) l

/-- Canonical disjoint, complete wire ownership for each of the three seed
states. This realizes the seed cardinalities as placements, but does not
assert anything about their key ranks or outsider counts. -/
noncomputable def candidateSeedPlacement (d : Nat) (hd : 14 ≤ d)
    (t : Nat) (ht : t ≤ 2) : Chvatal.Placement 64 d where
  regs := Chvatal.wireSets (candidateSeedFlowSizes d hd) t
  disjoint := by
    intro a b hne
    exact Chvatal.wireSets_disjoint (candidateSeedFlowSizes d hd) ht a b hne
  complete := by
    intro w
    exact Chvatal.wireSets_complete (candidateSeedFlowSizes d hd) ht w

theorem candidateSeedPlacement_card (d : Nat) (hd : 14 ≤ d)
    (t : Nat) (ht : t ≤ 2) (b : Chvatal.KBag 64 d) :
    ((candidateSeedPlacement d hd t ht).regs b).card =
      (candidateSeedFlowSizes d hd).a b.l t := by
  exact Chvatal.wireSets_card (candidateSeedFlowSizes d hd) ht b

/-! Immediately after the root fan-out, no wires have yet reached the
level-two subtree below any level-two bag. This gives the exact zero subtree
mass/non-native budget needed by the first stage-one child-count estimate. -/
theorem candidateSeed_stageOne_descendants_empty (d : Nat) (hd : 14 ≤ d)
    (w : Chvatal.KBag 64 d) (hw : 2 ≤ w.l) :
    (Chvatal.subtreeKeys 64 d (candidateSeedPlacement d hd 1 (by omega))
      (by norm_num) w).card = 0 := by
  rw [Chvatal.card_subtreeKeys (by norm_num)
    (candidateSeedPlacement d hd 1 (by omega)) w (seedNodeSize d · 1)]
  · apply Finset.sum_eq_zero
    intro h hh
    have hl : 2 ≤ w.l + h := by omega
    have hne : w.l + h ≠ 1 := by omega
    simp [seedNodeSize, hne]
  · intro b
    simpa [candidateSeedFlowSizes] using
      (candidateSeedPlacement_card d hd 1 (by omega) b)

def bootstrapNodeSize (d l t : Nat) : Nat :=
  if t = 3 then
    if l = 1 then seedStageThreeTopSize d
    else if l = 3 then seedStageThreeBottomSize d else 0
  else seedNodeSize d l t

def bootstrapUpAt (d l t : Nat) : Nat :=
  if t = 2 then if l = 2 then seedBottomUp2 d else 0
  else seedUpAt d l t

def bootstrapDownAt (d l t : Nat) : Nat :=
  if t = 2 then
    if l = 0 then seedTopDown2 d else if l = 2 then seedBottomDown2 d else 0
  else seedDownAt d l t

private theorem seed_bottom_up_even (d : Nat) (hd : 14 ≤ d) :
    2 ∣ seedBottomUp2 d := by
  have he : 6 * d - 28 = 1 + (6 * d - 29) := by omega
  refine ⟨255 * 2 ^ (6 * d - 29), ?_⟩
  unfold seedBottomUp2
  rw [he, pow_add]
  norm_num [pow_succ]
  ring

def candidateBootstrapFlowSizes (d : Nat) (hd : 14 ≤ d) : Chvatal.FlowSizes d 3 where
  a := bootstrapNodeSize d
  up := bootstrapUpAt d
  down := bootstrapDownAt d
  ha_root := by simp [bootstrapNodeSize, seedNodeSize, seedRootInput]
  ha_init := by
    intro l hl
    simp [bootstrapNodeSize, seedNodeSize]
    omega
  hup_even := by
    intro l t ht
    by_cases ht2 : t = 2
    · subst t
      by_cases hl : l = 2
      · subst l
        exact seed_bottom_up_even d hd
      · simp [bootstrapUpAt, hl]
    · have ht0 : t = 0 ∨ t = 1 := by omega
      rcases ht0 with rfl | rfl
      · simpa [bootstrapUpAt] using
          (candidateSeedFlowSizes d hd).hup_even l 0 (by norm_num)
      · simpa [bootstrapUpAt] using
          (candidateSeedFlowSizes d hd).hup_even l 1 (by norm_num)
  hup_root := by
    intro t ht
    by_cases ht2 : t = 2
    · subst t
      simp [bootstrapUpAt]
    · have ht0 : t = 0 ∨ t = 1 := by omega
      rcases ht0 with rfl | rfl <;> simp [bootstrapUpAt, seedUpAt]
  hdown_leaf := by
    intro t ht
    have hd0 : d ≠ 0 := by omega
    have hd1 : d ≠ 1 := by omega
    have hd2 : d ≠ 2 := by omega
    by_cases ht2 : t = 2
    · subst t
      simp [bootstrapDownAt, hd0, hd2]
    · have ht0 : t = 0 ∨ t = 1 := by omega
      rcases ht0 with rfl | rfl <;> simp [bootstrapDownAt, seedDownAt, hd0, hd1, hd2]
  hsplit := by
    intro l t hld ht
    by_cases ht2 : t = 2
    · subst t
      by_cases hl0 : l = 0
      · subst l
        simp [bootstrapNodeSize, bootstrapUpAt, bootstrapDownAt,
          seedNodeSize, seedUpAt, seedTopDown2, seedLevelOneUp]
      · by_cases hl2 : l = 2
        · subst l
          simpa [bootstrapNodeSize, bootstrapUpAt, bootstrapDownAt] using
            seed_bottom_frontier_split d hd
        · simp [bootstrapNodeSize, bootstrapUpAt, bootstrapDownAt,
            seedNodeSize, hl0, hl2]
    · have ht0 : t = 0 ∨ t = 1 := by omega
      rcases ht0 with rfl | rfl
      · simpa [bootstrapNodeSize, bootstrapUpAt, bootstrapDownAt] using
          seed_split_stage_zero d (by omega) l
      · simpa [bootstrapNodeSize, bootstrapUpAt, bootstrapDownAt] using
          seed_split_stage_one d (by omega) l
  hcons := by
    intro l t hld ht
    by_cases ht2 : t = 2
    · subst t
      by_cases hl0 : l = 0
      · subst l
        simp [bootstrapNodeSize, bootstrapUpAt, bootstrapDownAt, seedNodeSize]
      · by_cases hl1 : l = 1
        · subst l
          rw [if_pos (by omega : 1 < d)]
          exact (seed_stage_three_top_count d hd).symm
        · by_cases hl2 : l = 2
          · subst l
            simp [bootstrapNodeSize, bootstrapUpAt, bootstrapDownAt, seedNodeSize]
          · by_cases hl3 : l = 3
            · subst l
              simp [bootstrapNodeSize, bootstrapUpAt, bootstrapDownAt,
                seedStageThreeBottomSize, seedBottomDown2]
            · have hpred : l - 1 ≠ 0 := by omega
              simp [bootstrapNodeSize, bootstrapUpAt, bootstrapDownAt,
                seedNodeSize, hl0, hl1, hl2, hl3, hpred]
    · have ht0 : t = 0 ∨ t = 1 := by omega
      rcases ht0 with rfl | rfl
      · simpa [bootstrapNodeSize, bootstrapUpAt, bootstrapDownAt] using
          seed_transition_zero d (by omega) l
      · simpa [bootstrapNodeSize, bootstrapUpAt, bootstrapDownAt] using
          seed_transition_one d (by omega) l

noncomputable def candidateBootstrapPlacement (d : Nat) (hd : 14 ≤ d)
    (t : Nat) (ht : t ≤ 3) : Chvatal.Placement 64 d where
  regs := Chvatal.wireSets (candidateBootstrapFlowSizes d hd) t
  disjoint := by
    intro a b hne
    exact Chvatal.wireSets_disjoint (candidateBootstrapFlowSizes d hd) ht a b hne
  complete := by
    intro w
    exact Chvatal.wireSets_complete (candidateBootstrapFlowSizes d hd) ht w

theorem candidateBootstrapPlacement_card (d : Nat) (hd : 14 ≤ d)
    (t : Nat) (ht : t ≤ 3) (b : Chvatal.KBag 64 d) :
    ((candidateBootstrapPlacement d hd t ht).regs b).card = bootstrapNodeSize d b.l t := by
  exact Chvatal.wireSets_card (candidateBootstrapFlowSizes d hd) ht b

/-- The first-level seed counts fit the existing scaled two-round node
geometry exactly: 2^43 rows and a power-of-two column count. -/
theorem candidateSeed_levelOne_geometry (d : Nat) (hd : 14 ≤ d) :
    Nonempty (Chvatal.NodeGeom (seedRootDown d)
      (seedLevelOneUp d) (seedLevelOneDown d)) := by
  have hs : 0 ≤ 6 * d - 28 := by omega
  refine Chvatal.nodeGeom_of_template (6 * d - 28) (2 ^ 22) 32 65535
    (by norm_num) (by norm_num) (by norm_num) (Or.inr ?_)
    (seedRootDown d) (seedLevelOneUp d) (seedLevelOneDown d) ?_ ?_ ?_ ?_
  · norm_num
  · unfold seedRootDown
    rw [show 6 * d - 6 = (6 * d - 28) + 22 by omega, pow_add]
  · unfold seedLevelOneUp
    rw [show 6 * d - 22 = (6 * d - 28) + 6 by omega, pow_add]
    norm_num <;> ring
  · unfold seedLevelOneDown
    rw [show 6 * d - 12 = (6 * d - 28) + 16 by omega, pow_add]
    norm_num only [show (2 : Nat) ^ 16 = 65536 by norm_num]
    omega
  · have he : 63 < 6 * d - 6 := by omega
    unfold seedRootDown
    exact Nat.pow_lt_pow_right (by norm_num) he

/-- An actual root network realizes the stage-zero seed split, with the
existing constant root depth bound. -/
theorem candidateSeed_root_nodeGood (d : Nat) (hd : 14 ≤ d) :
    ∃ net : ComparatorNetwork (seedRootInput d),
      Chvatal.NodeGood 0 (seedRootInput d) 0 (seedRootDown d) net := by
  have hdown : seedRootDown d = 64 ^ (d - 1) := by
    unfold seedRootDown
    rw [Chvatal.p64 (d - 1)]
    congr 1
    omega
  exact Chvatal.nodeGood_root d hd _ _ _ (by simp [seedRootInput]) rfl hdown

/-- The stage-one node network is supplied by the proved two-round separator
theorem, and has the candidate seed's exact up/down sizes. -/
theorem candidateSeed_levelOne_nodeGood (d : Nat) (hd : 14 ≤ d) :
    ∃ net : ComparatorNetwork (seedRootDown d),
      Chvatal.NodeGood 1 (seedRootDown d) (seedLevelOneUp d)
        (seedLevelOneDown d) net := by
  obtain ⟨G⟩ := candidateSeed_levelOne_geometry d hd
  exact Chvatal.nodeGood_geom Chvatal.twoRoundSeparatorExists 1
    (seedRootDown d) (seedLevelOneUp d) (seedLevelOneDown d) (by omega) G

/-! At stage two, both special frontier bags retain valid separator
geometries after extracting their common power-of-two scale. -/

theorem candidateBootstrap_top_geometry (d : Nat) (hd : 14 ≤ d) :
    Nonempty (Chvatal.NodeGeom (bootstrapNodeSize d 0 2) 0 (seedTopDown2 d)) := by
  have ha : bootstrapNodeSize d 0 2 = 2 ^ (6 * d - 22) * 64 := by
    calc
      bootstrapNodeSize d 0 2 = 64 * seedLevelOneUp d := by
        simp [bootstrapNodeSize, seedNodeSize]
      _ = 64 * 2 ^ (6 * d - 22) := by rfl
      _ = 2 ^ (6 * d - 22) * 64 := Nat.mul_comm _ _
  have hu : 0 = 2 * (2 ^ (6 * d - 22) * 0) := by simp
  have hdn : seedTopDown2 d = 2 ^ (6 * d - 22) * 1 := by
    simp [seedTopDown2]
  have hbig : 2 ^ 63 < bootstrapNodeSize d 0 2 := by
    rw [ha]
    have he : 63 < 6 * d - 22 + 6 := by omega
    have hp : 2 ^ 63 < 2 ^ (6 * d - 22 + 6) :=
      Nat.pow_lt_pow_right (by norm_num) he
    have heq : 2 ^ (6 * d - 22 + 6) = 2 ^ (6 * d - 22) * 64 := by
      rw [pow_add]
      norm_num
    rw [← heq]
    exact hp
  exact Chvatal.nodeGeom_of_template (6 * d - 22) 64 0 1 (by norm_num)
    (by norm_num) (by norm_num) (Or.inl rfl)
    (bootstrapNodeSize d 0 2) 0 (seedTopDown2 d) ha hu hdn hbig

theorem candidateBootstrap_bottom_geometry (d : Nat) (hd : 14 ≤ d) :
    Nonempty (Chvatal.NodeGeom (bootstrapNodeSize d 2 2)
      (seedBottomUp2 d) (seedBottomDown2 d)) := by
  have ha : bootstrapNodeSize d 2 2 = 2 ^ (6 * d - 29) * 131070 := by
    calc
      bootstrapNodeSize d 2 2 = seedLevelOneDown d := by
        simp [bootstrapNodeSize, seedNodeSize]
      _ = 65535 * 2 ^ (6 * d - 28) := seed_down_as_common_mass d hd
      _ = 2 ^ (6 * d - 29) * 131070 := by
        rw [show 6 * d - 28 = 1 + (6 * d - 29) by omega, pow_add]
        norm_num
        ring
  have hu : seedBottomUp2 d = 2 * (2 ^ (6 * d - 29) * 255) := by
    calc
      seedBottomUp2 d = 255 * 2 ^ (6 * d - 28) := rfl
      _ = 2 * (2 ^ (6 * d - 29) * 255) := by
        rw [show 6 * d - 28 = 1 + (6 * d - 29) by omega, pow_add]
        norm_num
        ring
  have hdn : seedBottomDown2 d = 2 ^ (6 * d - 29) * 2040 := by
    calc
      seedBottomDown2 d = 1020 * 2 ^ (6 * d - 28) :=
        seed_bottom_down_as_common_mass d hd
      _ = 2 ^ (6 * d - 29) * 2040 := by
        rw [show 6 * d - 28 = 1 + (6 * d - 29) by omega, pow_add]
        norm_num
        ring
  have hbig : 2 ^ 63 < bootstrapNodeSize d 2 2 := by
    rw [ha]
    have hx : 63 < 6 * d - 29 + 16 := by omega
    have hp : 2 ^ 63 < 2 ^ (6 * d - 29 + 16) :=
      Nat.pow_lt_pow_right (by norm_num) hx
    have hc : 2 ^ 16 ≤ 131070 := by norm_num
    have hm := Nat.mul_le_mul_left (2 ^ (6 * d - 29)) hc
    have heq : 2 ^ (6 * d - 29 + 16) = 2 ^ (6 * d - 29) * 2 ^ 16 := by
      rw [pow_add]
    have hp' : 2 ^ (6 * d - 29 + 16) ≤ 2 ^ (6 * d - 29) * 131070 := by
      rw [heq]
      exact hm
    exact lt_of_lt_of_le hp hp'
  have hm' : 131070 = 2 * 255 + 64 * 2040 := by norm_num
  have hf0 : 4095 * 131070 ≤ 255 * 2 ^ 37 := by norm_num
  exact Chvatal.nodeGeom_of_template (6 * d - 29) 131070 255 2040 hm'
    (by norm_num) (by norm_num) (Or.inr hf0)
    (bootstrapNodeSize d 2 2) (seedBottomUp2 d) (seedBottomDown2 d)
    ha hu hdn hbig

theorem candidateBootstrap_stageTwo_nodeGood (d : Nat) (hd : 14 ≤ d) :
    (∃ net : ComparatorNetwork (bootstrapNodeSize d 0 2),
      Chvatal.NodeGood 2 (bootstrapNodeSize d 0 2) 0 (seedTopDown2 d) net) ∧
    (∃ net : ComparatorNetwork (bootstrapNodeSize d 2 2),
      Chvatal.NodeGood 2 (bootstrapNodeSize d 2 2) (seedBottomUp2 d)
        (seedBottomDown2 d) net) := by
  constructor
  · obtain ⟨G⟩ := candidateBootstrap_top_geometry d hd
    exact Chvatal.nodeGood_geom Chvatal.twoRoundSeparatorExists 2 _ _ _ (by omega) G
  · obtain ⟨G⟩ := candidateBootstrap_bottom_geometry d hd
    exact Chvatal.nodeGood_geom Chvatal.twoRoundSeparatorExists 2 _ _ _ (by omega) G

/-- Every seed node that sends a nonempty block has a local separator network
with exactly its assigned cardinality and flow parameters. This is the local
network-provider interface needed before proving the seed's rank invariant. -/
theorem candidateSeed_nodeGood_exists (d : Nat) (hd : 14 ≤ d) (t : Nat)
    (ht : t < 2) (b : Chvatal.KBag 64 d)
    (hdown : 0 < seedDownAt d b.l t) :
    ∃ net : ComparatorNetwork (seedNodeSize d b.l t),
      Chvatal.NodeGood t (seedNodeSize d b.l t) (seedUpAt d b.l t)
        (seedDownAt d b.l t) net := by
  by_cases ht0 : t = 0
  · subst t
    have hl : b.l = 0 := by
      by_contra hne
      simp [seedDownAt, hne] at hdown
    have hx : b.x = 0 := by
      have := b.hx
      simpa [hl] using this
    have hb : b = Chvatal.KBag.root 64 d := by
      apply Chvatal.KBag.ext <;> simp [Chvatal.KBag.root, hl, hx]
    subst b
    obtain ⟨net, hnet⟩ := candidateSeed_root_nodeGood d hd
    exact ⟨net, by simpa [seedNodeSize, seedUpAt, seedDownAt, seedRootInput] using hnet⟩
  · have ht1 : t = 1 := by omega
    subst t
    have hl : b.l = 1 := by
      by_contra hne
      simp [seedDownAt, hne] at hdown
    obtain ⟨net, hnet⟩ := candidateSeed_levelOne_nodeGood d hd
    rw [hl]
    exact ⟨net, by simpa [seedNodeSize, seedUpAt, seedDownAt] using hnet⟩

/-! ### Root-to-level-one outsider base case -/

/-- The root's first fan-out satisfies the seed outsider budget. Since the
input root owns every key, native-child occupancy is exact and the root-tail
term is zero; only the two boundary errors of its `NodeSpec` remain. -/
theorem candidateSeed_root_child_outsider_bound (d : Nat) (hd : 14 ≤ d)
    (nets : Nat → (b : Chvatal.KBag 64 d) → (n : Nat) → ComparatorNetwork n)
    (v : Equiv.Perm (Fin (64 ^ d)))
    (hspec : Chvatal.NodeSpec (seedRootInput d) 0 (seedRootDown d)
      (nets 0 (Chvatal.KBag.root 64 d) (seedRootInput d))
      (Chvatal.specEB 0 (seedRootInput d)) (Chvatal.specJmax 0) Chvatal.eps)
    (j : Fin 64) :
    (((Chvatal.KBag.root 64 d).child j.val j.isLt (by simp [Chvatal.KBag.root]; omega)).strangers 1 id
      (Chvatal.fromParentK (candidateSeedFlowSizes d hd) nets v 0
        ((Chvatal.KBag.root 64 d).child j.val j.isLt (by simp [Chvatal.KBag.root]; omega))) : ℝ) ≤
      Chvatal.paperRootEpsB * (64 : ℝ) ^ d := by
  let F := candidateSeedFlowSizes d hd
  let q := Chvatal.KBag.root 64 d
  have hq0 : q.l = 0 := by rfl
  have hq : q.l < d := by rw [hq0]; omega
  have hsize : F.a q.l 0 = seedRootInput d := by
    simp [F, candidateSeedFlowSizes, q, hq0, seedNodeSize, seedRootInput]
  have hup : F.up q.l 0 = 0 := by simp [F, candidateSeedFlowSizes, q, hq0, seedUpAt]
  have hdown : F.down q.l 0 = seedRootDown d := by
    simp [F, candidateSeedFlowSizes, q, hq0, seedDownAt]
  have hregs : (Chvatal.execPlacement F nets v 0 (by omega)).regs q = Finset.univ := by
    rw [Chvatal.execPlacement]
    change (Chvatal.wireSets F 0 q).image (Chvatal.X F nets v 0) = _
    rw [show Chvatal.wireSets F 0 q = Finset.univ by simp [Chvatal.wireSets, q]]
    change Finset.univ.image v = Finset.univ
    exact Finset.image_univ_of_surjective v.surjective
  have hM : ∀ j' : Fin 64,
      ((((Chvatal.execPlacement F nets v 0 (by omega)).regs q).filter fun κ =>
        (q.child j'.val j'.isLt hq).Native κ id).card : ℝ) ≤ F.down q.l 0 := by
    intro j'
    rw [hregs]
    have hc := Chvatal.native_card (br := 64) (d := d) (by norm_num)
      (q.child j'.val j'.isLt hq)
    have hlevel : (q.child j'.val j'.isLt hq).l = 1 := by
      change q.l + 1 = 1
      rw [hq0]
    have hp64 : seedRootDown d = 64 ^ (d - 1) := by
      unfold seedRootDown
      rw [Chvatal.p64 (d - 1)]
      congr 1
      omega
    rw [hlevel] at hc
    rw [hdown, hp64]
    exact_mod_cast (le_of_eq hc)
  have hrootStrangers : q.strangers 1 id
      ((Chvatal.execPlacement F nets v 0 (by omega)).regs q) = 0 := by
    exact Chvatal.KBag.strangers_eq_zero_of_lt_order q 1 id _ (by norm_num)
      (by norm_num) (by simpa [q, Chvatal.KBag.root])
  have hpos : (F.up q.l 0 : ℝ) / 2 ≤
      (q.strangers 1 id ((Chvatal.execPlacement F nets v 0 (by omega)).regs q) : ℝ) := by
    rw [hup, hrootStrangers]
    norm_num
  have hcard : (Chvatal.wireSets F 0 q).card = seedRootInput d := by
    rw [Chvatal.wireSets_card F (by omega), hsize]
  have hspec' : Chvatal.NodeSpec (Chvatal.wireSets F 0 q).card (F.up q.l 0)
      (F.down q.l 0) (nets 0 q (Chvatal.wireSets F 0 q).card)
      (Chvatal.specEB 0 (F.a q.l 0)) (Chvatal.specJmax (F.up q.l 0)) Chvatal.eps := by
    rw [hcard, hsize, hup, hdown]
    simpa [q, hq0] using hspec
  have hbad := Chvatal.bad_send0_real F nets v 0 (by omega) q hq j
    (Chvatal.specEB 0 (F.a q.l 0)) (Chvatal.specJmax (F.up q.l 0)) Chvatal.eps 0
    (by norm_num) hspec' (by simpa using hM) (by simpa using hpos)
  have heps : Chvatal.specEB 0 (F.a q.l 0) =
      Chvatal.paperRootEpsB * (64 : ℝ) ^ d / 2 := by
    simp [Chvatal.specEB, F, candidateSeedFlowSizes, q, hq0, seedNodeSize, seedRootInput]
  rw [hup, hrootStrangers, heps] at hbad
  calc
    _ ≤ 2 * (Chvatal.paperRootEpsB * (64 : ℝ) ^ d / 2) := by simpa using hbad
    _ = Chvatal.paperRootEpsB * (64 : ℝ) ^ d := by ring

/-! The explicit root error also fits the tapered stage-one budget. -/
theorem candidateSeed_root_child_tapered_budget (d : Nat) (hd : 14 ≤ d)
    (nets : Nat → (b : Chvatal.KBag 64 d) → (n : Nat) → ComparatorNetwork n)
    (v : Equiv.Perm (Fin (64 ^ d)))
    (hspec : Chvatal.NodeSpec (seedRootInput d) 0 (seedRootDown d)
      (nets 0 (Chvatal.KBag.root 64 d) (seedRootInput d))
      (Chvatal.specEB 0 (seedRootInput d)) (Chvatal.specJmax 0) Chvatal.eps)
    (j : Fin 64) :
    (((Chvatal.KBag.root 64 d).child j.val j.isLt
      (by simp [Chvatal.KBag.root]; omega)).strangers 1 id
      (Chvatal.fromParentK (candidateSeedFlowSizes d hd) nets v 0
        ((Chvatal.KBag.root 64 d).child j.val j.isLt
          (by simp [Chvatal.KBag.root]; omega))) : ℝ) ≤
      (Tapered945.mu : Rat) * candidateReferenceCapacity d 1 1 := by
  have hbase := candidateSeed_root_child_outsider_bound d hd nets v hspec j
  have hconst : Chvatal.paperRootEpsB * 64 ≤ (Tapered945.mu : ℝ) := by
    have hroot := Chvatal.paperRootEpsB_le_epsStar
    have hmu : Chvatal.invMu ≤ (Tapered945.mu : ℝ) := by
      norm_num [Chvatal.invMu, Tapered945.mu]
    norm_num at hroot ⊢
    nlinarith
  have hpow : (64 : ℝ) ^ d = 64 * (64 : ℝ) ^ (d - 1) := by
    have he : d = (d - 1) + 1 := by omega
    calc
      (64 : ℝ) ^ d = (64 : ℝ) ^ ((d - 1) + 1) :=
        congrArg (fun k : Nat => (64 : ℝ) ^ k) he
      _ = (64 : ℝ) ^ (d - 1) * 64 := by rw [pow_succ]
      _ = 64 * (64 : ℝ) ^ (d - 1) := by ring
  have hcap : candidateReferenceCapacity d 1 1 = (64 : Rat) ^ (d - 1) := by
    unfold candidateReferenceCapacity candidateCapacityExponent
    have hd' : d = (d - 1) + 1 := by omega
    rw [hd']
    have he : 6 * ((d - 1) + 1) + 6 * 1 - 4 * 1 - 8 = 6 * (d - 1) := by omega
    rw [he, pow_mul]
    norm_num
  calc
    _ ≤ Chvatal.paperRootEpsB * (64 : ℝ) ^ d := hbase
    _ = (Chvatal.paperRootEpsB * 64) * (64 : ℝ) ^ (d - 1) := by rw [hpow]; ring
    _ ≤ (Tapered945.mu : ℝ) * (64 : ℝ) ^ (d - 1) :=
      mul_le_mul_of_nonneg_right hconst (by positivity)
    _ = (Tapered945.mu : Rat) * candidateReferenceCapacity d 1 1 := by
      rw [hcap]
      norm_cast

end Tapered945
