import D2RankAlignment
import D2ScheduleReserve
import D2StaticAddressPartition

set_option maxHeartbeats 500000

open scoped BigOperators

namespace Chvatal.D2Reserve

open Chvatal.D2RankAlignment

/-- Extend the eight cumulative D2 child boundaries to a total function on
Nat, using the total mass after the final child. -/
def d2FlowRankBoundary (sizes : Fin 8 → Nat) (i : Nat) : Nat :=
  if h : i < 8 then d2FlowPosition sizes ⟨i, h⟩ else d2FlowTotal sizes

theorem d2FlowRankBoundary_zero (sizes : Fin 8 → Nat) :
    d2FlowRankBoundary sizes 0 = 0 := by
  simp [d2FlowRankBoundary, d2FlowPosition_zero]

theorem d2FlowRankBoundary_end (sizes : Fin 8 → Nat) :
    d2FlowRankBoundary sizes 8 = d2FlowTotal sizes := by
  simp [d2FlowRankBoundary]

theorem d2FlowRankBoundary_succ (sizes : Fin 8 → Nat) (i : Nat) (hi : i < 8) :
    d2FlowRankBoundary sizes (i + 1) =
      d2FlowRankBoundary sizes i + sizes ⟨i, hi⟩ := by
  by_cases hlt : i < 7
  · have hnext : i + 1 < 8 := by omega
    simp [d2FlowRankBoundary, hi, hnext]
    rw [d2FlowPosition_succ sizes i hlt]
  · have heq : i = 7 := by omega
    subst i
    have hlast := d2FlowPosition_last_end sizes
    simpa [d2FlowRankBoundary] using hlast.symm

theorem d2FlowRankBoundary_mono (sizes : Fin 8 → Nat) :
    ∀ i < 8, d2FlowRankBoundary sizes i ≤ d2FlowRankBoundary sizes (i + 1) := by
  intro i hi
  rw [d2FlowRankBoundary_succ sizes i hi]
  exact Nat.le_add_right _ _

/-- A finite set of size equal to the total child-deficit mass can be partitioned
into the eight abstract deficit rank intervals. This is not the sender's wire
bag when its own deficit `G` is positive; that bag has size `total-G`. -/
theorem d2Flow_rankedChildPartition {n : Nat} (s : Finset (Fin n))
    (sizes : Fin 8 → Nat) (hcard : s.card = d2FlowTotal sizes) :
    Finset.univ.biUnion (fun j : Fin 8 =>
      Chvatal.blockOf s (d2FlowRankBoundary sizes j.val)
        (d2FlowRankBoundary sizes (j.val + 1))) = s := by
  apply Chvatal.D2StaticAddressPartition.ranked_ports_biUnion_eq
    s (d2FlowRankBoundary sizes)
  · exact d2FlowRankBoundary_zero sizes
  · rw [d2FlowRankBoundary_end, hcard]
  · exact d2FlowRankBoundary_mono sizes

/-- Each abstract child-deficit rank interval has exactly its corresponding
flow size. -/
theorem d2Flow_rankedChildWidth {n : Nat} (s : Finset (Fin n))
    (sizes : Fin 8 → Nat) (hcard : s.card = d2FlowTotal sizes) (j : Fin 8) :
    (Chvatal.blockOf s (d2FlowRankBoundary sizes j.val)
      (d2FlowRankBoundary sizes (j.val + 1))).card = sizes j := by
  have hend : d2FlowRankBoundary sizes 8 = s.card := by
    rw [d2FlowRankBoundary_end, hcard]
  have hwidth := Chvatal.D2StaticAddressPartition.ranked_ports_card
    s (d2FlowRankBoundary sizes) hend (d2FlowRankBoundary_mono sizes)
    j.val j.isLt
  rw [hwidth, d2FlowRankBoundary_succ sizes j.val j.isLt]
  simp

/-- The ideal two-front child mass for one actual D2 flow interval. -/
def d2FlowTwoFrontMass (sizes : Fin 8 → Nat) (left right : Nat)
    (j : Fin 8) : Nat :=
  prefixIntervalMass left
      (d2FlowRankBoundary sizes j.val)
      (d2FlowRankBoundary sizes (j.val + 1)) +
    suffixIntervalMass right
      (d2FlowRankBoundary sizes j.val)
      (d2FlowRankBoundary sizes (j.val + 1))

/-- The D2 deficit update is exactly the low-prefix/high-suffix overlap of its
concrete child interval. This identifies the abstract profile with the flow
transition geometry before any separator-error assumptions enter. -/
theorem d2LocalChildDeficitUpdate_eq_d2FlowTwoFrontMass
    (sizes : Fin 8 → Nat) (left right : Nat) (j : Fin 8) :
    d2LocalChildDeficitUpdate .mid (d2FlowPosition sizes j) (sizes j)
        left right = d2FlowTwoFrontMass sizes left right j := by
  have hnext := d2FlowRankBoundary_succ sizes j.val (by omega)
  have hpos : d2FlowRankBoundary sizes j.val = d2FlowPosition sizes j := by
    simp [d2FlowRankBoundary, j.isLt]
  have hnext' : d2FlowRankBoundary sizes (j.val + 1) =
      d2FlowPosition sizes j + sizes j := by
    rw [hnext, hpos]
  rw [d2FlowTwoFrontMass, hpos, hnext']
  simp [d2LocalChildDeficitUpdate, d2LeftCut, d2RightCut,
    prefixIntervalMass_eq_left_front_overlap,
    suffixIntervalMass_eq_right_front_overlap]

/-- Across the eight real D2 child intervals, the local mid-role deficits
exactly partition the two exposed ends of the parent: the low front of length
`left` and the high front beginning at `right`. In particular, this total is
charged once, rather than once per child. -/
theorem d2Flow_child_deficits_sum
    (sizes : Fin 8 → Nat) (left right : Nat)
    (hleft : left ≤ right) (hright : right ≤ d2FlowTotal sizes) :
    (∑ j : Fin 8,
      d2LocalChildDeficitUpdate .mid (d2FlowPosition sizes j) (sizes j)
        left right) = left + (d2FlowTotal sizes - right) := by
  let total := d2FlowTotal sizes
  have hfronts : left ≤ total - (total - right) := by
    dsimp [total]
    omega
  have hgeneric := low_high_frontier_partition total left (total - right)
    (d2FlowRankBoundary sizes) 8
    (d2FlowRankBoundary_zero sizes) (d2FlowRankBoundary_end sizes)
    (d2FlowRankBoundary_mono sizes)
    (by dsimp [total]; omega) (Nat.sub_le total right) hfronts
  have hcomp : total - (total - right) = right := by
    dsimp [total]
    omega
  rw [hcomp] at hgeneric
  let profile : Nat → Nat := fun i =>
    prefixIntervalMass left (d2FlowRankBoundary sizes i)
        (d2FlowRankBoundary sizes (i + 1)) +
      suffixIntervalMass right (d2FlowRankBoundary sizes i)
        (d2FlowRankBoundary sizes (i + 1))
  have hgeneric' : (∑ i ∈ Finset.range 8, profile i) =
      left + (total - right) := by
    simpa [profile] using hgeneric.1
  have hmassProfile :
      (∑ j : Fin 8, profile j.val) = left + (total - right) := by
    rw [Fin.sum_univ_eq_sum_range (fun i : Nat => profile i)]
    exact hgeneric'
  have hmass :
      (∑ j : Fin 8, d2FlowTwoFrontMass sizes left right j) =
        left + (total - right) := by
    simpa [profile, d2FlowTwoFrontMass] using hmassProfile
  calc
    _ = ∑ j : Fin 8, d2FlowTwoFrontMass sizes left right j := by
      apply Finset.sum_congr rfl
      intro j hj
      exact d2LocalChildDeficitUpdate_eq_d2FlowTwoFrontMass sizes left right j
    _ = left + (total - right) := hmass

/-- Every ordinary D2 role writes its child root deficit to the low-prefix
plus high-suffix mass on that child's actual interval. -/
theorem d2FlowStage_regular_child_deficit_eq_rank_mass
    {active : Nat → Bool} {role : Nat → D2Role}
    {quota : Nat → D2Role → Nat} {h i G low high : Nat}
    (children : Fin 8 → D2FlowTree h)
    (ha : active i = true)
    (hr : role i = .topRise ∨ role i = .mid ∨ role i = .botDesc)
    (j : Fin 8) :
    d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowStage active role quota (h + 1) i
          (.node G low high children)) j) =
      d2FlowTwoFrontMass
        (fun k => d2FlowTreeRootDeficit (children k))
        (low + quota i (role i) / 2)
        (d2FlowTotal (fun k => d2FlowTreeRootDeficit (children k)) -
          high - quota i (role i) / 2) j := by
  rw [d2FlowStage_regular_child_deficit children ha hr j,
    d2FlowCutChild_deficit_eq_update]
  exact d2LocalChildDeficitUpdate_eq_d2FlowTwoFrontMass
    (fun k => d2FlowTreeRootDeficit (children k))
    (low + quota i (role i) / 2)
    (d2FlowTotal (fun k => d2FlowTreeRootDeficit (children k)) -
      high - quota i (role i) / 2) j

/-- If the sender's pre-stage deficit fits inside the low frontier, then its
single-prefix exact-rank mass in each child interval is bounded by that
child's two-front post-stage deficit. This is the comparison needed to use a
single-prefix false-mass provider with the flow's larger two-front reserves.
-/
theorem d2FlowStage_regular_child_dominates_parent_prefix_mass
    {active : Nat → Bool} {role : Nat → D2Role}
    {quota : Nat → D2Role → Nat} {h i G low high : Nat}
    (children : Fin 8 → D2FlowTree h)
    (ha : active i = true)
    (hr : role i = .topRise ∨ role i = .mid ∨ role i = .botDesc)
    (hbalance : G = low + high)
    (hfront : high ≤ quota i (role i) / 2)
    (j : Fin 8) :
    prefixIntervalMass G
        (d2FlowRankBoundary
        (fun k => d2FlowTreeRootDeficit (children k)) j.val)
        (d2FlowRankBoundary
        (fun k => d2FlowTreeRootDeficit (children k)) (j.val + 1)) ≤
      d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowStage active role quota (h + 1) i
            (.node G low high children)) j) := by
  have hleft : G ≤ low + quota i (role i) / 2 := by omega
  rw [d2FlowStage_regular_child_deficit_eq_rank_mass children ha hr j]
  unfold d2FlowTwoFrontMass
  exact (prefixIntervalMass_mono hleft).trans
    (Nat.le_add_right _ _)

/-- Across all eight child intervals, the total amount by which a one-prefix
reference can exceed the two-front reserves is at most the part of its mass
that lies beyond the reserved low prefix. The high suffix only decreases this
overrun. -/
theorem d2FlowTwoFront_prefix_excess_sum_le
    (sizes : Fin 8 → Nat) (G left right : Nat)
    (hG : G ≤ d2FlowTotal sizes) :
    (Finset.univ.sum fun j : Fin 8 =>
      prefixIntervalMass G (d2FlowRankBoundary sizes j.val)
        (d2FlowRankBoundary sizes (j.val + 1)) -
      d2FlowTwoFrontMass sizes left right j) ≤
      G - min G left := by
  let cuts := d2FlowRankBoundary sizes
  have hzero : cuts 0 = 0 := d2FlowRankBoundary_zero sizes
  have hend : cuts 8 = d2FlowTotal sizes := d2FlowRankBoundary_end sizes
  have hmono : ∀ i < 8, cuts i ≤ cuts (i + 1) :=
    d2FlowRankBoundary_mono sizes
  have hleftTotal : min G left ≤ d2FlowTotal sizes :=
    le_trans (Nat.min_le_left _ _) hG
  have hpart (H : Nat) (hH : H ≤ d2FlowTotal sizes) :
      (Finset.univ.sum fun j : Fin 8 =>
        prefixIntervalMass H (cuts j.val) (cuts (j.val + 1))) = H := by
    rw [Fin.sum_univ_eq_sum_range
      (fun i : Nat => prefixIntervalMass H (cuts i) (cuts (i + 1)))]
    rw [prefixIntervalMass_partition H cuts 8 (d2FlowTotal sizes)
      hzero hend hmono]
    simp [prefixIntervalMass, hH]
  have hprefixMono (j : Fin 8) :
      prefixIntervalMass (min G left) (cuts j.val) (cuts (j.val + 1)) ≤
        prefixIntervalMass G (cuts j.val) (cuts (j.val + 1)) :=
    prefixIntervalMass_mono (Nat.min_le_left _ _)
  have hdiffsum :
      (Finset.univ.sum fun j : Fin 8 =>
        prefixIntervalMass G (cuts j.val) (cuts (j.val + 1)) -
        prefixIntervalMass (min G left) (cuts j.val) (cuts (j.val + 1))) =
      G - min G left := by
    rw [Finset.sum_tsub_distrib Finset.univ (by
      intro j hj
      exact hprefixMono j)]
    rw [hpart G hG, hpart (min G left) hleftTotal]
  have hprefixLeReserve (j : Fin 8) :
      prefixIntervalMass (min G left) (cuts j.val) (cuts (j.val + 1)) ≤
        d2FlowTwoFrontMass sizes left right j := by
    unfold d2FlowTwoFrontMass cuts
    exact (prefixIntervalMass_mono (Nat.min_le_right _ _)).trans
      (Nat.le_add_right _ _)
  calc
    _ ≤ Finset.univ.sum fun j : Fin 8 =>
        prefixIntervalMass G (cuts j.val) (cuts (j.val + 1)) -
          prefixIntervalMass (min G left) (cuts j.val) (cuts (j.val + 1)) := by
      apply Finset.sum_le_sum
      intro j hj
      exact Nat.sub_le_sub_left (hprefixLeReserve j) _
    _ = G - min G left := hdiffsum

/-- With the strict `G <= capacity/512` input reserve and the candidate
ordinary quota lower bound `quota >= 15*capacity/4096`, the unmatched
single-prefix mass is at most `capacity/8192`. -/
theorem d2FlowTwoFront_prefix_excess_le_capacity
    (G low quota capacity half : Nat)
    (hhalf : quota = 2 * half)
    (hdeficit : 512 * G ≤ capacity)
    (hquota : 15 * capacity ≤ 4096 * quota) :
    8192 * (G - min G (low + half)) ≤ capacity := by
  have hG : 8192 * G ≤ 16 * capacity := by nlinarith [hdeficit]
  have hhalfquota : 15 * capacity ≤ 8192 * half := by
    rw [hhalf] at hquota
    nlinarith [hquota]
  by_cases hsmall : G ≤ half
  · have hmin : min G (low + half) = G :=
      Nat.min_eq_left (by omega)
    rw [hmin]
    simp
  · have hmin : half ≤ min G (low + half) := by omega
    have hgap : G - min G (low + half) ≤ G - half := by omega
    have hGsplit : G = (G - half) + half := by omega
    rw [hGsplit] at hG
    have hraw : 8192 * (G - half) ≤ capacity := by
      nlinarith [hG, hhalfquota]
    nlinarith [hgap, hraw]

/-- Tolerant all-stage version of the unmatched-prefix estimate. -/
theorem d2FlowTwoFront_prefix_excess_le_tolerant_capacity
    (G low quota capacity half : Nat)
    (hhalf : quota = 2 * half)
    (hdeficit : 4096 * G ≤ 23 * capacity)
    (hquota : 15 * capacity ≤ 4096 * quota) :
    8192 * (G - min G (low + half)) ≤ 31 * capacity := by
  have hG : 8192 * G ≤ 46 * capacity := by nlinarith [hdeficit]
  have hhalfquota : 15 * capacity ≤ 8192 * half := by
    rw [hhalf] at hquota
    nlinarith [hquota]
  by_cases hsmall : G ≤ half
  · have hmin : min G (low + half) = G :=
      Nat.min_eq_left (by omega)
    rw [hmin]
    simp
  · have hmin : half ≤ min G (low + half) := by omega
    have hgap : G - min G (low + half) ≤ G - half := by omega
    have hGsplit : G = (G - half) + half := by omega
    rw [hGsplit] at hG
    have hraw : 8192 * (G - half) ≤ 31 * capacity := by
      nlinarith [hG, hhalfquota]
    nlinarith [hgap, hraw]

/-- If the sender capacity consists of 4096-by-64 tiles, the strict reserve
and ordinary quota lower bound leave at most 32 unmatched prefix units per
tile. -/
theorem d2FlowTwoFront_prefix_excess_le_tiles
    (G low quota capacity half tiles : Nat)
    (hcapacity : capacity = 262144 * tiles)
    (hhalf : quota = 2 * half)
    (hdeficit : 512 * G ≤ capacity)
    (hquota : 15 * capacity ≤ 4096 * quota) :
    G - min G (low + half) ≤ 32 * tiles := by
  have h := d2FlowTwoFront_prefix_excess_le_capacity
    G low quota capacity half hhalf hdeficit hquota
  rw [hcapacity] at h
  omega

/-- The actual all-stage tolerance `G <= 23*capacity/4096`, together with
the candidate quota floor, leaves at most 31 unmatched prefix units per
8192-unit flow tile. -/
theorem d2FlowTwoFront_prefix_excess_le_tolerant_tiles
    (G low quota capacity half tiles : Nat)
    (hcapacity : capacity = 8192 * tiles)
    (hhalf : quota = 2 * half)
    (hdeficit : 4096 * G ≤ 23 * capacity)
    (hquota : 15 * capacity ≤ 4096 * quota) :
    G - min G (low + half) ≤ 31 * tiles := by
  have h := d2FlowTwoFront_prefix_excess_le_tolerant_capacity
    G low quota capacity half hhalf hdeficit hquota
  rw [hcapacity] at h
  omega

/-- The 448 core error plus the 31-unit two-front overrun fits the
512-per-output-tile budget after the input tile count doubles. -/
theorem d2Flow_tolerant_profile_budget_doubles
    (tiles parentError : Nat)
    (hparent : parentError ≤ 512 * tiles) :
    parentError + 448 * tiles + 31 * tiles ≤ 512 * (2 * tiles) := by
  omega

/-- Stage form of the aggregate two-front comparison: the total positive
overrun of exact-prefix child masses above their post-stage deficit reserves
is bounded by the sender's unmatched prefix mass. -/
theorem d2FlowStage_regular_child_prefix_excess_sum_le
    {active : Nat → Bool} {role : Nat → D2Role}
    {quota : Nat → D2Role → Nat} {h i G low high : Nat}
    (children : Fin 8 → D2FlowTree h)
    (ha : active i = true)
    (hr : role i = .topRise ∨ role i = .mid ∨ role i = .botDesc)
    (hG : G ≤ d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j))) :
    (Finset.univ.sum fun j : Fin 8 =>
      prefixIntervalMass G
        (d2FlowRankBoundary
          (fun k => d2FlowTreeRootDeficit (children k)) j.val)
        (d2FlowRankBoundary
          (fun k => d2FlowTreeRootDeficit (children k)) (j.val + 1)) -
      d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowStage active role quota (h + 1) i
            (.node G low high children)) j)) ≤
      G - min G (low + quota i (role i) / 2) := by
  let sizes : Fin 8 → Nat := fun j => d2FlowTreeRootDeficit (children j)
  let left := low + quota i (role i) / 2
  let right := d2FlowTotal sizes - high - quota i (role i) / 2
  have hbase := d2FlowTwoFront_prefix_excess_sum_le sizes G left right
    (by simpa [sizes] using hG)
  simpa [sizes, left, right,
    d2FlowStage_regular_child_deficit_eq_rank_mass children ha hr] using hbase

/-- Convert a grouped local L1 transfer and a flow-reserve overrun estimate
into a one-sided bound on actual mass above the child reserves. -/
theorem grouped_mass_overrun_le_transfer_add_ideal_overrun
    (actual ideal reserve : Fin 8 → Nat) (transferError idealOverrun : Nat)
    (htransfer : (Finset.univ.sum fun j : Fin 8 =>
      countDistance (actual j) (ideal j)) ≤ transferError)
    (hideal : (Finset.univ.sum fun j : Fin 8 =>
      ideal j - reserve j) ≤ idealOverrun) :
    (Finset.univ.sum fun j : Fin 8 => actual j - reserve j) ≤
      transferError + idealOverrun := by
  calc
    _ ≤ Finset.univ.sum fun j : Fin 8 =>
        countDistance (actual j) (ideal j) + (ideal j - reserve j) := by
      apply Finset.sum_le_sum
      intro j hj
      unfold countDistance
      omega
    _ = (Finset.univ.sum fun j : Fin 8 =>
        countDistance (actual j) (ideal j)) +
          (Finset.univ.sum fun j : Fin 8 => ideal j - reserve j) := by
      rw [Finset.sum_add_distrib]
    _ ≤ transferError + idealOverrun := Nat.add_le_add htransfer hideal

/-- Summing the preceding identity identifies the entire child profile after
any active ordinary role with its concrete two-front rank-mass profile. -/
theorem d2FlowStage_regular_child_profile_sum
    {active : Nat → Bool} {role : Nat → D2Role}
    {quota : Nat → D2Role → Nat} {h i G low high : Nat}
    (children : Fin 8 → D2FlowTree h)
    (ha : active i = true)
    (hr : role i = .topRise ∨ role i = .mid ∨ role i = .botDesc) :
    (∑ j : Fin 8,
      d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowStage active role quota (h + 1) i
            (.node G low high children)) j)) =
    (∑ j : Fin 8,
      d2FlowTwoFrontMass
        (fun k => d2FlowTreeRootDeficit (children k))
        (low + quota i (role i) / 2)
        (d2FlowTotal (fun k => d2FlowTreeRootDeficit (children k)) -
          high - quota i (role i) / 2) j) := by
  apply Finset.sum_congr rfl
  intro j hj
  exact d2FlowStage_regular_child_deficit_eq_rank_mass children ha hr j

/-- Under the established balance, evenness, endpoint, and noncrossing gates,
the actual ordinary-stage rank-mass profile has exactly parent deficit plus
sender quota. -/
theorem d2FlowStage_regular_rank_profile_mass
    {active : Nat → Bool} {role : Nat → D2Role}
    {quota : Nat → D2Role → Nat} {h i G low high : Nat}
    (children : Fin 8 → D2FlowTree h)
    (ha : active i = true)
    (hr : role i = .topRise ∨ role i = .mid ∨ role i = .botDesc)
    (hbal : G = low + high)
    (heven : quota i (role i) % 2 = 0)
    (hleft : low + quota i (role i) / 2 ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)))
    (hright : high + quota i (role i) / 2 ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)))
    (hdisjoint : low + quota i (role i) / 2 ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) -
        high - quota i (role i) / 2) :
    (∑ j : Fin 8,
      d2FlowTwoFrontMass
        (fun k => d2FlowTreeRootDeficit (children k))
        (low + quota i (role i) / 2)
        (d2FlowTotal (fun k => d2FlowTreeRootDeficit (children k)) -
          high - quota i (role i) / 2) j) = G + quota i (role i) := by
  calc
    _ = ∑ j : Fin 8,
        d2FlowTreeRootDeficit
          (d2FlowTreeChild
            (d2FlowStage active role quota (h + 1) i
              (.node G low high children)) j) :=
      (d2FlowStage_regular_child_profile_sum children ha hr).symm
    _ = G + quota i (role i) :=
      d2FlowStage_regular_child_mass children ha hr hbal heven hleft hright hdisjoint

/-- The actual post-stage down-block widths, plus the two half-up ports,
partition the sender's allocation. This is the rank-interval conservation
identity needed to instantiate `ranked_ports_cover` on the sender's physical
wire set (whose cardinality is `total - G`, not `total`). -/
theorem d2FlowStage_regular_rank_port_conservation
    {active : Nat → Bool} {role : Nat → D2Role}
    {quota : Nat → D2Role → Nat} {h i G low high : Nat}
    (children : Fin 8 → D2FlowTree h)
    (ha : active i = true)
    (hr : role i = .topRise ∨ role i = .mid ∨ role i = .botDesc)
    (hbal : G = low + high)
    (heven : quota i (role i) % 2 = 0)
    (hleft : low + quota i (role i) / 2 ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)))
    (hright : high + quota i (role i) / 2 ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)))
    (hdisjoint : low + quota i (role i) / 2 ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) -
        high - quota i (role i) / 2) :
    quota i (role i) +
      (Finset.univ.sum fun j : Fin 8 =>
        d2FlowTreeRootDeficit (children j) -
          d2FlowTreeRootDeficit
            (d2FlowTreeChild
              (d2FlowStage active role quota (h + 1) i
                (.node G low high children)) j)) =
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G := by
  let sizes : Fin 8 → Nat := fun j => d2FlowTreeRootDeficit (children j)
  let post : Fin 8 → Nat := fun j => d2FlowTreeRootDeficit
    (d2FlowTreeChild
      (d2FlowStage active role quota (h + 1) i (.node G low high children)) j)
  have hmass : (Finset.univ.sum fun j : Fin 8 => post j) = G + quota i (role i) := by
    simpa [post] using d2FlowStage_regular_child_mass children ha hr hbal heven
      hleft hright hdisjoint
  have hle (j : Fin 8) : post j ≤ sizes j := by
    change d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowStage active role quota (h + 1) i (.node G low high children)) j) ≤
      d2FlowTreeRootDeficit (children j)
    rw [d2FlowStage_regular_child_deficit children ha hr j]
    exact d2FlowCutChild_le_native (Nat.le_refl _) (by omega)
  have hsplit :
      (Finset.univ.sum fun j : Fin 8 => sizes j - post j) +
        (Finset.univ.sum fun j : Fin 8 => post j) = d2FlowTotal sizes := by
    rw [← Finset.sum_add_distrib]
    unfold d2FlowTotal
    apply Finset.sum_congr rfl
    intro j hj
    exact Nat.sub_add_cancel (hle j)
  have hremaining :
      (Finset.univ.sum fun j : Fin 8 => sizes j - post j) +
        (G + quota i (role i)) = d2FlowTotal sizes := by
    rw [← hmass]
    exact hsplit
  change quota i (role i) +
      (Finset.univ.sum fun j : Fin 8 => sizes j - post j) =
        d2FlowTotal sizes - G
  omega

/-- Given the D2 conservation equation, an ordinary sender's physical rank
intervals cover its wire bag: a left half-up port, eight consecutive down
ports, and the right half-up port. -/
theorem d2FlowSenderRankPorts_cover
    {n : Nat} (s : Finset (Fin n)) (widths : Fin 8 → Nat)
    (pi total G : Nat)
    (hsender : s.card = total - G)
    (heven : pi % 2 = 0)
    (hconserve : pi + d2FlowTotal widths = total - G) :
    (Chvatal.blockOf s 0 (pi / 2) ∪
      ((Finset.univ.biUnion fun j : Fin 8 =>
        Chvatal.blockOf s
          (pi / 2 + d2FlowRankBoundary widths j.val)
          (pi / 2 + d2FlowRankBoundary widths (j.val + 1))) ∪
        Chvatal.blockOf s (s.card - pi / 2) s.card)) = s := by
  have hpi : pi = 2 * (pi / 2) := by omega
  have hfull : pi + d2FlowTotal widths = s.card := by
    rw [hsender]
    exact hconserve
  have hright : pi / 2 + d2FlowTotal widths = s.card - pi / 2 := by omega
  have hleftend : pi / 2 + d2FlowTotal widths ≤ s.card := by omega
  have hcard : pi / 2 + d2FlowTotal widths +
      (s.card - (pi / 2 + d2FlowTotal widths)) = s.card := by omega
  have hboundaryEnd : d2FlowRankBoundary widths 8 = d2FlowTotal widths :=
    d2FlowRankBoundary_end widths
  have hresult := Chvatal.D2StaticAddressPartition.ranked_ports_with_sides_cover
    s (d2FlowRankBoundary widths) (pi / 2)
    (d2FlowRankBoundary_zero widths) (d2FlowRankBoundary_mono widths) (by
      rw [hboundaryEnd]
      exact hcard)
  simpa [hboundaryEnd, hright] using hresult

/-- The grouped parent up-port is disjoint from every child down-port, and
distinct child down-ports are disjoint from one another. -/
theorem d2FlowSenderRankPorts_disjoint
    {n : Nat} (s : Finset (Fin n)) (widths : Fin 8 → Nat)
    (pi total G : Nat)
    (hsender : s.card = total - G)
    (heven : pi % 2 = 0)
    (hconserve : pi + d2FlowTotal widths = total - G) :
    Disjoint
      (Chvatal.blockOf s 0 (pi / 2) ∪
        Chvatal.blockOf s (s.card - pi / 2) s.card)
      (Finset.univ.biUnion fun j : Fin 8 =>
        Chvatal.blockOf s
          (pi / 2 + d2FlowRankBoundary widths j.val)
          (pi / 2 + d2FlowRankBoundary widths (j.val + 1))) ∧
      (∀ i j : Fin 8, i ≠ j →
        Disjoint
          (Chvatal.blockOf s
            (pi / 2 + d2FlowRankBoundary widths i.val)
            (pi / 2 + d2FlowRankBoundary widths (i.val + 1)))
          (Chvatal.blockOf s
            (pi / 2 + d2FlowRankBoundary widths j.val)
            (pi / 2 + d2FlowRankBoundary widths (j.val + 1)))) := by
  have hpi : pi = 2 * (pi / 2) := by omega
  have hfull : pi + d2FlowTotal widths = s.card := by
    rw [hsender]
    exact hconserve
  have hright : pi / 2 + d2FlowTotal widths = s.card - pi / 2 := by omega
  have hcard : pi / 2 + d2FlowTotal widths +
      (s.card - (pi / 2 + d2FlowTotal widths)) = s.card := by omega
  have hboundaryEnd : d2FlowRankBoundary widths 8 = d2FlowTotal widths :=
    d2FlowRankBoundary_end widths
  have hresult := Chvatal.D2StaticAddressPartition.ranked_ports_with_sides_disjoint
    s (d2FlowRankBoundary widths) (pi / 2)
    (d2FlowRankBoundary_mono widths) (by
      rw [hboundaryEnd]
      exact hcard)
  simpa [hboundaryEnd, hright] using hresult

/-- The preceding partition applies directly to every ordinary D2 stage
transition satisfying its cut gates. -/
theorem d2FlowStage_regular_sender_rank_ports_cover
    {active : Nat → Bool} {role : Nat → D2Role}
    {quota : Nat → D2Role → Nat} {h i G low high n : Nat}
    (children : Fin 8 → D2FlowTree h) (s : Finset (Fin n))
    (ha : active i = true)
    (hr : role i = .topRise ∨ role i = .mid ∨ role i = .botDesc)
    (hbal : G = low + high)
    (heven : quota i (role i) % 2 = 0)
    (hleft : low + quota i (role i) / 2 ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)))
    (hright : high + quota i (role i) / 2 ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)))
    (hdisjoint : low + quota i (role i) / 2 ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) -
        high - quota i (role i) / 2)
    (hsender : s.card = d2FlowTotal
      (fun j => d2FlowTreeRootDeficit (children j)) - G) :
    (Chvatal.blockOf s 0 (quota i (role i) / 2) ∪
      ((Finset.univ.biUnion fun j : Fin 8 =>
        Chvatal.blockOf s
          (quota i (role i) / 2 + d2FlowRankBoundary
            (fun k => d2FlowTreeRootDeficit (children k) -
              d2FlowTreeRootDeficit
                (d2FlowTreeChild (d2FlowStage active role quota (h + 1) i
                  (.node G low high children)) k)) j.val)
          (quota i (role i) / 2 + d2FlowRankBoundary
            (fun k => d2FlowTreeRootDeficit (children k) -
              d2FlowTreeRootDeficit
                (d2FlowTreeChild (d2FlowStage active role quota (h + 1) i
                  (.node G low high children)) k)) (j.val + 1))) ∪
        Chvatal.blockOf s (s.card - quota i (role i) / 2) s.card)) = s := by
  let widths : Fin 8 → Nat := fun j =>
    d2FlowTreeRootDeficit (children j) -
      d2FlowTreeRootDeficit
        (d2FlowTreeChild (d2FlowStage active role quota (h + 1) i
          (.node G low high children)) j)
  have hconserve : quota i (role i) + d2FlowTotal widths =
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G := by
    simpa [widths, d2FlowTotal] using
      d2FlowStage_regular_rank_port_conservation children ha hr hbal heven
        hleft hright hdisjoint
  have hcover := d2FlowSenderRankPorts_cover s widths
    (quota i (role i))
    (d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j))) G
    hsender heven hconserve
  simpa [widths] using hcover

/-- The same actual ordinary transition also gives pairwise disjoint sender
pieces when the two up ends are grouped as one parent destination. -/
theorem d2FlowStage_regular_sender_rank_ports_disjoint
    {active : Nat → Bool} {role : Nat → D2Role}
    {quota : Nat → D2Role → Nat} {h i G low high n : Nat}
    (children : Fin 8 → D2FlowTree h) (s : Finset (Fin n))
    (ha : active i = true)
    (hr : role i = .topRise ∨ role i = .mid ∨ role i = .botDesc)
    (hbal : G = low + high)
    (heven : quota i (role i) % 2 = 0)
    (hleft : low + quota i (role i) / 2 ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)))
    (hright : high + quota i (role i) / 2 ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)))
    (hdisjoint : low + quota i (role i) / 2 ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) -
        high - quota i (role i) / 2)
    (hsender : s.card = d2FlowTotal
      (fun j => d2FlowTreeRootDeficit (children j)) - G) :
    Disjoint
      (Chvatal.blockOf s 0 (quota i (role i) / 2) ∪
        Chvatal.blockOf s (s.card - quota i (role i) / 2) s.card)
      (Finset.univ.biUnion fun j : Fin 8 =>
        Chvatal.blockOf s
          (quota i (role i) / 2 + d2FlowRankBoundary
            (fun k => d2FlowTreeRootDeficit (children k) -
              d2FlowTreeRootDeficit
                (d2FlowTreeChild (d2FlowStage active role quota (h + 1) i
                  (.node G low high children)) k)) j.val)
          (quota i (role i) / 2 + d2FlowRankBoundary
            (fun k => d2FlowTreeRootDeficit (children k) -
              d2FlowTreeRootDeficit
                (d2FlowTreeChild (d2FlowStage active role quota (h + 1) i
                  (.node G low high children)) k)) (j.val + 1))) ∧
      (∀ j k : Fin 8, j ≠ k →
        Disjoint
          (Chvatal.blockOf s
            (quota i (role i) / 2 + d2FlowRankBoundary
              (fun q => d2FlowTreeRootDeficit (children q) -
                d2FlowTreeRootDeficit
                  (d2FlowTreeChild (d2FlowStage active role quota (h + 1) i
                    (.node G low high children)) q)) j.val)
            (quota i (role i) / 2 + d2FlowRankBoundary
              (fun q => d2FlowTreeRootDeficit (children q) -
                d2FlowTreeRootDeficit
                  (d2FlowTreeChild (d2FlowStage active role quota (h + 1) i
                    (.node G low high children)) q)) (j.val + 1)))
          (Chvatal.blockOf s
            (quota i (role i) / 2 + d2FlowRankBoundary
              (fun q => d2FlowTreeRootDeficit (children q) -
                d2FlowTreeRootDeficit
                  (d2FlowTreeChild (d2FlowStage active role quota (h + 1) i
                    (.node G low high children)) q)) k.val)
            (quota i (role i) / 2 + d2FlowRankBoundary
              (fun q => d2FlowTreeRootDeficit (children q) -
                d2FlowTreeRootDeficit
                  (d2FlowTreeChild (d2FlowStage active role quota (h + 1) i
                    (.node G low high children)) q)) (k.val + 1)))) := by
  let widths : Fin 8 → Nat := fun j =>
    d2FlowTreeRootDeficit (children j) -
      d2FlowTreeRootDeficit
        (d2FlowTreeChild (d2FlowStage active role quota (h + 1) i
          (.node G low high children)) j)
  have hconserve : quota i (role i) + d2FlowTotal widths =
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G := by
    simpa [widths, d2FlowTotal] using
      d2FlowStage_regular_rank_port_conservation children ha hr hbal heven
        hleft hright hdisjoint
  have hdisj := d2FlowSenderRankPorts_disjoint s widths
    (quota i (role i))
    (d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j))) G
    hsender heven hconserve
  simpa [widths] using hdisj

end Chvatal.D2Reserve
