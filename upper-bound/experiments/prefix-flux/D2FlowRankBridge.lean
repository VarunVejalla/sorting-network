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
