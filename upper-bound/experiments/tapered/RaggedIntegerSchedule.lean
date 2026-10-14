import AddressDebt
import CandidateFrontier
import Mathlib.Tactic

namespace Tapered945

open Chvatal

/-- One local integer split chosen for an address-dependent bag. -/
structure LocalIntegerFlow {d : Nat} (b : KBag 64 d) (C eta : Rat) (count : Nat) where
  up : Nat
  blocks : Fin 64 → Nat
  upEven : Even up
  upLe : up ≤ count
  upError : |(up : Rat) - addressUpAt b C| ≤ 1
  blockTotal : (∑ j, blocks j) = count - up
  blockError : ∀ j, |(blocks j : Rat) - addressDownAt b C j| ≤ 1 + 70 / 64

/-- If a bag has the reference occupancy up to the proved 69-wire discrepancy,
its real signed flow has an integer realization. -/
theorem local_integer_flow_nonempty {d : Nat} (b : KBag 64 d)
    (C eta : Rat) (count : Nat) (hC : 2 ^ 34 ≤ C) (heta : |eta| ≤ 69)
    (hcount : (count : Rat) = (1 - 1 / cap) * C + eta) :
    Nonempty (LocalIntegerFlow b C eta count) := by
  obtain ⟨up, blocks, heven, hupLe, hupError, htotal, hblockError⟩ :=
    candidate_round_bag_of_occupancy b C eta count hC heta hcount
  exact ⟨⟨up, blocks, heven, hupLe, hupError, htotal, hblockError⟩⟩

/-- Candidate frontier membership is enough to invoke the local integerizer. -/
theorem candidate_local_integer_flow_nonempty {d : Nat} (hd : 14 ≤ d)
    (t : Nat) (ht : t ≤ candidateTf d) (b : KBag 64 d) (eta : Rat)
    (hactive : candidateActive d t b) (count : Nat)
    (heta : |eta| ≤ 69)
    (hcount : (count : Rat) = (1 - 1 / cap) * candidateReferenceCapacity d b.l t + eta) :
    Nonempty (LocalIntegerFlow b (candidateReferenceCapacity d b.l t) eta count) := by
  exact local_integer_flow_nonempty b (candidateReferenceCapacity d b.l t) eta count
    (candidate_active_capacity_lower d hd t ht b.l hactive.1) heta hcount

/-- At the raw input root, the proposed interior reference capacity is only
`N/256`; this is why the ordinary bounded-discrepancy invariant cannot be the
root initialization rule. -/
theorem candidate_root_capacity_normalization (d : Nat) (hd : 2 ≤ d) :
    candidateReferenceCapacity d 0 0 * 256 = (64 ^ d : Nat) := by
  have hexp : candidateCapacityExponent d 0 0 + 8 = 6 * d := by
    unfold candidateCapacityExponent
    omega
  calc
    candidateReferenceCapacity d 0 0 * 256 =
        (2 : Rat) ^ candidateCapacityExponent d 0 0 * 2 ^ 8 := by
          norm_num [candidateReferenceCapacity, candidateCapacityExponent]
    _ = (2 : Rat) ^ (candidateCapacityExponent d 0 0 + 8) := (pow_add _ _ _).symm
    _ = (2 : Rat) ^ (6 * d) := by rw [hexp]
    _ = (64 : Rat) ^ d := by
      calc
        (2 : Rat) ^ (6 * d) = ((2 : Rat) ^ 6) ^ d := by rw [pow_mul]
        _ = (64 : Rat) ^ d := by norm_num
    _ = (64 ^ d : Nat) := by norm_num

/-- The actual raw-root wire count misses the candidate interior occupancy
target by far more than 69 wires, for every supported depth. -/
theorem candidate_raw_root_exceeds_interior_target (d : Nat) (hd : 14 ≤ d) :
    69 < (64 ^ d : Nat) -
      ((1 - 1 / cap) * candidateReferenceCapacity d 0 0) := by
  have hnorm := candidate_root_capacity_normalization d (by omega)
  have hNnat : 256 ≤ 64 ^ d := by
    calc
      256 ≤ 64 ^ 2 := by norm_num
      _ ≤ 64 ^ d := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hN : (256 : Rat) ≤ (64 ^ d : Nat) := by exact_mod_cast hNnat
  have hnormRat : candidateReferenceCapacity d 0 0 * 256 = (64 ^ d : Rat) := by
    exact_mod_cast hnorm
  have hcap : cap = 2 ^ 24 := by norm_num [cap]
  have htarget : (1 - 1 / cap) * candidateReferenceCapacity d 0 0 =
      (1 - 1 / (2 : Rat) ^ 24) * ((64 ^ d : Rat) / 256) := by
    rw [hcap, ← hnormRat]
    field_simp
  have hgap : (64 ^ d : Rat) -
      ((1 - 1 / cap) * candidateReferenceCapacity d 0 0) >
        (255 / 256 : Rat) * (64 ^ d : Rat) := by
    rw [htarget]
    calc
      (64 ^ d : Rat) -
          (1 - 1 / (2 : Rat) ^ 24) * ((64 ^ d : Rat) / 256) =
          (1 - (1 - 1 / (2 : Rat) ^ 24) / 256) * (64 ^ d : Rat) := by ring
      _ > (255 / 256 : Rat) * (64 ^ d : Rat) := by
        apply mul_lt_mul_of_pos_right
        · norm_num
        · positivity
  have hlarge : (255 / 256 : Rat) * (256 : Rat) > 69 := by norm_num
  have : (255 / 256 : Rat) * (256 : Rat) ≤
      (255 / 256 : Rat) * (64 ^ d : Rat) := by
    nlinarith [hN]
  have hweak : 69 < (255 / 256 : Rat) * (64 ^ d : Rat) :=
    lt_of_lt_of_le hlarge this
  have hgap69 : (64 ^ d : Rat) -
      ((1 - 1 / cap) * candidateReferenceCapacity d 0 0) > 69 :=
    lt_trans hweak hgap
  exact_mod_cast hgap69

/-- Active candidate capacities have the exact spatial and space-time ratios
needed by the signed occupancy identity. -/
theorem candidate_active_capacity_ratios {d : Nat} (hd : 14 ≤ d)
    (t : Nat) (ht : t ≤ candidateTf d) (b : KBag 64 d)
    (hactive : candidateActive d t b) (htf : t < candidateTf d) :
    candidateReferenceCapacity d (b.l + 2) t = 64 ^ 2 *
        candidateReferenceCapacity d b.l t ∧
      candidateReferenceCapacity d (b.l + 1) (t + 1) =
        4 * candidateReferenceCapacity d b.l t := by
  have hbase : 4 * t + 8 ≤ 6 * d + 6 * b.l := by
    have hα := candidate_alpha_exponent_bound d hd t ht
    have hαlinear : 4 * t + 8 ≤ 6 * d + 6 * candidateAlpha d t := by
      unfold candidateCapacityExponent at hα
      omega
    have hlevel : candidateAlpha d t ≤ b.l := hactive.1
    omega
  exact ⟨candidate_reference_capacity_grandchild d b.l t hbase,
    candidate_reference_capacity_next_stage d hd t htf b.l hactive.1⟩

/-- Pick all local integer splits simultaneously over any active address set.
This is only a choice constructor: the caller must separately prove the
occupancy and capacity premises for every active bag. -/
noncomputable def chooseLocalIntegerFlows {d : Nat}
    (Active : KBag 64 d → Prop) (C eta : KBag 64 d → Rat)
    (count : KBag 64 d → Nat)
    (hlocal : ∀ b, Active b → Nonempty (LocalIntegerFlow b (C b) (eta b) (count b))) :
    ∀ b, Active b → LocalIntegerFlow b (C b) (eta b) (count b) := by
  classical
  intro b hb
  exact Classical.choice (hlocal b hb)

private theorem child_level_lt {d : Nat} (b : KBag 64 d) (j : Fin 64)
    (hdepth : b.l + 2 < d) :
    (b.child j.val j.isLt (by omega)).l < d := by
  change b.l + 1 < d
  omega

private theorem grandchild_level_lt {d : Nat} (b : KBag 64 d) (j l : Fin 64)
    (hdepth : b.l + 2 < d) :
    ((b.child j.val j.isLt (by omega)).child l.val l.isLt (child_level_lt b j hdepth)).l < d := by
  change b.l + 2 < d
  omega

/-- The address of a child after a parent split receives that parent's block
and the up-flows selected at the child's 64 children. -/
def routedChildCount {d : Nat} {Active : KBag 64 d → Prop}
    {C eta : KBag 64 d → Rat} {count : KBag 64 d → Nat}
    (F : ∀ b, Active b → LocalIntegerFlow b (C b) (eta b) (count b))
    (b : KBag 64 d) (hb : Active b) (j : Fin 64) (hdepth : b.l + 2 < d)
    (hgcActive : ∀ l : Fin 64,
      Active ((b.child j.val j.isLt (by omega)).child l.val l.isLt (child_level_lt b j hdepth))) : Nat :=
    (F b hb).blocks j +
    ∑ l : Fin 64,
      (F ((b.child j.val j.isLt (by omega)).child l.val l.isLt (child_level_lt b j hdepth))
        (hgcActive l)).up

/-- The local rounding construction preserves the 69-wire discrepancy after
one ordinary interior routing transition. Root, frontier, and terminal cases
are deliberately outside this statement. -/
theorem routed_child_discrepancy {d : Nat}
    {Active : KBag 64 d → Prop} {C eta : KBag 64 d → Rat}
    {count : KBag 64 d → Nat}
    (F : ∀ b, Active b → LocalIntegerFlow b (C b) (eta b) (count b))
    (b : KBag 64 d) (hb : Active b) (j : Fin 64) (hdepth : b.l + 2 < d)
    (hgcActive : ∀ l : Fin 64,
      Active ((b.child j.val j.isLt (by omega)).child l.val l.isLt (child_level_lt b j hdepth)))
    (hCgrand : ∀ l : Fin 64,
      C ((b.child j.val j.isLt (by omega)).child l.val l.isLt (child_level_lt b j hdepth)) = 64 ^ 2 * C b) :
    |(routedChildCount F b hb j hdepth hgcActive : Rat) -
        (1 - 1 / cap) * (4 * C b)| ≤ 69 := by
  apply candidate_occupancy_transition b j (by omega)
    (child_level_lt b j hdepth)
    (C b) (4 * C b)
    (routedChildCount F b hb j hdepth hgcActive)
    ((F b hb).blocks j)
    (fun l => (F ((b.child j.val j.isLt (by omega)).child l.val l.isLt (child_level_lt b j hdepth))
      (hgcActive l)).up)
    rfl
    ((F b hb).blockError j)
    (by
      intro l
      simpa [hCgrand l] using
        (F ((b.child j.val j.isLt (by omega)).child l.val l.isLt (child_level_lt b j hdepth))
          (hgcActive l)).upError)
    (by
      unfold routedChildCount
      push_cast
      rfl)

/-- The generic local recurrence specializes to the proposed schedule on an
interior address: the next-stage child occupancy is within 69 of its target
capacity, provided the current bag and all grandchildren already satisfy the
integer-flow hypotheses. This packages the induction step but does not prove
those hypotheses globally. -/
theorem candidate_interior_routed_discrepancy {d : Nat} (hd : 14 ≤ d)
    (t : Nat) (ht : t < candidateTf d) (b : KBag 64 d)
    (hb : candidateScheduledActive d t b)
    (hbottom : b.l + 2 ≤ candidateOmega t)
    (hdepth : b.l + 2 < d)
    (eta : KBag 64 d → Rat)
    (ncount : KBag 64 d → Nat)
    (F : ∀ q, candidateScheduledActive d t q →
      LocalIntegerFlow q (candidateReferenceCapacity d q.l t) (eta q) (ncount q)) :
    ∀ j : Fin 64,
      |(routedChildCount
          (fun q hq => F q hq) b hb j hdepth
          (by
            intro l
            exact (candidate_interior_active_successors d hd t ht b hb hbottom).2 j l)
          : Rat) -
        (1 - 1 / cap) *
          candidateReferenceCapacity d (b.l + 1) (t + 1)| ≤ 69 := by
  intro j
  have hchilddepth : (b.child j.val j.isLt (by omega)).l < d := by
    exact child_level_lt b j hdepth
  let hgcActive : ∀ l : Fin 64,
      candidateScheduledActive d t
        ((b.child j.val j.isLt (by omega)).child l.val l.isLt
          (child_level_lt b j hdepth)) := by
    intro l
    exact (candidate_interior_active_successors d hd t ht b hb hbottom).2 j l
  have hcapacity := candidate_active_capacity_ratios hd t
    (by unfold candidateTf at ht ⊢; omega) b hb.1 (by
      unfold candidateTf at ht ⊢
      omega)
  have hnext := hcapacity.2
  have hgrand : ∀ l : Fin 64,
      candidateReferenceCapacity d
        ((b.child j.val j.isLt (by omega)).child l.val l.isLt
          (child_level_lt b j hdepth)).l t =
        64 ^ 2 * candidateReferenceCapacity d b.l t := by
    intro l
    have hlev : ((b.child j.val j.isLt (by omega)).child l.val l.isLt
        (child_level_lt b j hdepth)).l = b.l + 2 := by rfl
    rw [hlev]
    exact hcapacity.1
  have hbase :
      |(routedChildCount
          (fun q hq => F q hq) b hb j hdepth hgcActive : Rat) -
        (1 - 1 / cap) * (4 * candidateReferenceCapacity d b.l t)| ≤ 69 := by
    exact routed_child_discrepancy (fun q hq => F q hq) b hb j hdepth
      hgcActive hgrand
  rw [hnext]
  exact hbase

/-- Interior local-flow closure: if the current active bags already have
integer realizations, then each scheduled child admits a local integer flow at
the next stage. This is the precise reusable induction step; it leaves the
root and moving-frontier seed/exit rules to the global scheduler. -/
theorem candidate_interior_child_flow_exists {d : Nat} (hd : 14 ≤ d)
    (t : Nat) (ht : t < candidateTf d) (b : KBag 64 d)
    (hb : candidateScheduledActive d t b)
    (hbottom : b.l + 2 ≤ candidateOmega t)
    (hdepth : b.l + 2 < d)
    (eta : KBag 64 d → Rat) (ncount : KBag 64 d → Nat)
    (F : ∀ q, candidateScheduledActive d t q →
      LocalIntegerFlow q (candidateReferenceCapacity d q.l t) (eta q) (ncount q)) :
    ∀ j : Fin 64,
      Nonempty (LocalIntegerFlow
        (b.child j.val j.isLt (by omega))
        (candidateReferenceCapacity d (b.l + 1) (t + 1))
        ((routedChildCount (fun q hq => F q hq) b hb j hdepth
          (fun l => (candidate_interior_active_successors d hd t ht b hb hbottom).2 j l) : Rat) -
          (1 - 1 / cap) * candidateReferenceCapacity d (b.l + 1) (t + 1))
        (routedChildCount (fun q hq => F q hq) b hb j hdepth
          (fun l => (candidate_interior_active_successors d hd t ht b hb hbottom).2 j l))) := by
  intro j
  let child := b.child j.val j.isLt (by omega)
  let hchild : candidateScheduledActive d (t + 1) child :=
    (candidate_interior_active_successors d hd t ht b hb hbottom).1 j
  let n := routedChildCount (fun q hq => F q hq) b hb j hdepth
    (fun l => (candidate_interior_active_successors d hd t ht b hb hbottom).2 j l)
  let e : Rat := (n : Rat) -
    (1 - 1 / cap) * candidateReferenceCapacity d (b.l + 1) (t + 1)
  have he : |e| ≤ 69 := by
    change |(routedChildCount (fun q hq => F q hq) b hb j hdepth
      (fun l => (candidate_interior_active_successors d hd t ht b hb hbottom).2 j l) : Rat) -
      (1 - 1 / cap) * candidateReferenceCapacity d (b.l + 1) (t + 1)| ≤ 69
    exact candidate_interior_routed_discrepancy hd t ht b hb hbottom hdepth eta ncount F j
  have htNext : t + 1 ≤ candidateTf d := by omega
  have hcapacity : 2 ^ 34 ≤ candidateReferenceCapacity d (b.l + 1) (t + 1) := by
    exact candidate_active_capacity_lower d hd (t + 1) htNext (b.l + 1) hchild.1.1
  have hcount : (n : Rat) =
      (1 - 1 / cap) * candidateReferenceCapacity d (b.l + 1) (t + 1) + e := by
    change (n : Rat) =
      (1 - 1 / cap) * candidateReferenceCapacity d (b.l + 1) (t + 1) +
        ((n : Rat) - (1 - 1 / cap) * candidateReferenceCapacity d (b.l + 1) (t + 1))
    ring
  have hflow := local_integer_flow_nonempty child
    (candidateReferenceCapacity d (b.l + 1) (t + 1)) e n hcapacity he hcount
  exact hflow

end Tapered945
