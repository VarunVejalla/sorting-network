import D2RankRebatch
import D2BalancedPrefixProfile
import D2StaticWireSets

open scoped BigOperators
open Chvatal.D2RankAlignment
open Chvatal.D2StaticWireSets

namespace Chvatal.D2RankProfileRouting

/-- A live rank position of a sender is routed to the physical address of
that rank in the sender's increasing wire order. -/
def rankDestination {n : Nat} {J : Type*}
    (sender : Finset (Fin n)) (cellOf : Fin n → J)
    (b : Fin sender.card) : J :=
  cellOf (sender.orderEmbOfFin rfl b)

/-- The threshold count actually routed to one destination cell. `out` is
the Boolean output profile of the fixed local core in row-major rank order. -/
def routedActualCount {n W : Nat} {J : Type*} [DecidableEq J]
    (sender : Finset (Fin n)) (cellOf : Fin n → J)
    (out : Fin W → Bool) (hcapacity : sender.card ≤ W) (j : J) : Nat :=
  ∑ b ∈ Finset.univ.filter (fun b : Fin sender.card =>
      rankDestination sender cellOf b = j),
    if out ⟨b.val, Nat.lt_of_lt_of_le b.isLt hcapacity⟩ then 1 else 0

/-- The ideal next-cell profile is obtained by routing the first `H` ranks
of the sender. This is the exact rank-cut target, grouped by physical cell. -/
def routedIdealCount {n : Nat} {J : Type*} [DecidableEq J]
    (sender : Finset (Fin n)) (cellOf : Fin n → J) (H : Nat) (j : J) : Nat :=
  ∑ b ∈ Finset.univ.filter (fun b : Fin sender.card =>
      rankDestination sender cellOf b = j),
    if b.val < H then 1 else 0

/-- Grouping the local core's rank-by-rank threshold errors into the actual
physical destinations cannot increase their total l1 profile error. The
ordered embedding makes this a concrete address-routing statement for any
finite D2 bag, including bags represented by several wire runs. -/
theorem routed_profile_error_le_rank_error
    {n W : Nat} {J : Type*} [Fintype J] [DecidableEq J]
    (sender : Finset (Fin n)) (cellOf : Fin n → J)
    (out : Fin W → Bool) (H : Nat)
    (hcapacity : sender.card ≤ W) :
    (∑ j : J, countDistance
      (routedActualCount sender cellOf out hcapacity j)
      (routedIdealCount sender cellOf H j)) ≤
    ∑ b : Fin sender.card,
      countDistance
        (if out ⟨b.val, Nat.lt_of_lt_of_le b.isLt hcapacity⟩ then 1 else 0)
        (if b.val < H then 1 else 0) := by
  let group : Fin sender.card → J := rankDestination sender cellOf
  let actual : Fin sender.card → Nat := fun b =>
    if out ⟨b.val, Nat.lt_of_lt_of_le b.isLt hcapacity⟩ then 1 else 0
  let ideal : Fin sender.card → Nat := fun b => if b.val < H then 1 else 0
  simpa [group, actual, ideal, routedActualCount, routedIdealCount,
    rankDestination] using
    (grouped_countDistance_le_refined_countDistance group actual ideal)

/-- Thus any local core certificate bounding the singleton-rank errors by
448 also bounds the total error of its next physical cell profile by 448. -/
theorem routed_profile_error_le_448
    {n W : Nat} {J : Type*} [Fintype J] [DecidableEq J]
    (sender : Finset (Fin n)) (cellOf : Fin n → J)
    (out : Fin W → Bool) (H : Nat)
    (hcapacity : sender.card ≤ W)
    (hlocal : (∑ b : Fin sender.card,
      countDistance
        (if out ⟨b.val, Nat.lt_of_lt_of_le b.isLt hcapacity⟩ then 1 else 0)
        (if b.val < H then 1 else 0)) ≤ 448) :
    (∑ j : J, countDistance
      (routedActualCount sender cellOf out hcapacity j)
      (routedIdealCount sender cellOf H j)) ≤ 448 :=
  (routed_profile_error_le_rank_error sender cellOf out H hcapacity).trans hlocal

/-- With exact conservation of the threshold mass, the 448 total profile
error gives at most 224 keys of one-sided leakage across any union of physical
destinations. In particular, this applies to every address prefix that is a
union of destination cells. -/
theorem routed_profile_subset_excess_le_224
    {n W : Nat} {J : Type*} [Fintype J] [DecidableEq J]
    (sender : Finset (Fin n)) (cellOf : Fin n → J)
    (out : Fin W → Bool) (H : Nat)
    (hcapacity : sender.card ≤ W)
    (hTotal : (∑ j : J,
      routedActualCount sender cellOf out hcapacity j) =
      ∑ j : J, routedIdealCount sender cellOf H j)
    (hlocal : (∑ b : Fin sender.card,
      countDistance
        (if out ⟨b.val, Nat.lt_of_lt_of_le b.isLt hcapacity⟩ then 1 else 0)
        (if b.val < H then 1 else 0)) ≤ 448)
    (S : Finset J) :
    2 * ((∑ j ∈ S, routedActualCount sender cellOf out hcapacity j) -
      (∑ j ∈ S, routedIdealCount sender cellOf H j)) ≤ 448 := by
  exact subset_excess_le_half_l1
    (routedActualCount sender cellOf out hcapacity)
    (routedIdealCount sender cellOf H) 448 hTotal
    (routed_profile_error_le_448 sender cellOf out H hcapacity hlocal) S

end Chvatal.D2RankProfileRouting
