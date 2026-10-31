import D2RankAlignment

open scoped BigOperators

namespace Chvatal.D2RankAlignment

/-- A balanced routed profile with total l1 error at most `B` has at most
`B/2` excess mass on every chosen family of destination cells. This lets a
two-sided profile estimate control any union of physical cells, including a
prefix of the next sender's address interval. -/
theorem subset_excess_le_half_l1
    {J : Type*} [Fintype J] [DecidableEq J]
    (actual ideal : J → Nat) (B : Nat)
    (hTotal : (∑ j : J, actual j) = ∑ j : J, ideal j)
    (hL1 : (∑ j : J, countDistance (actual j) (ideal j)) ≤ B)
    (S : Finset J) :
    2 * ((∑ j ∈ S, actual j) - (∑ j ∈ S, ideal j)) ≤ B := by
  have hdirection := balanced_port_directional_leakage actual ideal B hTotal hL1
  have hlocal (j : J) : actual j ≤ ideal j + (actual j - ideal j) := by omega
  have hsum := Finset.sum_le_sum (s := S) (fun j hj => hlocal j)
  rw [Finset.sum_add_distrib] at hsum
  have hsubset :
      (∑ j ∈ S, actual j) - (∑ j ∈ S, ideal j) ≤
        ∑ j ∈ S, (actual j - ideal j) := by omega
  have hpositive :
      (∑ j ∈ S, (actual j - ideal j)) ≤ ∑ j : J, (actual j - ideal j) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg S.subset_univ
      (fun j hj _ => Nat.zero_le _)
  calc
    2 * ((∑ j ∈ S, actual j) - (∑ j ∈ S, ideal j)) ≤
        2 * (∑ j ∈ S, (actual j - ideal j)) := Nat.mul_le_mul_left 2 hsubset
    _ ≤ 2 * (∑ j : J, (actual j - ideal j)) := Nat.mul_le_mul_left 2 hpositive
    _ ≤ B := hdirection.1

end Chvatal.D2RankAlignment
