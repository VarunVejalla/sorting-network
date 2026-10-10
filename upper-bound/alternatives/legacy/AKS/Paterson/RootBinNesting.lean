module

public import AKS.Paterson.RootSortedBins

/-! # Coarse ancestor bins contain their finer bins -/

@[expose] public section

namespace Paterson.Bags

open Finset

theorem bin_width_ancestor {k l L : ℕ} (U : Finset (Fin (2 ^ k)))
    (hL : L ≤ l) (hd : 2 ^ l ∣ U.card) :
    U.card / 2 ^ L = 2 ^ (l - L) * (U.card / 2 ^ l) := by
  have hm := Nat.mul_div_cancel' hd
  have hp : 2 ^ l = 2 ^ L * 2 ^ (l - L) := by
    rw [← pow_add, Nat.add_sub_of_le hL]
  calc U.card / 2 ^ L =
      (2 ^ L * (2 ^ (l - L) * (U.card / 2 ^ l))) / 2 ^ L := by
        congr 1
        rw [← mul_assoc, ← hp, hm]
    _ = _ := Nat.mul_div_right _ (m := 2 ^ L) (by positivity)

theorem positionalBin_ancestor {k l L : ℕ} (U : Finset (Fin (2 ^ k)))
    (hL : L ≤ l) (hd : 2 ^ l ∣ U.card) (x : ℕ) :
    positionalBin U l x ⊆ positionalBin U L (x / 2 ^ (l - L)) := by
  intro i hi
  obtain ⟨j, hj, rfl⟩ := mem_image.mp hi
  obtain ⟨_, hlo, hhi⟩ := mem_filter.mp hj
  apply mem_image.mpr
  refine ⟨j, mem_filter.mpr ⟨mem_univ _, ?_⟩, rfl⟩
  rw [bin_width_ancestor U hL hd]
  have hdlo := Nat.div_mul_le_self x (2 ^ (l - L))
  have hdhi := Nat.lt_div_mul_add (by positivity : 0 < (2 : ℕ) ^ (l - L)) (a := x)
  have hlo' := Nat.mul_le_mul_right (U.card / 2 ^ l) hdlo
  have hhi' := Nat.mul_le_mul_right (U.card / 2 ^ l) (show
      x + 1 ≤ (x / 2 ^ (l - L)) * 2 ^ (l - L) + 2 ^ (l - L) by omega)
  simp only [mul_assoc, Nat.add_mul, Nat.one_mul] at hlo' hhi' hlo hhi ⊢
  constructor <;> omega

end Paterson.Bags
