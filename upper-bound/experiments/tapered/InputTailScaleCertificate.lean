import CandidateFrontier
import AKS.Chvatal.Tree
import Mathlib.Tactic

namespace Tapered945

/-- A concrete interior scheduled bag where the native child interval is much
larger than the reference register capacity. This certifies why one-bag
outsider tails cannot by themselves provide the separator's internal cuts. -/
theorem stage10_level2_scale (d : Nat) (hd : 14 <= d) :
    candidateAlpha d 10 = 0 /\ candidateOmega 10 = 4 /\
    candidateCapacityExponent d 2 10 = 6 * d - 36 /\
    (Chvatal.bagSize 64 d 2 : Rat) =
      2 ^ 24 * candidateReferenceCapacity d 2 10 /\
    (Chvatal.bagSize 64 d 3 : Rat) =
      2 ^ 18 * candidateReferenceCapacity d 2 10 := by
  have hcap : candidateCapacityExponent d 2 10 = 6 * d - 36 := by
    unfold candidateCapacityExponent
    omega
  have hpow : 6 * (d - 2) = (6 * d - 36) + 24 := by omega
  have hpowChild : 6 * (d - 3) = (6 * d - 36) + 18 := by omega
  refine ⟨?_, ?_, hcap, ?_, ?_⟩
  · unfold candidateAlpha candidateAlphaBase Chvatal.ceilParity
    norm_num [Nat.sub_eq_zero_of_le (by omega : 14 <= d)]
  · unfold candidateOmega candidateOmegaBase Chvatal.ceilParity
    norm_num
  · change ((64 ^ (d - 2) : Nat) : Rat) =
      2 ^ 24 * (2 : Rat) ^ (6 * d - 36)
    have hNat : 64 ^ (d - 2) = 2 ^ 24 * 2 ^ (6 * d - 36) := by
      calc
        64 ^ (d - 2) = (2 ^ 6) ^ (d - 2) := by norm_num
        _ = 2 ^ (6 * (d - 2)) := by rw [pow_mul]
        _ = 2 ^ ((6 * d - 36) + 24) := by rw [hpow]
        _ = 2 ^ 24 * 2 ^ (6 * d - 36) := by rw [pow_add]; ring
    exact_mod_cast hNat
  · change ((64 ^ (d - 3) : Nat) : Rat) =
      2 ^ 18 * (2 : Rat) ^ (6 * d - 36)
    have hNat : 64 ^ (d - 3) = 2 ^ 18 * 2 ^ (6 * d - 36) := by
      calc
        64 ^ (d - 3) = (2 ^ 6) ^ (d - 3) := by norm_num
        _ = 2 ^ (6 * (d - 3)) := by rw [pow_mul]
        _ = 2 ^ ((6 * d - 36) + 18) := by rw [hpowChild]
        _ = 2 ^ 18 * 2 ^ (6 * d - 36) := by rw [pow_add]; ring
    exact_mod_cast hNat

end Tapered945
