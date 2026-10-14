import CandidateSeed
import Mathlib.Tactic

namespace Tapered945

/-! Exact population accounting at the two special bootstrap frontiers.
These identities use only the integer seed schedule. They do not assert that
the descendant registers contain the corresponding native keys. -/

/-- At the stage-two root, its own register plus all level-two descendant
registers account for the entire root interval. Thus the strict-subtree mass
defect is exactly the root's own register size. -/
theorem bootstrap_root_population_identity (d : Nat) (hd : 14 ≤ d) :
    (64 ^ d : Rat) =
      64 * seedLevelOneUp d + 4096 * seedLevelOneDown d := by
  have hNat : 64 ^ d = 64 * seedLevelOneUp d + 4096 * seedLevelOneDown d := by
    calc
      64 ^ d = seedRootInput d := rfl
      _ = 64 * seedRootDown d := seed_root_conservation d (by omega)
      _ = 64 * (seedLevelOneUp d + 64 * seedLevelOneDown d) := by
        rw [seed_level_one_conservation d (by omega)]
      _ = 64 * seedLevelOneUp d + 4096 * seedLevelOneDown d := by ring
  exact_mod_cast hNat

private theorem bootstrap_bottom_count_as_common_mass (d : Nat)
    (hd : 14 ≤ d) :
    seedBottomDown2 d = 1020 * 2 ^ (6 * d - 28) := by
  unfold seedBottomDown2
  rw [show 6 * d - 18 = 10 + (6 * d - 28) by omega,
      show 6 * d - 26 = 2 + (6 * d - 28) by omega,
      pow_add, pow_add]
  norm_num
  omega

/-- At the first moving bottom frontier, the level-one interval consists in
population exactly of its own register plus its 4096 level-three descendants.
The omitted mass in a strict-descendant-only estimate is therefore precisely
the level-one register size, rather than a small rounding error. -/
theorem bootstrap_level_one_population_identity (d : Nat) (hd : 14 ≤ d) :
    (64 ^ (d - 1) : Rat) =
      seedStageThreeTopSize d + 4096 * seedBottomDown2 d := by
  have hdown := bootstrap_bottom_count_as_common_mass d hd
  have htop : seedStageThreeTopSize d = 2 ^ (6 * d - 14) := rfl
  have hnative : (64 ^ (d - 1) : Rat) = (2 : Rat) ^ (6 * d - 6) := by
    rw [show (64 : Rat) = 2 ^ 6 by norm_num, ← pow_mul]
    congr 1
    omega
  have hbase : (2 : Rat) ^ (6 * d - 6) =
      2 ^ 22 * 2 ^ (6 * d - 28) := by
    rw [show 6 * d - 6 = 22 + (6 * d - 28) by omega, pow_add]
  have htop' : (2 : Rat) ^ (6 * d - 14) =
      2 ^ 14 * (2 : Rat) ^ (6 * d - 28) := by
    rw [show 6 * d - 14 = 14 + (6 * d - 28) by omega, pow_add]
  rw [hnative, hbase, htop, hdown]
  push_cast
  rw [htop']
  ring

/-- The first-frontier whole-subtree defect is an order-one fraction of the
reference capacity: it equals exactly `candidateReferenceCapacity d 1 3`.
This is why the strict-subtree ambient-mass lemma cannot by itself yield the
small signed reserve at this state. -/
theorem bootstrap_level_one_defect_is_reference_capacity
    (d : Nat) (hd : 14 ≤ d) :
    (64 ^ (d - 1) : Rat) - 4096 * seedBottomDown2 d =
      candidateReferenceCapacity d 1 3 := by
  have hmass := bootstrap_level_one_population_identity d hd
  have htop : (seedStageThreeTopSize d : Rat) =
      candidateReferenceCapacity d 1 3 := by
    unfold candidateReferenceCapacity
    rw [show candidateCapacityExponent d 1 3 = 6 * d - 14 by
      unfold candidateCapacityExponent; omega]
    exact_mod_cast (show seedStageThreeTopSize d = 2 ^ (6 * d - 14) by rfl)
  rw [hmass, htop]
  ring

end Tapered945
