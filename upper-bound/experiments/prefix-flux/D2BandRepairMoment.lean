import D2BandRepairInversion

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

namespace Chvatal.D2BandRepairMoment

open Chvatal.D2BandRepair4096Network
open Chvatal.D2TwoGridPhysicalBand
open Chvatal.D2BandRepairInversion
open Chvatal.D2InversionLocalization

/-- The checked 832-wire common-band provider bounds the third distance
moment around the sender's exact zero-count cut by a constant independent of
the sender's input height profile. -/
theorem physical_twoGridRepair_third_moment_le_832_pow_four
    (h : Chvatal.D2BandRepair4096Network.Col → Nat)
    (hbound : ∀ c, h c ≤ 4096)
    (perm : Chvatal.D2BandRepair4096Network.Row →
      Equiv.Perm Chvatal.D2BandRepair4096Network.Col) :
    cutDistanceMoment
      (fun w : Wire =>
        twoGridRepair.exec (fullHeightAfterRowPermutation h perm) w)
      (zeroCount (fun w : Wire =>
        twoGridRepair.exec (fullHeightAfterRowPermutation h perm) w)) 3
      ≤ 832 ^ 4 := by
  let v : Wire → Bool := fun w =>
    twoGridRepair.exec (fullHeightAfterRowPermutation h perm) w
  let q := zeroCount v
  have hpop : (cutWrongOnes v q).card + (cutWrongZeros v q).card ≤ 832 := by
    simpa [v, q] using physical_twoGridRepair_wrong_population_le_832 h hbound perm
  have hnear := physical_twoGridRepair_misplaced_bits_within_832 h hbound perm
  have hone : (cutWrongOnes v q).sum (fun p => (q - p.val) ^ 3) ≤
      (cutWrongOnes v q).card * 832 ^ 3 := by
    calc
      _ ≤ (cutWrongOnes v q).sum (fun _ => 832 ^ 3) := by
        apply Finset.sum_le_sum
        intro p hp
        simp only [cutWrongOnes, Finset.mem_filter, Finset.mem_univ,
          true_and] at hp
        have hdist := hnear.2 p hp.2 hp.1
        have hdistV : zeroCount v ≤ p.val + 832 := by simpa [v] using hdist
        have hdist' : zeroCount v - p.val ≤ 832 := by omega
        have hdist'' : q - p.val ≤ 832 := by simpa [q] using hdist'
        exact Nat.pow_le_pow_left hdist'' 3
      _ = (cutWrongOnes v q).card * 832 ^ 3 := by simp
  have hzero : (cutWrongZeros v q).sum (fun p => (p.val - q) ^ 3) ≤
      (cutWrongZeros v q).card * 832 ^ 3 := by
    calc
      _ ≤ (cutWrongZeros v q).sum (fun _ => 832 ^ 3) := by
        apply Finset.sum_le_sum
        intro p hp
        simp only [cutWrongZeros, Finset.mem_filter, Finset.mem_univ,
          true_and] at hp
        have hdist := hnear.1 p hp.2 hp.1
        have hdistV : p.val < zeroCount v + 832 := by simpa [v] using hdist
        have hdist' : p.val - zeroCount v ≤ 832 := by omega
        have hdist'' : p.val - q ≤ 832 := by simpa [q] using hdist'
        exact Nat.pow_le_pow_left hdist'' 3
      _ = (cutWrongZeros v q).card * 832 ^ 3 := by simp
  change (cutWrongOnes v q).sum (fun p => (q - p.val) ^ 3) +
      (cutWrongZeros v q).sum (fun p => (p.val - q) ^ 3) ≤ 832 ^ 4
  calc
    _ ≤ ((cutWrongOnes v q).card +
          (cutWrongZeros v q).card) * 832 ^ 3 := by
      calc
        _ ≤ (cutWrongOnes v q).card * 832 ^ 3 +
            (cutWrongZeros v q).card * 832 ^ 3 :=
          Nat.add_le_add hone hzero
        _ = _ := by rw [Nat.add_mul]
    _ ≤ 832 * 832 ^ 3 := Nat.mul_le_mul_right _ hpop
    _ = 832 ^ 4 := by norm_num [pow_succ]

end Chvatal.D2BandRepairMoment
