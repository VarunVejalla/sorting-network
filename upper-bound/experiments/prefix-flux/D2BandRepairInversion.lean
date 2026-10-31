import D2BandInversion
import D2BandRepair4096Network
import D2BlockSortDisplacement

open Chvatal.D2BandInversion
open Chvatal.D2BandRepair4096Network
open Chvatal.D2TwoGridPhysicalBand

namespace Chvatal.D2BandRepairInversion

set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

def sortedZeroPrefix {N : Nat} (q : Nat) (w : Fin N) : Bool :=
  if w.val < q then false else true

def hammingDistance {N : Nat} (v w : Fin N → Bool) : Nat :=
  (Finset.univ.filter fun x : Fin N => v x ≠ w x).card

/-- Threshold the rank carried on each output wire. -/
def rankThresholdWord (out : Wire → Wire) (q : Nat) : Wire → Bool :=
  fun w => if (out w).val < q then false else true

private theorem card_fin_prefix_le {N q : Nat} (hq : q ≤ N) :
    (Finset.univ.filter fun p : Fin N => p.val < q).card = q := by
  classical
  by_cases hq' : q < N
  · let a : Fin N := ⟨q, hq'⟩
    have hset : (Finset.univ.filter fun p : Fin N => p.val < q) = Finset.Iio a := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_Iio]
      change p.val < q ↔ p.val < q
      rfl
    rw [hset]
    simp [a]
  · have hqeq : q = N := by omega
    subst q
    simp

private theorem threshold_zeroCount_eq {out : Wire → Wire}
    (hbij : Function.Bijective out) {q : Nat} (hq : q ≤ 4096 * 64) :
    Chvatal.D2InversionLocalization.zeroCount (rankThresholdWord out q) = q := by
  classical
  unfold Chvatal.D2InversionLocalization.zeroCount
    Chvatal.D2InversionLocalization.zeroPositions
  have hset :
      (Finset.univ.filter fun w : Wire => rankThresholdWord out q w = false) =
        Finset.univ.filter fun w : Wire => (out w).val < q := by
    ext w
    simp [rankThresholdWord]
  have hcard :
      (Finset.univ.filter fun w : Wire => (out w).val < q).card =
        (Finset.univ.filter fun w : Wire => w.val < q).card := by
    apply Finset.card_bij (fun w _ => out w)
    · intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
      exact hw
    · intro a ha b hb hab
      exact hbij.1 hab
    · intro a ha
      obtain ⟨w, hw⟩ := hbij.2 a
      refine ⟨w, ?_, hw⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      simpa [hw] using ha
  rw [hset, hcard]
  exact card_fin_prefix_le hq

theorem hammingDistance_eq_cut_wrong_population
    {N : Nat} (v : Fin N → Bool) :
    hammingDistance v (sortedZeroPrefix
      (Chvatal.D2InversionLocalization.zeroCount v)) =
      (Chvatal.D2InversionLocalization.cutWrongOnes v
        (Chvatal.D2InversionLocalization.zeroCount v)).card +
      (Chvatal.D2InversionLocalization.cutWrongZeros v
        (Chvatal.D2InversionLocalization.zeroCount v)).card := by
  classical
  let q := Chvatal.D2InversionLocalization.zeroCount v
  let A := Chvatal.D2InversionLocalization.cutWrongOnes v q
  let B := Chvatal.D2InversionLocalization.cutWrongZeros v q
  have hunion :
      Finset.univ.filter (fun w : Fin N => v w ≠ sortedZeroPrefix q w) = A ∪ B := by
    ext w
    by_cases hp : w.val < q <;> cases hv : v w <;>
      simp [A, B, q, sortedZeroPrefix,
        Chvatal.D2InversionLocalization.cutWrongOnes,
        Chvatal.D2InversionLocalization.cutWrongZeros, hp, hv] <;> omega
  have hdisjoint : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro w hwA hwB
    simp [A, B, Chvatal.D2InversionLocalization.cutWrongOnes,
      Chvatal.D2InversionLocalization.cutWrongZeros] at hwA hwB
    omega
  unfold hammingDistance
  rw [hunion, Finset.card_union_of_disjoint hdisjoint]

theorem physical_twoGridRepair_zeroCount_eq
    (v : Wire → Bool) :
    Chvatal.D2InversionLocalization.zeroCount (twoGridRepair.exec v) =
      Chvatal.D2InversionLocalization.zeroCount v := by
  unfold Chvatal.D2InversionLocalization.zeroCount
    Chvatal.D2InversionLocalization.zeroPositions
  exact Chvatal.D2BandRepair4096Network.comparatorNetwork_falseCount_preserved
    twoGridRepair v

theorem hammingDistance_triangle {N : Nat} (v w z : Fin N → Bool) :
    hammingDistance v z ≤ hammingDistance v w + hammingDistance w z := by
  classical
  let A := Finset.univ.filter fun p : Fin N => v p ≠ z p
  let B := Finset.univ.filter fun p : Fin N => v p ≠ w p
  let C := Finset.univ.filter fun p : Fin N => w p ≠ z p
  have hsubset : A ⊆ B ∪ C := by
    intro p hp
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    simp only [B, C, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and]
    by_cases hvw : v p = w p
    · right
      simpa [hvw] using hp
    · exact Or.inl hvw
  calc
    hammingDistance v z = A.card := rfl
    _ ≤ (B ∪ C).card := Finset.card_le_card hsubset
    _ ≤ B.card + C.card := Finset.card_union_le _ _
    _ = hammingDistance v w + hammingDistance w z := rfl

theorem hammingDistance_sortedZero_le_countDistance {N : Nat}
    (q r : Nat) (hq : q ≤ N) (hr : r ≤ N) :
    hammingDistance (sortedZeroPrefix (N := N) q) (sortedZeroPrefix (N := N) r) ≤
      Chvatal.D2RankAlignment.countDistance q r := by
  classical
  by_cases hqr : q ≤ r
  · have hsubset :
        (Finset.univ.filter fun p : Fin N =>
          sortedZeroPrefix (N := N) q p ≠ sortedZeroPrefix (N := N) r p) ⊆
        (Finset.univ.filter fun p : Fin N => q ≤ p.val ∧ p.val < r) := by
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      by_cases hpq : p.val < q
      · have hpr : p.val < r := by omega
        simp [sortedZeroPrefix, hpq, hpr] at hp
      · by_cases hpr : p.val < r
        · exact ⟨by omega, hpr⟩
        · simp [sortedZeroPrefix, hpq, hpr] at hp
    have hcard := Finset.card_le_card hsubset
    have hband := interval_band_card_le (N := N) (lo := q) (hi := r)
    calc
      hammingDistance (sortedZeroPrefix (N := N) q) (sortedZeroPrefix (N := N) r) ≤
          (Finset.univ.filter fun p : Fin N => q ≤ p.val ∧ p.val < r).card := by
        exact hcard
      _ ≤ r - q := by simpa [and_comm] using hband
      _ = Chvatal.D2RankAlignment.countDistance q r := by
        simp [Chvatal.D2RankAlignment.countDistance, Nat.sub_eq_zero_of_le hqr]
  · have hrq : r ≤ q := Nat.le_of_not_ge hqr
    have hsubset :
        (Finset.univ.filter fun p : Fin N =>
          sortedZeroPrefix (N := N) q p ≠ sortedZeroPrefix (N := N) r p) ⊆
        (Finset.univ.filter fun p : Fin N => r ≤ p.val ∧ p.val < q) := by
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      by_cases hpr : p.val < r
      · have hpq : p.val < q := by omega
        simp [sortedZeroPrefix, hpr, hpq] at hp
      · by_cases hpq : p.val < q
        · exact ⟨by omega, hpq⟩
        · simp [sortedZeroPrefix, hpr, hpq] at hp
    have hcard := Finset.card_le_card hsubset
    have hband := interval_band_card_le (N := N) (lo := r) (hi := q)
    calc
      hammingDistance (sortedZeroPrefix (N := N) q) (sortedZeroPrefix (N := N) r) ≤
          (Finset.univ.filter fun p : Fin N => r ≤ p.val ∧ p.val < q).card := by
        exact hcard
      _ ≤ q - r := by simpa [and_comm] using hband
      _ = Chvatal.D2RankAlignment.countDistance q r := by
        simp [Chvatal.D2RankAlignment.countDistance, Nat.sub_eq_zero_of_le hrq]

theorem hammingDistance_sortedZero_zero {N : Nat} (v : Fin N → Bool) :
    hammingDistance v (sortedZeroPrefix 0) =
      Chvatal.D2InversionLocalization.zeroCount v := by
  classical
  simp [hammingDistance, sortedZeroPrefix,
    Chvatal.D2InversionLocalization.zeroCount,
    Chvatal.D2InversionLocalization.zeroPositions]

theorem hammingDistance_sortedZero_full {N : Nat} (v : Fin N → Bool) :
    hammingDistance v (sortedZeroPrefix (N := N) N) =
      N - Chvatal.D2InversionLocalization.zeroCount v := by
  classical
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := Finset.univ) (p := fun p : Fin N => v p = false)
  have hfalse :
      (Finset.univ.filter fun p : Fin N => v p = false).card =
        Chvatal.D2InversionLocalization.zeroCount v := rfl
  have htrue :
      (Finset.univ.filter fun p : Fin N => v p ≠ false).card =
        hammingDistance v (sortedZeroPrefix (N := N) N) := by
    simp [hammingDistance, sortedZeroPrefix]
  rw [hfalse, htrue, Finset.card_univ, Fintype.card_fin] at hsplit
  omega

/-- For every threshold input profile, after the fixed two-grid repair and
row-preserving shuffle, all inversions are confined to the common 832-wire
transition band. This gives a fixed per-sender aggregate inversion budget. -/
theorem physical_twoGridRepair_inversionCount_le_832_sq
    (h : Chvatal.D2BandRepair4096Network.Col → Nat)
    (hbound : ∀ c, h c ≤ 4096)
    (perm : Chvatal.D2BandRepair4096Network.Row →
      Equiv.Perm Chvatal.D2BandRepair4096Network.Col) :
    Chvatal.D2InversionLocalization.inversionCount
      (fun w : Wire =>
        twoGridRepair.exec (fullHeightAfterRowPermutation h perm) w) ≤
      832 * 832 := by
  obtain ⟨a, b, hwidth, hab, ha, hb, hbefore, hafter⟩ :=
    physical_twoGridRepair_common_wire_band h hbound perm
  have hinterval : 64 * b - 64 * a ≤ 832 := by
    by_cases hab : a ≤ b
    · have hmul : 64 * b - 64 * a = 64 * (b - a) := by omega
      rw [hmul]
      exact hwidth
    · have hba : b ≤ a := by omega
      have hzero : 64 * b - 64 * a = 0 := by omega
      omega
  have hband :
      (Finset.univ.filter fun w : Wire =>
        64 * a ≤ w.val ∧ w.val < 64 * b).card ≤ 832 := by
    exact (interval_band_card_le).trans hinterval
  exact inversionCount_le_of_uniform_exterior
    (fun w : Wire =>
      twoGridRepair.exec (fullHeightAfterRowPermutation h perm) w)
    hbefore hafter hband

/-- More sharply than the inversion-count bound, the physical two-grid stage
places every misplaced threshold bit within 832 ranks of its exact cut. -/
theorem physical_twoGridRepair_misplaced_bits_within_832
    (h : Chvatal.D2BandRepair4096Network.Col → Nat)
    (hbound : ∀ c, h c ≤ 4096)
    (perm : Chvatal.D2BandRepair4096Network.Row →
      Equiv.Perm Chvatal.D2BandRepair4096Network.Col) :
    (∀ w : Wire,
      (twoGridRepair.exec (fullHeightAfterRowPermutation h perm) w = false) →
      Chvatal.D2InversionLocalization.zeroCount
          (fun x : Wire =>
            twoGridRepair.exec (fullHeightAfterRowPermutation h perm) x) ≤ w.val →
      w.val < Chvatal.D2InversionLocalization.zeroCount
          (fun x : Wire =>
            twoGridRepair.exec (fullHeightAfterRowPermutation h perm) x) + 832) ∧
    (∀ w : Wire,
      (twoGridRepair.exec (fullHeightAfterRowPermutation h perm) w = true) →
      w.val < Chvatal.D2InversionLocalization.zeroCount
          (fun x : Wire =>
            twoGridRepair.exec (fullHeightAfterRowPermutation h perm) x) →
      Chvatal.D2InversionLocalization.zeroCount
          (fun x : Wire =>
            twoGridRepair.exec (fullHeightAfterRowPermutation h perm) x) ≤ w.val + 832) := by
  obtain ⟨a, b, hwidth, hab, ha, hb, hbefore, hafter⟩ :=
    physical_twoGridRepair_common_wire_band h hbound perm
  have hinterval : 64 * b - 64 * a ≤ 832 := by
    by_cases hab' : a ≤ b
    · have hmul : 64 * b - 64 * a = 64 * (b - a) := by omega
      rw [hmul]
      exact hwidth
    · have hba : b ≤ a := by omega
      have hzero : 64 * b - 64 * a = 0 := by omega
      omega
  exact misplaced_bits_within_uniform_exterior_band
    (fun w : Wire =>
      twoGridRepair.exec (fullHeightAfterRowPermutation h perm) w)
    ha hb hinterval hbefore hafter

/-- If every threshold of a permutation-valued output is the fixed physical
two-grid output for some bounded height profile, the 832-wire threshold-band
provider upgrades to a pointwise key-rank displacement bound. The remaining
network-specific obligation is to establish `hmatch` by threshold
commutation through the initial column sort and fixed row permutations. -/
theorem physical_twoGrid_threshold_family_rank_displacement
    (out : Wire → Wire) (hbij : Function.Bijective out)
    (height : Nat → Chvatal.D2BandRepair4096Network.Col → Nat)
    (perm : Chvatal.D2BandRepair4096Network.Row →
      Equiv.Perm Chvatal.D2BandRepair4096Network.Col)
    (hbound : ∀ q c, height q c ≤ 4096)
    (hmatch : ∀ q w, rankThresholdWord out q w =
      twoGridRepair.exec (fullHeightAfterRowPermutation (height q) perm) w) :
    ∀ w, (out w).val ≤ w.val + 832 ∧ w.val ≤ (out w).val + 832 := by
  apply Chvatal.D2BlockSortDisplacement.localized_threshold_errors_give_pointwise_rank_displacement
  · intro q w hp hq
    have hqN : q ≤ 4096 * 64 := by omega
    have hzero := threshold_zeroCount_eq hbij hqN
    have hprovider := physical_twoGridRepair_misplaced_bits_within_832
      (height q) (hbound q) perm
    have heq : rankThresholdWord out q =
        twoGridRepair.exec (fullHeightAfterRowPermutation (height q) perm) :=
      funext (hmatch q)
    have hproviderZero :
        Chvatal.D2InversionLocalization.zeroCount
          (twoGridRepair.exec (fullHeightAfterRowPermutation (height q) perm)) = q := by
      rw [← heq]
      exact hzero
    have htrue : twoGridRepair.exec
        (fullHeightAfterRowPermutation (height q) perm) w = true := by
      rw [← hmatch q w]
      simp [rankThresholdWord, Nat.not_lt.mpr hq]
    have hlocal := hprovider.2 w htrue (by simpa [hproviderZero] using hp)
    simpa [hproviderZero] using hlocal
  · intro q w hq hp
    have hqN : q ≤ 4096 * 64 := by omega
    have hzero := threshold_zeroCount_eq hbij hqN
    have hprovider := physical_twoGridRepair_misplaced_bits_within_832
      (height q) (hbound q) perm
    have heq : rankThresholdWord out q =
        twoGridRepair.exec (fullHeightAfterRowPermutation (height q) perm) :=
      funext (hmatch q)
    have hproviderZero :
        Chvatal.D2InversionLocalization.zeroCount
          (twoGridRepair.exec (fullHeightAfterRowPermutation (height q) perm)) = q := by
      rw [← heq]
      exact hzero
    have hfalse : twoGridRepair.exec
        (fullHeightAfterRowPermutation (height q) perm) w = false := by
      rw [← hmatch q w]
      simp [rankThresholdWord, hp]
    have hlocal := hprovider.1 w hfalse (by simpa [hproviderZero] using hq)
    simpa [hproviderZero] using hlocal


/-- The same physical common band bounds the total number of wrong-side wires
at the sender's exact threshold cut by 832. -/
theorem physical_twoGridRepair_wrong_population_le_832
    (h : Chvatal.D2BandRepair4096Network.Col → Nat)
    (hbound : ∀ c, h c ≤ 4096)
    (perm : Chvatal.D2BandRepair4096Network.Row →
      Equiv.Perm Chvatal.D2BandRepair4096Network.Col) :
    (Chvatal.D2InversionLocalization.cutWrongOnes
      (fun w : Wire =>
        twoGridRepair.exec (fullHeightAfterRowPermutation h perm) w)
      (Chvatal.D2InversionLocalization.zeroCount
        (fun w : Wire =>
          twoGridRepair.exec (fullHeightAfterRowPermutation h perm) w))).card +
    (Chvatal.D2InversionLocalization.cutWrongZeros
      (fun w : Wire =>
        twoGridRepair.exec (fullHeightAfterRowPermutation h perm) w)
      (Chvatal.D2InversionLocalization.zeroCount
        (fun w : Wire =>
          twoGridRepair.exec (fullHeightAfterRowPermutation h perm) w))).card ≤ 832 := by
  obtain ⟨a, b, hwidth, hab, ha, hb, hbefore, hafter⟩ :=
    physical_twoGridRepair_common_wire_band h hbound perm
  have hinterval : 64 * b - 64 * a ≤ 832 := by
    by_cases hab' : a ≤ b
    · have hmul : 64 * b - 64 * a = 64 * (b - a) := by omega
      rw [hmul]
      exact hwidth
    · have hba : b ≤ a := by omega
      have hzero : 64 * b - 64 * a = 0 := by omega
      omega
  exact misplaced_population_le_uniform_exterior_band
    (fun w : Wire =>
      twoGridRepair.exec (fullHeightAfterRowPermutation h perm) w)
    ha hb hinterval hbefore hafter

/-- The fixed two-grid repair is within 832 wire changes of the sorted Boolean
word with the same exact zero count. -/
theorem physical_twoGridRepair_hamming_le_832
    (h : Chvatal.D2BandRepair4096Network.Col → Nat)
    (hbound : ∀ c, h c ≤ 4096)
    (perm : Chvatal.D2BandRepair4096Network.Row →
      Equiv.Perm Chvatal.D2BandRepair4096Network.Col) :
    hammingDistance
      (fun w : Wire =>
        twoGridRepair.exec (fullHeightAfterRowPermutation h perm) w)
      (sortedZeroPrefix (N := 4096 * 64)
        (Chvatal.D2InversionLocalization.zeroCount
        (fun w : Wire =>
          twoGridRepair.exec (fullHeightAfterRowPermutation h perm) w))) ≤ 832 := by
  rw [hammingDistance_eq_cut_wrong_population]
  exact physical_twoGridRepair_wrong_population_le_832 h hbound perm

end Chvatal.D2BandRepairInversion
