import D2RankAlignment
import D2BandRepairInversion

/-! A rank partition has at most one tile containing a fixed threshold cut.
If pure tiles incur only their incoming count mismatch, the local sorting
error is charged once, on the unique mixed tile, rather than once per tile.
This is a generic arithmetic interface; the D2 address/routing hypotheses
needed to instantiate it are separate. -/

namespace Chvatal.D2SparseMixedTileTransfer

open Chvatal.D2RankAlignment
open Chvatal.D2BandRepairInversion
open Chvatal.D2BandRepair4096Network
open Chvatal.D2TwoGridPhysicalBand
open scoped BigOperators

abbrev TileWire := Fin (4096 * 64)

theorem zeroCount_le_tile_size (v : TileWire → Bool) :
    Chvatal.D2InversionLocalization.zeroCount v ≤ 4096 * 64 := by
  calc
    Chvatal.D2InversionLocalization.zeroCount v =
        (Chvatal.D2InversionLocalization.zeroPositions v).card := rfl
    _ ≤ Finset.univ.card := Finset.card_le_univ _
    _ = 4096 * 64 := by simp

/-- On a pure target tile, the error is exactly its count mismatch. On a mixed
tile, triangle inequality adds the local fixed-core repair budget once. -/
theorem tile_error_le_count_error_plus_mixed_budget
    (v : TileWire → Bool) (target W : Nat)
    (htarget : target ≤ 4096 * 64)
    (hlocal : hammingDistance v
      (sortedZeroPrefix (N := 4096 * 64)
        (Chvatal.D2InversionLocalization.zeroCount v)) ≤ W) :
    hammingDistance v (sortedZeroPrefix (N := 4096 * 64) target) ≤
      Chvatal.D2RankAlignment.countDistance
        (Chvatal.D2InversionLocalization.zeroCount v) target +
        (if 0 < target ∧ target < 4096 * 64 then W else 0) := by
  let actual := Chvatal.D2InversionLocalization.zeroCount v
  have hactual : actual ≤ 4096 * 64 := zeroCount_le_tile_size v
  by_cases hzero : target = 0
  · subst target
    rw [hammingDistance_sortedZero_zero]
    simp [Chvatal.D2RankAlignment.countDistance]
  by_cases hfull : target = 4096 * 64
  · subst target
    rw [hammingDistance_sortedZero_full]
    simp [actual, Chvatal.D2RankAlignment.countDistance, hactual]
  have htarget_pos : 0 < target := by omega
  have htarget_lt : target < 4096 * 64 := by omega
  calc
    hammingDistance v (sortedZeroPrefix (N := 4096 * 64) target) ≤
        hammingDistance v (sortedZeroPrefix (N := 4096 * 64) actual) +
          hammingDistance
            (sortedZeroPrefix (N := 4096 * 64) actual)
            (sortedZeroPrefix (N := 4096 * 64) target) :=
      hammingDistance_triangle _ _ _
    _ ≤ W + Chvatal.D2RankAlignment.countDistance actual target := by
      have hsorted := hammingDistance_sortedZero_le_countDistance
        (N := 4096 * 64) actual target hactual htarget
      simpa [actual] using Nat.add_le_add hlocal hsorted
    _ = Chvatal.D2RankAlignment.countDistance actual target + W := by omega
    _ = Chvatal.D2RankAlignment.countDistance
          (Chvatal.D2InversionLocalization.zeroCount v) target +
        (if 0 < target ∧ target < 4096 * 64 then W else 0) := by
      simp [actual, htarget_pos, htarget_lt]

/-- A monotone interval partition has at most one interval containing a given
prefix cut strictly in its interior. -/
theorem prefix_partition_at_most_one_mixed
    {T : Nat} (bounds : Nat → Nat) (H : Nat)
    (hmono : ∀ i j, i ≤ j → bounds i ≤ bounds j) :
    (Finset.univ.filter fun i : Fin T =>
      0 < prefixIntervalMass H (bounds i.val) (bounds (i.val + 1)) ∧
        prefixIntervalMass H (bounds i.val) (bounds (i.val + 1)) <
          bounds (i.val + 1) - bounds i.val).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro i hi j hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
  have hwidth_i : bounds i.val ≤ bounds (i.val + 1) :=
    hmono i.val (i.val + 1) (Nat.le_succ _)
  have hwidth_j : bounds j.val ≤ bounds (j.val + 1) :=
    hmono j.val (j.val + 1) (Nat.le_succ _)
  have hiCut : bounds i.val < H ∧ H < bounds (i.val + 1) := by
    unfold prefixIntervalMass at hi
    omega
  have hjCut : bounds j.val < H ∧ H < bounds (j.val + 1) := by
    unfold prefixIntervalMass at hj
    omega
  by_contra hne
  have hval : i.val ≠ j.val := by
    intro heq
    apply hne
    exact Fin.ext heq
  have horder : i.val < j.val ∨ j.val < i.val := by omega
  rcases horder with hij | hji
  · have hbetween := hmono (i.val + 1) j.val (by omega)
    omega
  · have hbetween := hmono (j.val + 1) i.val (by omega)
    omega

theorem sum_error_le_parent_error_add_mixed_budget
    {T : Nat} (baseError tileError : Fin T -> Nat)
    (mixed : Fin T -> Prop) [DecidablePred mixed] (W B : Nat)
    (hmixed : (Finset.univ.filter mixed).card <= B)
    (herror : forall i, tileError i <= baseError i + (if mixed i then W else 0)) :
    (Finset.univ.sum fun i : Fin T => tileError i) <=
      (Finset.univ.sum fun i : Fin T => baseError i) + W * B := by
  calc
    (Finset.univ.sum fun i : Fin T => tileError i) <=
        Finset.univ.sum fun i : Fin T =>
          baseError i + (if mixed i then W else 0) :=
      Finset.sum_le_sum fun i hi => herror i
    _ = (Finset.univ.sum fun i : Fin T =>
          baseError i) + W * (Finset.univ.filter mixed).card := by
      rw [Finset.sum_add_distrib]
      congr 1
      rw [← Finset.sum_filter]
      simp
      exact Nat.mul_comm _ _
    _ <= (Finset.univ.sum fun i : Fin T => baseError i) + W * B :=
      Nat.add_le_add_left (Nat.mul_le_mul_left W hmixed) _

theorem sum_error_le_parent_error_add_single_mixed
    {T : Nat} (tileLength targetCount actualCount tileError : Fin T -> Nat)
    (W : Nat)
    (hmixed : (Finset.univ.filter fun i : Fin T =>
      0 < targetCount i ∧ targetCount i < tileLength i).card <= 1)
    (herror : forall i,
      tileError i <= countDistance (actualCount i) (targetCount i) +
        (if 0 < targetCount i ∧ targetCount i < tileLength i then W else 0)) :
    (Finset.univ.sum fun i : Fin T => tileError i) <=
      (Finset.univ.sum fun i : Fin T =>
        countDistance (actualCount i) (targetCount i)) + W := by
  have h := sum_error_le_parent_error_add_mixed_budget
    (fun i => countDistance (actualCount i) (targetCount i)) tileError
    (fun i => 0 < targetCount i ∧ targetCount i < tileLength i) W 1
    (by simpa using hmixed) herror
  simpa using h

/-- The mixed-tile sum bound specialized to target masses cut from one global
rank prefix. -/
theorem sum_error_le_parent_error_add_single_prefix_boundary
    {T : Nat} (bounds : Nat → Nat) (H W : Nat)
    (tileLength targetCount actualCount tileError : Fin T → Nat)
    (hmono : ∀ i j, i ≤ j → bounds i ≤ bounds j)
    (htileLength : ∀ i, tileLength i = bounds (i.val + 1) - bounds i.val)
    (htarget : ∀ i,
      targetCount i = prefixIntervalMass H (bounds i.val) (bounds (i.val + 1)))
    (herror : ∀ i,
      tileError i ≤ countDistance (actualCount i) (targetCount i) +
        (if 0 < targetCount i ∧ targetCount i < tileLength i then W else 0)) :
    (Finset.univ.sum fun i : Fin T => tileError i) ≤
      (Finset.univ.sum fun i : Fin T =>
        countDistance (actualCount i) (targetCount i)) + W := by
  apply sum_error_le_parent_error_add_single_mixed
  · have hmixed := prefix_partition_at_most_one_mixed (T := T) bounds H hmono
    simpa [htileLength, htarget] using hmixed
  · simpa [htileLength] using herror

/-- Concrete physical two-grid version of the mixed-tile transfer on
full-sized tiles. The tiles form a monotone partition of global rank space;
each tile runs the checked fixed repair. The total Hamming mismatch after
repair is at most the incoming tile-count error plus 832, independent of the
number of tiles. Partial tiles need a live-wire Hamming statement. -/
theorem tiled_physical_repair_hamming_le_parent_add_832
    {T : Nat} (bounds : Nat → Nat) (H : Nat)
    (sourceHeight : Fin T → Chvatal.D2BandRepair4096Network.Col → Nat)
    (perm : Fin T → Chvatal.D2BandRepair4096Network.Row →
      Equiv.Perm Chvatal.D2BandRepair4096Network.Col)
    (hmono : ∀ i j, i ≤ j → bounds i ≤ bounds j)
    (hcomplete : ∀ i : Fin T, bounds (i.val + 1) - bounds i.val = 4096 * 64)
    (hbound : ∀ i c, sourceHeight i c ≤ 4096) :
    (Finset.univ.sum fun i : Fin T =>
      hammingDistance
        (fun w : TileWire =>
          twoGridRepair.exec
            (fullHeightAfterRowPermutation
              (sourceHeight i) (perm i)) w)
        (sortedZeroPrefix (N := 4096 * 64)
          (prefixIntervalMass H (bounds i.val) (bounds (i.val + 1))))) ≤
      (Finset.univ.sum fun i : Fin T =>
        Chvatal.D2RankAlignment.countDistance
          (Chvatal.D2InversionLocalization.zeroCount
            (fullHeightAfterRowPermutation
              (sourceHeight i) (perm i)))
          (prefixIntervalMass H (bounds i.val) (bounds (i.val + 1)))) + 832 := by
  apply sum_error_le_parent_error_add_single_prefix_boundary
    bounds H 832
    (fun i => bounds (i.val + 1) - bounds i.val)
    (fun i => prefixIntervalMass H (bounds i.val) (bounds (i.val + 1)))
    (fun i => Chvatal.D2InversionLocalization.zeroCount
      (fullHeightAfterRowPermutation (sourceHeight i) (perm i)))
    (fun i => hammingDistance
      (fun w : TileWire =>
        twoGridRepair.exec
          (fullHeightAfterRowPermutation
            (sourceHeight i) (perm i)) w)
      (sortedZeroPrefix (N := 4096 * 64)
        (prefixIntervalMass H (bounds i.val) (bounds (i.val + 1)))))
  · exact hmono
  · intro i
    rfl
  · intro i
    rfl
  · intro i
    have htarget : prefixIntervalMass H (bounds i.val) (bounds (i.val + 1)) ≤
        4096 * 64 := by
      unfold prefixIntervalMass
      exact (Nat.min_le_right _ _).trans (by rw [hcomplete i])
    have htile := tile_error_le_count_error_plus_mixed_budget _ _ _ htarget
      (Chvatal.D2BandRepairInversion.physical_twoGridRepair_hamming_le_832
        (sourceHeight i) (hbound i) (perm i))
    rw [Chvatal.D2BandRepairInversion.physical_twoGridRepair_zeroCount_eq] at htile
    simpa [hcomplete] using htile

end Chvatal.D2SparseMixedTileTransfer
