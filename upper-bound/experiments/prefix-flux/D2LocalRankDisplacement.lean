import D2BandRepairInversion
import D2Slope35Physical4096

open Chvatal.D2BandRepair4096Network
open Chvatal.D2BandRepairInversion
open Chvatal.D2Slope35Physical4096
open Chvatal.D2Slope25Physical
open Chvatal.D2RankAlignment
open Chvatal.D2TwoGridPhysicalBand

namespace Chvatal.D2LocalRankDisplacement

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

abbrev Wire := Fin (4096 * 64)
abbrev Col := Fin 64
abbrev Row := Fin 4096

private def columnSort : ComparatorNetwork (4096 * 64) :=
  Chvatal.columnSortNetwork 4096 64 (by omega)

private def perm35 : Equiv.Perm Wire :=
  Chvatal.rowScrambleWirePerm 4096 64 (by omega) scramble35

private def perm25 : Equiv.Perm Wire :=
  Chvatal.rowScrambleWirePerm 4096 64 (by omega) (fun r => affine25 r)

private def permRows (perm : Row → Equiv.Perm Col) : Equiv.Perm Wire :=
  Chvatal.rowScrambleWirePerm 4096 64 (by omega) perm

/-- The fixed two-shuffle prefix, lifted from Boolean profiles to arbitrary
rank values. Its input is already ordered down each column. -/
noncomputable def physicalTwoShuffleKeys (v : Wire → Wire) : Wire → Wire :=
  let first := columnSort.exec (Function.comp v perm35.symm)
  let secondInput := Function.comp (Function.comp first reorientWirePerm) perm25.symm
  columnSort.exec secondInput

/-- The complete local macro: two physical shuffles, a row-preserving
column permutation, and the fixed two-grid band repair. -/
noncomputable def localCore (v : Wire → Wire) (perm : Row → Equiv.Perm Col) : Wire → Wire :=
  twoGridRepair.exec
    (Function.comp (physicalTwoShuffleKeys v)
      (permRows (fun r => (perm r).symm)).symm)

private def thresholdMap (q : Nat) (x : Wire) : Bool :=
  if x.val < q then false else true

private theorem thresholdMap_monotone (q : Nat) : Monotone (thresholdMap q) := by
  intro a b hab
  have habv := Fin.le_iff_val_le_val.mp hab
  by_cases ha : a.val < q
  · by_cases hb : b.val < q
    · simp [thresholdMap, ha, hb]
    · simp [thresholdMap, ha, hb]
  · have hb : ¬ b.val < q := by omega
    simp [thresholdMap, ha, hb]

private theorem threshold_exec (net : ComparatorNetwork (4096 * 64))
    (v : Wire → Wire) (q : Nat) :
    rankThresholdWord (net.exec v) q = net.exec (rankThresholdWord v q) := by
  change thresholdMap q ∘ net.exec v = net.exec (thresholdMap q ∘ v)
  exact net.exec_comp_monotone (thresholdMap_monotone q) v

private theorem rankThreshold_comp (v : Wire → Wire) (e : Equiv.Perm Wire) (q : Nat) :
    rankThresholdWord (Function.comp v e) q =
      Function.comp (rankThresholdWord v q) e := rfl

private theorem antitone_bool_eq_topPrefix (s : Row → Bool) (hs : Antitone s) :
    ∀ r, s r = decide (r.val < (Finset.univ.filter fun i : Row => s i = true).card) := by
  classical
  intro r
  by_cases hr : s r = true
  · have hsubset : Finset.Iic r ⊆ Finset.univ.filter fun i : Row => s i = true := by
      intro i hi
      have hir : i ≤ r := Finset.mem_Iic.mp hi
      have hmono := hs hir
      have htrue : true ≤ s i := by simpa [hr] using hmono
      have hsi : s i = true := by
        cases hs_i : s i with
        | false =>
            rw [hs_i] at htrue
            exact False.elim ((by decide : ¬ (true ≤ false)) htrue)
        | true => rfl
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsi⟩
    have hcard := Finset.card_le_card hsubset
    have hIic : (Finset.Iic r).card = r.val + 1 := by simp
    rw [hIic] at hcard
    have hcount : r.val + 1 ≤
        (Finset.univ.filter fun i : Row => s i = true).card := by omega
    rw [hr]
    exact (decide_eq_true (by omega)).symm
  · have hfalse : s r = false := by cases h : s r <;> simp_all
    have hsubset : (Finset.univ.filter fun i : Row => s i = true) ⊆ Finset.Iio r := by
      intro i hi
      have htrue : s i = true := (Finset.mem_filter.mp hi).2
      have hir : i < r := by
        by_contra hn
        have hri : r ≤ i := le_of_not_gt hn
        have hmono := hs hri
        rw [hfalse, htrue] at hmono
        exact (by decide : ¬ (true ≤ false)) hmono
      exact Finset.mem_Iio.mpr hir
    have hcard := Finset.card_le_card hsubset
    have hIio : (Finset.Iio r).card = r.val := by simp
    rw [hIio] at hcard
    have hcount :
        (Finset.univ.filter fun i : Row => s i = true).card ≤ r.val := by omega
    rw [hfalse]
    exact (decide_eq_false (by omega)).symm

def thresholdHeight (v : Wire → Wire) (q : Nat) (c : Col) : Nat :=
  Chvatal.matrixColumnTrueCount c (rankThresholdWord v q)

private theorem threshold_eq_topPrefix (v : Wire → Wire) (q : Nat)
    (hdesc : ∀ (c : Col) (r s : Row), r.val ≤ s.val →
      (v (Chvatal.matrixWire 4096 64 s c)).val ≤
        (v (Chvatal.matrixWire 4096 64 r c)).val) :
    rankThresholdWord v q = topPrefix (thresholdHeight v q) := by
  funext w
  rw [← Chvatal.matrixWire_matrixRow_col (by omega) w]
  let r : Row := Chvatal.matrixRow 4096 64 (by omega) w
  let c : Col := Chvatal.matrixCol 4096 64 (by omega) w
  have hanti : Antitone (fun i : Row =>
      rankThresholdWord v q (Chvatal.matrixWire 4096 64 i c)) := by
    intro i j hij
    have hval := hdesc c i j (Fin.le_iff_val_le_val.mp hij)
    by_cases hi : (v (Chvatal.matrixWire 4096 64 i c)).val < q
    · have hj : (v (Chvatal.matrixWire 4096 64 j c)).val < q := by omega
      simp [rankThresholdWord, hi, hj]
    · simp only [rankThresholdWord]
      by_cases hj : (v (Chvatal.matrixWire 4096 64 j c)).val < q <;>
        simp [hi, hj]
  have hprofile := antitone_bool_eq_topPrefix
    (fun i : Row => rankThresholdWord v q (Chvatal.matrixWire 4096 64 i c)) hanti r
  calc
    rankThresholdWord v q (Chvatal.matrixWire 4096 64 r c) =
        decide (r.val <
          (Finset.univ.filter fun i : Row =>
            rankThresholdWord v q (Chvatal.matrixWire 4096 64 i c) = true).card) := hprofile
    _ = topPrefix (thresholdHeight v q) (Chvatal.matrixWire 4096 64 r c) := by
      simp [topPrefix, thresholdHeight, matrixColumnTrueCount,
        Chvatal.matrixWire_row_col]

private theorem threshold_physical_twoShuffleKeys
    (v : Wire → Wire) (q : Nat)
    (hdesc : ∀ (c : Col) (r s : Row), r.val ≤ s.val →
      (v (Chvatal.matrixWire 4096 64 s c)).val ≤
        (v (Chvatal.matrixWire 4096 64 r c)).val) :
    rankThresholdWord (physicalTwoShuffleKeys v) q =
      bottomUnaryProfile (fullHeightTwoShuffle (thresholdHeight v q)) := by
  let h := thresholdHeight v q
  have htop : rankThresholdWord v q = topPrefix h :=
    threshold_eq_topPrefix v q hdesc
  have hbound : ∀ c, h c ≤ 4096 := by
    intro c
    exact Chvatal.matrixColumnTrueCount_le c (rankThresholdWord v q)
  have hfirst : rankThresholdWord
      (columnSort.exec (Function.comp v perm35.symm)) q =
      bottomUnaryProfile (slope35PhysicalOutputHeight h) := by
    rw [threshold_exec]
    change (Chvatal.columnSortNetwork 4096 64 (by omega)).exec
      (Function.comp (rankThresholdWord v q) perm35.symm) = _
    rw [htop]
    change (Chvatal.columnSortNetwork 4096 64 (by omega)).exec
      (Function.comp (topPrefix h) perm35.symm) = _
    rw [show Function.comp (topPrefix h) perm35.symm =
      Chvatal.D2Slope35Physical4096.scrambledTopPrefix h by
        funext w
        rfl]
    exact slope35SortPhysical_eq_bottomUnaryProfile h hbound
  have hinput : rankThresholdWord
      (Function.comp
        (Function.comp (columnSort.exec (Function.comp v perm35.symm)) reorientWirePerm)
        perm25.symm) q = physicalTwoShuffleInput h := by
    have hcomp25 := rankThreshold_comp
      (Function.comp (columnSort.exec (Function.comp v perm35.symm)) reorientWirePerm)
      perm25.symm q
    have hcompReorient := rankThreshold_comp
      (columnSort.exec (Function.comp v perm35.symm)) reorientWirePerm q
    calc
      rankThresholdWord
          (Function.comp
            (Function.comp (columnSort.exec (Function.comp v perm35.symm)) reorientWirePerm)
            perm25.symm) q = Function.comp
          (rankThresholdWord
            (Function.comp (columnSort.exec (Function.comp v perm35.symm)) reorientWirePerm) q)
          perm25.symm := hcomp25
      _ = Function.comp
            (Function.comp
              (rankThresholdWord (columnSort.exec (Function.comp v perm35.symm)) q)
              reorientWirePerm)
            perm25.symm := by rw [hcompReorient]
      _ = Function.comp
            (Function.comp (bottomUnaryProfile (slope35PhysicalOutputHeight h))
              reorientWirePerm)
            perm25.symm := by rw [hfirst]
      _ = physicalTwoShuffleInput h := by
        funext w
        rfl
  have hsecond : rankThresholdWord (physicalTwoShuffleKeys v) q =
      bottomUnaryProfile (fullHeightTwoShuffle h) := by
    rw [physicalTwoShuffleKeys, threshold_exec, hinput]
    exact fullHeightTwoShuffle_physical h hbound
  simpa [h] using hsecond

private theorem exec_bijective {n : Nat} (net : ComparatorNetwork n)
    (v : Fin n → Fin n) (hv : Function.Bijective v) :
    Function.Bijective (net.exec v) := by
  obtain ⟨ρ, hρ⟩ := ComparatorNetwork.exec_eq_comp_perm net v
  rw [hρ]
  exact hv.comp ρ.bijective

private theorem comp_perm_bijective {n : Nat} (v : Fin n → Fin n)
    (e : Equiv.Perm (Fin n)) (hv : Function.Bijective v) :
    Function.Bijective (Function.comp v e) := hv.comp e.bijective

private theorem localCore_threshold_match
    (v : Wire → Wire) (perm : Row → Equiv.Perm Col) (q : Nat)
    (hdesc : ∀ (c : Col) (r s : Row), r.val ≤ s.val →
      (v (Chvatal.matrixWire 4096 64 s c)).val ≤
        (v (Chvatal.matrixWire 4096 64 r c)).val) :
    rankThresholdWord (localCore v perm) q =
      twoGridRepair.exec
        (fullHeightAfterRowPermutation (thresholdHeight v q) perm) := by
  let pRows := permRows (fun r => (perm r).symm)
  have hshuffle := threshold_physical_twoShuffleKeys v q hdesc
  have hcomm := threshold_exec twoGridRepair
    (Function.comp (physicalTwoShuffleKeys v) pRows.symm) q
  have hroute : rankThresholdWord
      (Function.comp (physicalTwoShuffleKeys v) pRows.symm) q =
      Function.comp (rankThresholdWord (physicalTwoShuffleKeys v) q) pRows.symm :=
    rankThreshold_comp (physicalTwoShuffleKeys v) pRows.symm q
  funext w
  calc
    rankThresholdWord (localCore v perm) q w =
        twoGridRepair.exec
          (rankThresholdWord (Function.comp (physicalTwoShuffleKeys v) pRows.symm) q) w := by
      have hpoint := congrFun hcomm w
      exact hpoint
    _ = twoGridRepair.exec
        (Function.comp (rankThresholdWord (physicalTwoShuffleKeys v) q) pRows.symm) w := by
      rw [hroute]
    _ = twoGridRepair.exec
        (fullHeightAfterRowPermutation (thresholdHeight v q) perm) w := by
      rw [hshuffle]
      rfl

/-- The fixed local macro changes the input's descending column orientation
to the standard ascending orientation. -/
theorem localCore_restores_columnMonotone
    (v : Wire → Wire) (perm : Row → Equiv.Perm Col)
    (hdesc : ∀ (c : Col) (r s : Row), r.val ≤ s.val →
      (v (Chvatal.matrixWire 4096 64 s c)).val ≤
        (v (Chvatal.matrixWire 4096 64 r c)).val) :
    ∀ (c : Col) (r s : Row), r.val ≤ s.val →
      (localCore v perm (Chvatal.matrixWire 4096 64 r c)).val ≤
        (localCore v perm (Chvatal.matrixWire 4096 64 s c)).val := by
  intro c r s hrs
  by_contra hnot
  have hrev :
      (localCore v perm (Chvatal.matrixWire 4096 64 s c)).val <
        (localCore v perm (Chvatal.matrixWire 4096 64 r c)).val := by omega
  let q := (localCore v perm (Chvatal.matrixWire 4096 64 r c)).val
  have hsorted := physical_twoGridRepair_restores_columnMonotone
    (thresholdHeight v q) (by
      intro d
      exact Chvatal.matrixColumnTrueCount_le d (rankThresholdWord v q)) perm c hrs
  have hfalse : rankThresholdWord (localCore v perm) q
      (Chvatal.matrixWire 4096 64 s c) = false := by
    simp [rankThresholdWord, q]
    omega
  have htrue : rankThresholdWord (localCore v perm) q
      (Chvatal.matrixWire 4096 64 r c) = true := by
    simp [rankThresholdWord, q]
  have hmatch := localCore_threshold_match v perm q hdesc
  rw [hmatch] at htrue hfalse
  change twoGridRepair.exec
      (fullHeightAfterRowPermutation (thresholdHeight v q) perm)
      (Chvatal.matrixWire 4096 64 r c) ≤
    twoGridRepair.exec
      (fullHeightAfterRowPermutation (thresholdHeight v q) perm)
      (Chvatal.matrixWire 4096 64 s c) at hsorted
  rw [htrue, hfalse] at hsorted
  exact (by decide : ¬ (true ≤ false)) hsorted

/-- Reverse the row coordinate of a fixed tile, keeping columns fixed. This is
the wire reindexing that converts an ascending-column output back to the
descending-column convention expected by the next local core. -/
def reverseRowsWire (w : Wire) : Wire :=
  Chvatal.matrixWire 4096 64
    (Fin.rev (Chvatal.matrixRow 4096 64 (by omega) w))
    (Chvatal.matrixCol 4096 64 (by omega) w)

theorem reverseRowsWire_matrixWire (r : Row) (c : Col) :
    reverseRowsWire (Chvatal.matrixWire 4096 64 r c) =
      Chvatal.matrixWire 4096 64 (Fin.rev r) c := by
  simp [reverseRowsWire, Chvatal.matrixWire_row_col]

/-- Reversing the row wiring after the local core restores its descending
column input contract. -/
theorem localCore_reverseRows_descending
    (v : Wire → Wire) (perm : Row → Equiv.Perm Col)
    (hdesc : ∀ (c : Col) (r s : Row), r.val ≤ s.val →
      (v (Chvatal.matrixWire 4096 64 s c)).val ≤
        (v (Chvatal.matrixWire 4096 64 r c)).val) :
    ∀ (c : Col) (r s : Row), r.val ≤ s.val →
      (localCore v perm (reverseRowsWire (Chvatal.matrixWire 4096 64 s c))).val ≤
        (localCore v perm (reverseRowsWire (Chvatal.matrixWire 4096 64 r c))).val := by
  intro c r s hrs
  have hrev : Fin.rev s ≤ Fin.rev r := by
    apply Fin.le_iff_val_le_val.mpr
    simp only [Fin.val_rev]
    omega
  have hmono := localCore_restores_columnMonotone v perm hdesc c
    (Fin.rev s) (Fin.rev r) hrev
  simpa only [reverseRowsWire_matrixWire] using hmono

/-- The local macro is a permutation of the tile values whenever its input is.
This exposes the bijectivity fact used internally by the rank-displacement
proof so the all-prefix escape interface can use the inverse output map. -/
theorem localCore_bijective
    (v : Wire → Wire) (hbij : Function.Bijective v)
    (perm : Row → Equiv.Perm Col) : Function.Bijective (localCore v perm) := by
  let pRows := permRows (fun r => (perm r).symm)
  have hpre := exec_bijective columnSort
    (Function.comp v perm35.symm) (comp_perm_bijective v perm35.symm hbij)
  have hmid := exec_bijective columnSort
    (Function.comp (Function.comp (columnSort.exec (Function.comp v perm35.symm))
      reorientWirePerm) perm25.symm)
    (comp_perm_bijective
      (Function.comp (columnSort.exec (Function.comp v perm35.symm)) reorientWirePerm)
      perm25.symm (comp_perm_bijective _ reorientWirePerm hpre))
  exact exec_bijective twoGridRepair
    (Function.comp (physicalTwoShuffleKeys v) pRows.symm)
    (comp_perm_bijective (physicalTwoShuffleKeys v) pRows.symm hmid)

theorem localCore_rank_displacement
    (v : Wire → Wire) (hbij : Function.Bijective v)
    (perm : Row → Equiv.Perm Col)
    (hdesc : ∀ (c : Col) (r s : Row), r.val ≤ s.val →
      (v (Chvatal.matrixWire 4096 64 s c)).val ≤
        (v (Chvatal.matrixWire 4096 64 r c)).val) :
    ∀ w, (localCore v perm w).val ≤ w.val + 832 ∧
      w.val ≤ (localCore v perm w).val + 832 := by
  let pRows := permRows (fun r => (perm r).symm)
  have hpre := exec_bijective columnSort
    (Function.comp v perm35.symm) (comp_perm_bijective v perm35.symm hbij)
  have hmid := exec_bijective columnSort
    (Function.comp (Function.comp (columnSort.exec (Function.comp v perm35.symm))
      reorientWirePerm) perm25.symm)
    (comp_perm_bijective
      (Function.comp (columnSort.exec (Function.comp v perm35.symm)) reorientWirePerm)
      perm25.symm (comp_perm_bijective _ reorientWirePerm hpre))
  have hout := exec_bijective twoGridRepair
    (Function.comp (physicalTwoShuffleKeys v) pRows.symm)
    (comp_perm_bijective (physicalTwoShuffleKeys v) pRows.symm hmid)
  have hmatch : ∀ q w, rankThresholdWord (localCore v perm) q w =
      twoGridRepair.exec
        (fullHeightAfterRowPermutation (thresholdHeight v q) perm) w := by
    intro q w
    exact congrFun (localCore_threshold_match v perm q hdesc) w
  exact physical_twoGrid_threshold_family_rank_displacement
    (localCore v perm) hout (thresholdHeight v) perm
    (by
      intro q c
      exact Chvatal.matrixColumnTrueCount_le c (rankThresholdWord v q))
    hmatch

end Chvatal.D2LocalRankDisplacement
