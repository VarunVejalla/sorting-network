import CyclicPermScratch
import CyclicResidueCount
import AKS.Chvatal.Lemma61
import Mathlib.Tactic

namespace Tapered945
open Chvatal

set_option maxHeartbeats 500000

/-- The destination column's source is obtained by the row permutation inverse. -/
theorem mem_scrambledRowOnes_iff {m : Nat} (c : MonotoneColumnSums m 16)
    (σ : Scramble m 16) (r : Fin m) (j : Fin 16) :
    j ∈ scrambledRowOnes c σ r ↔ (σ r).symm j ∈ monotoneRowOnes c r := by
  simp only [scrambledRowOnes, Finset.mem_image]
  constructor
  · rintro ⟨k, hk, hkj⟩
    have hk' : (σ r).symm j = k := by
      simpa using (congrArg (σ r).symm hkj).symm
    simpa [hk'] using hk
  · intro hj
    exact ⟨(σ r).symm j, hj, Equiv.apply_symm_apply (σ r) j⟩

/-- Expand a scrambled column sum as occupancy of the unique source column
that maps to the destination in each row. -/
theorem scrambledColSum_eq_preimage_rows {m : Nat} (c : MonotoneColumnSums m 16)
    (σ : Scramble m 16) (j : Fin 16) :
    scrambledColSum c σ j =
      ∑ r : Fin m, if (σ r).symm j ∈ monotoneRowOnes c r then 1 else 0 := by
  simp [scrambledColSum, mem_scrambledRowOnes_iff]

/-- In one row, the inverse source contributes exactly one unit when occupied. -/
theorem preimage_indicator_eq_source_sum {m : Nat} (c : MonotoneColumnSums m 16)
    (σ : Scramble m 16) (r : Fin m) (j : Fin 16) :
    (if (σ r).symm j ∈ monotoneRowOnes c r then 1 else 0) =
      ∑ k : Fin 16,
        if k ∈ monotoneRowOnes c r ∧ σ r k = j then 1 else 0 := by
  classical
  simp [Equiv.apply_eq_iff_eq_symm_apply]
  let k0 := (σ r).symm j
  have hcard : (Finset.univ.filter (fun k : Fin 16 =>
      k ∈ monotoneRowOnes c r ∧ k = k0)).card =
      if k0 ∈ monotoneRowOnes c r then 1 else 0 := by
    have hfilter : Finset.univ.filter (fun k : Fin 16 =>
        k ∈ monotoneRowOnes c r ∧ k = k0) =
        if k0 ∈ monotoneRowOnes c r then {k0} else ∅ := by
      ext k
      by_cases h : k = k0
      · subst k
        by_cases hk : k0 ∈ monotoneRowOnes c r <;> simp [hk]
      · by_cases hk : k0 ∈ monotoneRowOnes c r <;> simp [h, hk]
    rw [hfilter]
    by_cases hk : k0 ∈ monotoneRowOnes c r <;> simp [hk]
  rw [hcard]

/-- The destination column total is the sum of its source-column row counts. -/
theorem scrambledColSum_eq_source_rows {m : Nat} (c : MonotoneColumnSums m 16)
    (σ : Scramble m 16) (j : Fin 16) :
    scrambledColSum c σ j =
      ∑ k : Fin 16, ∑ r : Fin m,
        if k ∈ monotoneRowOnes c r ∧ σ r k = j then 1 else 0 := by
  rw [scrambledColSum_eq_preimage_rows]
  simp_rw [preimage_indicator_eq_source_sum]
  rw [Finset.sum_comm]

/-- For one source column, the cyclic shift sends its active rows to at most
`ceil(height/16)` rows of any chosen destination column. -/
theorem cyclicSourceCount16_le (m h : Nat) (hh : h ≤ m)
    (k j : Fin 16) :
    (∑ r : Fin m, if m-r.val ≤ h ∧ cyclicShift16 (m := m) r k = j then 1 else 0) * 16
      ≤ h+15 := by
  classical
  let L := m-h
  have hsum :
      (∑ r : Fin m, if m-r.val ≤ h ∧ cyclicShift16 (m := m) r k = j then 1 else 0) =
        ((Finset.range m).filter (fun r =>
          m-r ≤ h ∧ (k.val+r)%16 = j.val)).card := by
    calc
      _ = ∑ r : Fin m, if m-r.val ≤ h ∧ (k.val+r.val)%16 = j.val then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro r hr
        have hj : cyclicShift16 r k = j ↔ (k.val+r.val)%16 = j.val := by
          simp [cyclicShift16, Fin.ext_iff]
        simp only [hj]
      _ = ∑ r ∈ Finset.range m,
          if m-r ≤ h ∧ (k.val+r)%16 = j.val then 1 else 0 :=
        Fin.sum_univ_eq_sum_range
          (fun r : Nat => if m-r ≤ h ∧ (k.val+r)%16 = j.val then 1 else 0) m
      _ = _ := by rw [← Finset.card_filter]
  have hset : (Finset.range m).filter (fun r => m-r ≤ h) = Finset.Ico L m := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [hsum, show ((Finset.range m).filter
      (fun r => m-r ≤ h ∧ (k.val+r)%16 = j.val)) =
      (Finset.Ico L m).filter (fun r => (k.val+r)%16 = j.val) by
        rw [← Finset.filter_filter, hset]
        ]
  have hlen : L+h = m := by dsimp [L]; omega
  rw [← hlen]
  exact card_residue_in_Ico_le L h k.val j.val

/-- Adding a fixed offset to every row shift preserves the same source-count
bound. -/
theorem cyclicSourceCount16_offset_le (m h offset : Nat) (hh : h ≤ m)
    (k j : Fin 16) :
    (∑ r : Fin m, if m-r.val ≤ h ∧ (k.val+r.val+offset)%16 = j.val then 1 else 0) * 16
      ≤ h+15 := by
  classical
  let L := m-h
  have hsum :
      (∑ r : Fin m, if m-r.val ≤ h ∧ (k.val+r.val+offset)%16 = j.val then 1 else 0) =
        ((Finset.range m).filter (fun r =>
          m-r ≤ h ∧ (k.val+offset+r)%16 = j.val)).card := by
    calc
      _ = ∑ r : Fin m, if m-r.val ≤ h ∧ (k.val+offset+r.val)%16 = j.val then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro r hr
        simp only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      _ = ∑ r ∈ Finset.range m,
          if m-r ≤ h ∧ (k.val+offset+r)%16 = j.val then 1 else 0 :=
        Fin.sum_univ_eq_sum_range
          (fun r : Nat => if m-r ≤ h ∧ (k.val+offset+r)%16 = j.val then 1 else 0) m
      _ = _ := by rw [← Finset.card_filter]
  have hset : (Finset.range m).filter (fun r => m-r ≤ h) = Finset.Ico L m := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [hsum, show ((Finset.range m).filter
      (fun r => m-r ≤ h ∧ (k.val+offset+r)%16 = j.val)) =
      (Finset.Ico L m).filter (fun r => (k.val+offset+r)%16 = j.val) by
        rw [← Finset.filter_filter, hset]]
  have hlen : L+h = m := by dsimp [L]; omega
  rw [← hlen]
  exact card_residue_in_Ico_le L h (k.val+offset) j.val

/-- Summing the sixteen source-column residue bounds gives an additive
15 discrepancy for every destination column. -/
theorem sum16_source_bounds (f h : Fin 16 → Nat)
    (hbound : ∀ k, f k * 16 ≤ h k + 15) :
    (∑ k : Fin 16, f k) * 16 ≤ (∑ k : Fin 16, h k) + 240 := by
  rw [Finset.sum_mul]
  calc
    _ ≤ ∑ k : Fin 16, (h k + 15) := Finset.sum_le_sum fun k _ => hbound k
    _ = (∑ k : Fin 16, h k) + 240 := by
      rw [Finset.sum_add_distrib]
      simp

theorem cyclicScramble16_col_bound {m : Nat} (c : MonotoneColumnSums m 16)
    (j : Fin 16) :
    scrambledColSum c cyclicScramble16 j * 16 ≤ totalColumnOnes c + 240 := by
  rw [scrambledColSum_eq_source_rows]
  apply le_trans (sum16_source_bounds
    (fun k => ∑ r : Fin m,
      if k ∈ monotoneRowOnes c r ∧ cyclicScramble16 r k = j then 1 else 0)
    (fun k => (c k).val) ?_)
  · simp [totalColumnOnes]
  · intro k
    have hocc : ∀ r : Fin m, k ∈ monotoneRowOnes c r ↔ m-r.val ≤ (c k).val := by
      intro r
      simp [monotoneRowOnes]
    simp only [hocc, cyclicScramble16]
    exact cyclicSourceCount16_le m (c k).val (Nat.le_of_lt_succ (c k).isLt) k j

/-- At exact mass `16*i`, the cyclic first-round scramble obeys the 15 cap. -/
theorem cyclicScramble16_firstRoundCap {m : Nat} (c : MonotoneColumnSums m 16)
    (i : Nat) (hmass : totalColumnOnes c = 16*i) (hi : i ≤ m) :
    ∀ j : Fin 16, scrambledColSum c cyclicScramble16 j ≤ i+15 := by
  intro j
  have h := cyclicScramble16_col_bound c j
  omega

/-- Any rowwise affine cyclic shift has the same additive column discrepancy. -/
theorem affineScramble16_col_bound {m : Nat} (σ : Scramble m 16) (offset : Nat)
    (haction : ∀ r k, (σ r k).val = (k.val+r.val+offset)%16)
    (c : MonotoneColumnSums m 16) (j : Fin 16) :
    scrambledColSum c σ j * 16 ≤ totalColumnOnes c + 240 := by
  rw [scrambledColSum_eq_source_rows]
  apply le_trans (sum16_source_bounds
    (fun k => ∑ r : Fin m,
      if k ∈ monotoneRowOnes c r ∧ σ r k = j then 1 else 0)
    (fun k => (c k).val) ?_)
  · simp [totalColumnOnes]
  · intro k
    have hocc : ∀ r : Fin m, k ∈ monotoneRowOnes c r ↔ m-r.val ≤ (c k).val := by
      intro r
      simp [monotoneRowOnes]
    have hmap : ∀ r : Fin m, σ r k = j ↔
        (k.val+r.val+offset)%16 = j.val := by
      intro r
      constructor
      · intro h
        have hv := congrArg Fin.val h
        simpa [haction] using hv
      · intro h
        apply Fin.ext
        simpa [haction] using h
    simp only [hocc, hmap]
    exact cyclicSourceCount16_offset_le m (c k).val offset
      (Nat.le_of_lt_succ (c k).isLt) k j

/-- Exact-mass first-round cap for every affine cyclic shift. -/
theorem affineScramble16_firstRoundCap {m : Nat} (σ : Scramble m 16) (offset : Nat)
    (haction : ∀ r k, (σ r k).val = (k.val+r.val+offset)%16)
    (c : MonotoneColumnSums m 16) (i : Nat)
    (hmass : totalColumnOnes c = 16*i) (hi : i ≤ m) :
    ∀ j : Fin 16, scrambledColSum c σ j ≤ i+15 := by
  intro j
  have h := affineScramble16_col_bound σ offset haction c j
  omega

end Tapered945
