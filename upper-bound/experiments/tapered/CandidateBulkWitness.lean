import AKS.Chvatal.Bulk2Count
import Mathlib.Tactic

namespace Tapered945
open Chvatal

def complementColumns {m n : Nat} (c : MonotoneColumnSums m n) : MonotoneColumnSums m n :=
  fun j => ⟨m-(c j).val, by have h := (c j).isLt; omega⟩

def reverseRows {m n : Nat} (σ : Scramble m n) : Scramble m n := fun r => σ (Fin.rev r)

theorem reverseRows_involutive {m n : Nat} : Function.Involutive (@reverseRows m n) := by
  intro σ
  funext r
  simp [reverseRows]

theorem card_filter_reverseRows {m n : Nat} (P : Scramble m n → Prop) [DecidablePred P] :
    (Finset.univ.filter (fun σ => P (reverseRows σ))).card = (Finset.univ.filter P).card :=
  Finset.card_equiv (Function.Involutive.toPerm reverseRows reverseRows_involutive) (by simp)

theorem complement_row_ones {m n : Nat} (c : MonotoneColumnSums m n) (r : Fin m) :
    monotoneRowOnes (complementColumns c) r = (monotoneRowOnes c (Fin.rev r))ᶜ := by
  ext j
  simp only [monotoneRowOnes, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_compl, complementColumns, Fin.rev]
  have hr := r.isLt
  have hj := (c j).isLt
  omega

/-- At exact mass an upper-deviation witness always has a half-sized signed
witness. The negative branch is subsequently interpreted as a zero tail. -/
theorem small_signed_witness (n : Nat) (y : Fin n → Real) (i T : Real)
    (hmass : ∑ j, y j = n*i) (S : Finset (Fin n))
    (hS : i*S.card + T ≤ ∑ j ∈ S, y j) :
    ∃ R : Finset (Fin n), (R.card : Real) ≤ (n : Real)/2 ∧
      (i*R.card + T ≤ ∑ j ∈ R, y j ∨ (∑ j ∈ R, y j) + T ≤ i*R.card) := by
  classical
  by_cases hsmall : (S.card : Real) ≤ (n : Real)/2
  · exact ⟨S, hsmall, Or.inl hS⟩
  · refine ⟨Sᶜ, ?_, Or.inr ?_⟩
    · have hc := Finset.card_add_card_compl S
      simp only [Finset.card_univ, Fintype.card_fin] at hc
      have hcr : (S.card : Real)+(Sᶜ.card : Real) = n := by exact_mod_cast hc
      linarith
    · have hs := Finset.sum_add_sum_compl S y
      rw [hmass] at hs
      have hc := Finset.card_add_card_compl S
      simp only [Finset.card_univ, Fintype.card_fin] at hc
      have hcr : (S.card : Real)+(Sᶜ.card : Real) = n := by exact_mod_cast hc
      have hp := congrArg (fun z : Real => i*z) hcr
      nlinarith [hp]

private theorem mem_image_perm_iff {n : Nat} (s : Finset (Fin n))
    (e : Equiv.Perm (Fin n)) (j : Fin n) : j ∈ s.image e ↔ e.symm j ∈ s := by
  constructor
  · rintro h
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp h
    simpa using hk
  · intro h
    exact Finset.mem_image.mpr ⟨e.symm j, h, e.apply_symm_apply j⟩

theorem complement_scrambled_row {m n : Nat} (c : MonotoneColumnSums m n)
    (σ : Scramble m n) (r : Fin m) :
    scrambledRowOnes (complementColumns c) (reverseRows σ) r =
      (scrambledRowOnes c σ (Fin.rev r))ᶜ := by
  ext j
  simp only [scrambledRowOnes, reverseRows, mem_image_perm_iff, Finset.mem_compl,
    complement_row_ones]

theorem complement_scrambled_column {m n : Nat} (c : MonotoneColumnSums m n)
    (σ : Scramble m n) (j : Fin n) :
    scrambledColSum (complementColumns c) (reverseRows σ) j + scrambledColSum c σ j = m := by
  unfold scrambledColSum
  simp only [complement_scrambled_row, Finset.mem_compl]
  rw [← Equiv.sum_comp Fin.revPerm (fun r : Fin m => if j ∈ scrambledRowOnes c σ r then 1 else 0)]
  rw [← Finset.sum_add_distrib]
  have he : ∀ r : Fin m,
      (if ¬ j ∈ scrambledRowOnes c σ r.rev then 1 else 0) +
        (if j ∈ scrambledRowOnes c σ r.rev then 1 else 0) = (1 : Nat) := by
    intro r
    split_ifs <;> simp_all
  simp only [Fin.revPerm_apply]
  calc
    _ = ∑ _ : Fin m, (1 : Nat) := by
      apply Finset.sum_congr rfl
      intro r _
      split_ifs <;> simp_all
    _ = m := by simp

theorem column_sum_mass {m n : Nat} (c : MonotoneColumnSums m n) (σ : Scramble m n) :
    (∑ j : Fin n, scrambledColSum c σ j) = totalColumnOnes c := by
  unfold scrambledColSum
  rw [Finset.sum_comm, totalColumnOnes_eq_sum_rowOnes]
  apply Finset.sum_congr rfl
  intro r _
  rw [← Finset.card_filter]
  have he : (Finset.univ.filter (fun j => j ∈ scrambledRowOnes c σ r)) =
      scrambledRowOnes c σ r := by ext j; simp
  rw [he]
  exact Finset.card_image_of_injective _ (σ r).injective

theorem onesInColumns_eq_sum {m n : Nat} (c : MonotoneColumnSums m n)
    (σ : Scramble m n) (S : Finset (Fin n)) :
    onesInColumns c σ S = ∑ j ∈ S, scrambledColSum c σ j := by
  unfold onesInColumns onesInRows scrambledColSum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter, Finset.card_filter]

/-- A genuine exact-mass matrix witness reduces to an upper tail on at most
half the columns, in either the original or complemented/reversed model. -/
theorem small_column_tail_witness {m n : Nat} (c : MonotoneColumnSums m n)
    (σ : Scramble m n) (i : Nat) (hi : i ≤ m)
    (hmass : totalColumnOnes c = n*i) (S : Finset (Fin n)) (T : Real)
    (hS : (i : Real)*S.card + T ≤ (onesInColumns c σ S : Real)) :
    ∃ R : Finset (Fin n), (R.card : Real) ≤ (n : Real)/2 ∧
      ((i : Real)*R.card + T ≤ (onesInColumns c σ R : Real) ∨
       ((m-i : Nat) : Real)*R.card + T ≤
         (onesInColumns (complementColumns c) (reverseRows σ) R : Real)) := by
  have hmR : (∑ j : Fin n, (scrambledColSum c σ j : Real)) = (n : Real)*i := by
    exact_mod_cast (column_sum_mass c σ).trans hmass
  have hSR : (i : Real)*S.card + T ≤ ∑ j ∈ S, (scrambledColSum c σ j : Real) := by
    simpa only [onesInColumns_eq_sum, Nat.cast_sum] using hS
  obtain ⟨R, hR, htail⟩ := small_signed_witness n (fun j => (scrambledColSum c σ j : Real)) i T hmR S hSR
  refine ⟨R, hR, ?_⟩
  rcases htail with hp | hn
  · left
    simpa only [onesInColumns_eq_sum, Nat.cast_sum] using hp
  · right
    have he : onesInColumns (complementColumns c) (reverseRows σ) R + onesInColumns c σ R = m*R.card := by
      rw [onesInColumns_eq_sum, onesInColumns_eq_sum, ← Finset.sum_add_distrib]
      rw [Finset.sum_congr rfl (fun j _ => complement_scrambled_column c σ j)]
      simp [mul_comm]
    have heR : (onesInColumns (complementColumns c) (reverseRows σ) R : Real) +
        (onesInColumns c σ R : Real) = (m : Real)*R.card := by exact_mod_cast he
    have hnR : (onesInColumns c σ R : Real) + T ≤ (i : Real)*R.card := by
      simpa only [onesInColumns_eq_sum, Nat.cast_sum] using hn
    rw [Nat.cast_sub hi]
    nlinarith

theorem complement_exact_mass {m n : Nat} (c : MonotoneColumnSums m n)
    (i : Nat) (hi : i ≤ m) (hmass : totalColumnOnes c = n*i) :
    totalColumnOnes (complementColumns c) = n*(m-i) := by
  have he : totalColumnOnes (complementColumns c) + totalColumnOnes c = n*m := by
    unfold totalColumnOnes
    rw [← Finset.sum_add_distrib]
    have hp : ∀ j : Fin n, (complementColumns c j).val + (c j).val = m := by
      intro j
      dsimp [complementColumns]
      have hj := (c j).isLt
      omega
    rw [Finset.sum_congr rfl (fun j _ => hp j)]
    simp
  rw [hmass] at he
  rw [Nat.mul_sub_left_distrib]
  omega

theorem complement_excess_exact {m n : Nat} (c : MonotoneColumnSums m n)
    (i : Nat) (hi : i ≤ m) (hmass : totalColumnOnes c = n*i) :
    excessAbove (complementColumns c) (m-i) = excessAbove c i := by
  have he : ∀ j : Fin n, (c j).val-i+i = (c j).val+(i-(c j).val) := by
    intro j
    omega
  have hs := Finset.sum_congr (rfl : (Finset.univ : Finset (Fin n)) = Finset.univ)
    (fun j _ => he j)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hs
  have hm : (∑ j : Fin n, (c j).val) = n*i := hmass
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, hm] at hs
  have hec : ∀ j : Fin n, (complementColumns c j).val-(m-i) = i-(c j).val := by
    intro j
    dsimp [complementColumns]
    have hj := (c j).isLt
    omega
  unfold excessAbove
  rw [Finset.sum_congr rfl (fun j _ => hec j)]
  omega

/-- Failure of a bulk excess bound supplies the genuinely small two-tailed
witness needed by the probability union, with unchanged deviation size. -/
theorem excess_small_column_witness {m n : Nat} (c : MonotoneColumnSums m n)
    (σ : Scramble m n) (i : Nat) (hi : i ≤ m)
    (hmass : totalColumnOnes c = n*i) (epsB : Real)
    (hge : (epsB/2)*(m*n) ≤ (onesAboveBottom c σ i : Real)) :
    ∃ R : Finset (Fin n), (R.card : Real) ≤ (n : Real)/2 ∧
      ((i : Real)*R.card + (epsB/2)*(m*n) ≤ (onesInColumns c σ R : Real) ∨
       ((m-i : Nat) : Real)*R.card + (epsB/2)*(m*n) ≤
         (onesInColumns (complementColumns c) (reverseRows σ) R : Real)) := by
  have h := lemma61_excess_columns epsB c σ i hge
  simp only [Nat.cast_mul] at h
  exact small_column_tail_witness c σ i hi hmass (excessColumnSet c σ i) ((epsB/2)*(m*n)) h

end Tapered945
