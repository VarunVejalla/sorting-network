import AKS.Chvatal.Lemma61
import AKS.Chvatal.Bulk2Elem

/-! # Round 2 of the walk bound: the deterministic part (ROUND2.md §2), against the package's
definitions (`scrambledColSum`, `onesAboveBottom`, `excessAbove`, `totalColumnOnes`).

For output columns `S` and an input column `j`, `walkN σ S j h` counts the top `h` rows `r`
(those with `m - h ≤ r`) in which the scramble sends `j` into `S`; `walkW = walkN - p h` with
`p = #S / n`. -/

open Finset BigOperators

namespace Round2

open Chvatal

variable {m n : ℕ}

/-- Rows among the top `h` in which column `j` lands in `S`. -/
def walkN (σ : Scramble m n) (S : Finset (Fin n)) (j : Fin n) (h : ℕ) : ℕ :=
  (Finset.univ.filter fun r : Fin m => m - h ≤ r.val ∧ σ r j ∈ S).card

/-- The centred walk `W_j(h) = N_j(h) - p h`. -/
noncomputable def walkW (σ : Scramble m n) (S : Finset (Fin n)) (j : Fin n) (h : ℕ) : ℝ :=
  (walkN σ S j h : ℝ) - (S.card : ℝ) / n * h

/-- Ones that land in the columns `S`, counted per input column. -/
theorem sum_scrambledColSum_eq (c : MonotoneColumnSums m n) (σ : Scramble m n)
    (S : Finset (Fin n)) :
    ∑ T ∈ S, scrambledColSum c σ T = ∑ j : Fin n, walkN σ S j (c j).val := by
  classical
  simp only [scrambledColSum, walkN, scrambledRowOnes, monotoneRowOnes]
  -- both sides count pairs (r, j) with j a one of row r and σ r j ∈ S
  rw [Finset.sum_comm]
  have hrow : ∀ r : Fin m, ∑ T ∈ S, (if T ∈ (Finset.univ.filter fun j => m - r.val ≤ (c j).val).image
      (σ r) then 1 else 0) =
      ∑ j : Fin n, (if m - (c j).val ≤ r.val ∧ σ r j ∈ S then 1 else 0) := by
    intro r
    rw [Finset.sum_boole, Finset.sum_boole]
    simp only [Nat.cast_id]
    refine Finset.card_bij' (fun T _ => (σ r).symm T) (fun j _ => σ r j) ?_ ?_ ?_ ?_
    · intro T hT
      simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and] at hT ⊢
      obtain ⟨hTS, j, hj, rfl⟩ := hT
      simp only [Equiv.symm_apply_apply]
      have := (c j).isLt
      exact ⟨by omega, hTS⟩
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and] at hj ⊢
      refine ⟨hj.2, j, ?_, rfl⟩
      have := r.isLt
      omega
    · intro T _; exact (σ r).apply_symm_apply T
    · intro j _; exact (σ r).symm_apply_apply j
  trans ∑ r : Fin m, ∑ j : Fin n, (if m - (c j).val ≤ r.val ∧ σ r j ∈ S then 1 else 0)
  · exact Finset.sum_congr rfl (fun r _ => by convert hrow r)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_boole]
  rfl

/-- Every row sends exactly `#S` columns into `S`, so the walks sum to zero at every height. -/
theorem sum_walkN (σ : Scramble m n) (S : Finset (Fin n)) (h : ℕ) (hh : h ≤ m) :
    ∑ j : Fin n, walkN σ S j h = S.card * h := by
  classical
  simp only [walkN]
  have : ∀ j : Fin n, (Finset.univ.filter fun r : Fin m => m - h ≤ r.val ∧ σ r j ∈ S).card =
      ∑ r : Fin m, if m - h ≤ r.val ∧ σ r j ∈ S then 1 else 0 := fun j => by
    rw [Finset.sum_boole]; simp
  simp_rw [this]
  rw [Finset.sum_comm]
  have hrow : ∀ r : Fin m, ∑ j : Fin n, (if m - h ≤ r.val ∧ σ r j ∈ S then 1 else 0) =
      if m - h ≤ r.val then S.card else 0 := by
    intro r
    by_cases hr : m - h ≤ r.val
    · simp only [hr, true_and, if_true]
      rw [Finset.sum_boole]
      simp only [Nat.cast_id]
      exact Finset.card_bij (fun j _ => σ r j) (fun j hj => by simpa using hj)
        (fun a _ b _ hab => (σ r).injective hab)
        (fun T hT => ⟨(σ r).symm T, by simpa using hT, by simp⟩)
    · simp [hr]
  simp_rw [hrow]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul]
  have hc : (Finset.univ.filter fun r : Fin m => m - h ≤ r.val).card = h := by
    trans (Finset.Ico (m - h) m).card
    · refine Finset.card_bij (fun r _ => r.val) ?_ ?_ ?_
      · intro r hr
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
        exact Finset.mem_Ico.2 ⟨hr, r.isLt⟩
      · intro a _ b _ hab; exact Fin.ext hab
      · intro x hx
        rw [Finset.mem_Ico] at hx
        refine ⟨⟨x, hx.2⟩, ?_, rfl⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hx.1
    · rw [Nat.card_Ico]; omega
  rw [hc, mul_comm]

theorem sum_walkW (σ : Scramble m n) (S : Finset (Fin n)) (h : ℕ) (hh : h ≤ m) (hn : 0 < n) :
    ∑ j : Fin n, walkW σ S j h = 0 := by
  simp only [walkW, Finset.sum_sub_distrib]
  rw [← Nat.cast_sum, sum_walkN σ S h hh, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  push_cast
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [nsmul_eq_mul]
  field_simp
  ring

/-- Output columns at or above level `i`. -/
def Sstar (c : MonotoneColumnSums m n) (σ : Scramble m n) (i : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun T => i ≤ scrambledColSum c σ T

theorem onesAboveBottom_eq_sum (c : MonotoneColumnSums m n) (σ : Scramble m n) (i : ℕ) :
    (onesAboveBottom c σ i : ℝ) = ∑ T ∈ Sstar c σ i, ((scrambledColSum c σ T : ℝ) - i) := by
  classical
  simp only [onesAboveBottom, Sstar]
  rw [Finset.sum_filter]
  push_cast
  refine Finset.sum_congr rfl fun T _ => ?_
  by_cases h : i ≤ scrambledColSum c σ T
  · rw [if_pos h, Nat.cast_sub h]
  · rw [if_neg h]
    have : scrambledColSum c σ T - i = 0 := by omega
    rw [this]; simp

/-- **Reduction** (ROUND2 §2.1): at exact mass the excess is a sum of column walks. -/
theorem onesAboveBottom_eq_walks (c : MonotoneColumnSums m n) (σ : Scramble m n) (i : ℕ)
    (hn : 0 < n) (hmass : totalColumnOnes c = n * i) :
    (onesAboveBottom c σ i : ℝ) = ∑ j : Fin n, walkW σ (Sstar c σ i) j (c j).val := by
  rw [onesAboveBottom_eq_sum, Finset.sum_sub_distrib, ← Nat.cast_sum,
    sum_scrambledColSum_eq]
  simp only [walkW, Finset.sum_sub_distrib]
  rw [Nat.cast_sum]
  congr 1
  rw [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
  have hsum : (∑ j : Fin n, ((c j).val : ℝ)) = n * i := by
    have := congrArg (fun x : ℕ => (x : ℝ)) hmass
    simp only [totalColumnOnes] at this
    push_cast at this
    exact this
  rw [hsum]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

/-- The dual variable: the best excess of the walk over a `λ`-cone around the base row `b`. -/
noncomputable def Ydual (σ : Scramble m n) (S : Finset (Fin n)) (j : Fin n) (b : ℕ) (lam : ℝ) : ℝ :=
  (Finset.range (m + 1)).sup' ⟨0, by simp⟩ fun h =>
    walkW σ S j h - walkW σ S j b - lam * |(h : ℝ) - b|

theorem walk_le_dual (σ : Scramble m n) (S : Finset (Fin n)) (j : Fin n) (b lam : ℝ) (bN : ℕ)
    (hb : (bN : ℝ) = b) (h : ℕ) (hh : h ≤ m) :
    walkW σ S j h - walkW σ S j bN ≤ lam * |(h : ℝ) - b| + Ydual σ S j bN lam := by
  have : walkW σ S j h - walkW σ S j bN - lam * |(h : ℝ) - bN| ≤ Ydual σ S j bN lam :=
    Finset.le_sup' (f := fun h => walkW σ S j h - walkW σ S j bN - lam * |(h : ℝ) - bN|)
      (Finset.mem_range.2 (by omega))
  rw [hb] at this
  linarith

/-- **Weak duality** (ROUND2 §2.2–2.3): for any base row `b ≤ m`. -/
theorem onesAboveBottom_le_dual (c : MonotoneColumnSums m n) (σ : Scramble m n) (i : ℕ)
    (hn : 0 < n) (hmass : totalColumnOnes c = n * i) (b : ℕ) (hb : b ≤ m) (lam : ℝ) :
    (onesAboveBottom c σ i : ℝ) ≤
      lam * ∑ j : Fin n, |((c j).val : ℝ) - b| + ∑ j : Fin n, Ydual σ (Sstar c σ i) j b lam := by
  rw [onesAboveBottom_eq_walks c σ i hn hmass]
  have h0 := sum_walkW σ (Sstar c σ i) b hb hn
  calc ∑ j : Fin n, walkW σ (Sstar c σ i) j (c j).val
      = ∑ j : Fin n, (walkW σ (Sstar c σ i) j (c j).val - walkW σ (Sstar c σ i) j b) := by
        rw [Finset.sum_sub_distrib, h0, sub_zero]
    _ ≤ ∑ j : Fin n, (lam * |((c j).val : ℝ) - b| + Ydual σ (Sstar c σ i) j b lam) :=
        Finset.sum_le_sum fun j _ =>
          walk_le_dual σ _ j b lam b rfl (c j).val (Nat.lt_succ_iff.1 (c j).isLt)
    _ = _ := by rw [Finset.sum_add_distrib, Finset.mul_sum]

/-- At exact mass the total displacement from `i` is twice the excess. -/
theorem sum_abs_eq_two_excess (c : MonotoneColumnSums m n) (i : ℕ)
    (hmass : totalColumnOnes c = n * i) :
    ∑ j : Fin n, |((c j).val : ℝ) - i| = 2 * (excessAbove c i : ℝ) := by
  have hpos : ∀ x : ℝ, |x| = 2 * max x 0 - x := fun x => by
    rcases le_total 0 x with h | h
    · rw [abs_of_nonneg h, max_eq_left h]; ring
    · rw [abs_of_nonpos h, max_eq_right h]; ring
  simp_rw [hpos]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hz : ∑ j : Fin n, (((c j).val : ℝ) - i) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have := congrArg (fun x : ℕ => (x : ℝ)) hmass
    simp only [totalColumnOnes] at this
    push_cast at this
    rw [this]; ring
  rw [hz, sub_zero]
  congr 1
  simp only [excessAbove]
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  rcases le_total i (c j).val with h | h
  · rw [Nat.cast_sub h, max_eq_left (by linarith [show (i : ℝ) ≤ (c j).val by exact_mod_cast h])]
  · have : (c j).val - i = 0 := by omega
    rw [this, max_eq_right (by linarith [show ((c j).val : ℝ) ≤ i by exact_mod_cast h])]
    simp

theorem sum_abs_base_le (c : MonotoneColumnSums m n) (i b : ℕ)
    (hmass : totalColumnOnes c = n * i) :
    ∑ j : Fin n, |((c j).val : ℝ) - b| ≤ 2 * (excessAbove c i : ℝ) + n * |(i : ℝ) - b| := by
  rw [← sum_abs_eq_two_excess c i hmass]
  calc ∑ j : Fin n, |((c j).val : ℝ) - b|
      ≤ ∑ j : Fin n, (|((c j).val : ℝ) - i| + |(i : ℝ) - b|) :=
        Finset.sum_le_sum fun j _ => by
          have := abs_sub_le ((c j).val : ℝ) i b
          linarith
    _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]

end Round2
