import AKS.Sub800.Round2Det

/-! # Fringe by double weak duality: the deterministic part (UB-34, `experiments/fringe-duality`)

One round of the separator on a column-sorted Boolean matrix (`MonotoneColumnSums`: column `j` holds
its `c j` ones in the bottom rows) followed by a row scramble `σ`. For weights `a` on the output
columns:

* `sum_weighted_scrambledColSum_eq`: `Σ_T a T · scrambledColSum c σ T = Σ_j A_j(c j)`, where
  `A_j(h) = Σ_{r in the bottom h rows} a (σ r j)` is the weighted walk of input column `j`;
* `weighted_duality`: for every `λ`, `Σ_T a T · scrambledColSum c σ T ≤ λ · Σ_j c j + Σ_j Y_j(λ)`,
  `Y_j(λ) = max_{h ≤ m} (A_j(h) − λ h)`.

With `a` the indicator of a set this is `Round2.sum_scrambledColSum_eq`; with `a = z` (the output
heights of round 1) it bounds `Σ_T z_T²`, and with a convex cost it is the round-2 step. -/

open Finset BigOperators

namespace FringeDuality

open Chvatal

variable {m n : ℕ}

/-- The weighted walk of input column `j`: total weight of the outputs it reaches in the bottom `h`
rows. -/
noncomputable def walkA (σ : Scramble m n) (a : Fin n → ℝ) (j : Fin n) (h : ℕ) : ℝ :=
  ∑ r ∈ Finset.univ.filter (fun r : Fin m => m - h ≤ r.val), a (σ r j)

/-- Its drift-corrected maximum `Y_j(λ) = max_{h ≤ m} (A_j(h) − λ h)`. -/
noncomputable def walkY (σ : Scramble m n) (a : Fin n → ℝ) (lam : ℝ) (j : Fin n) : ℝ :=
  (Finset.range (m + 1)).sup' ⟨0, by simp⟩ fun h => walkA σ a j h - lam * h

/-- **Weighted round identity.** -/
theorem sum_weighted_scrambledColSum_eq (c : MonotoneColumnSums m n) (σ : Scramble m n)
    (a : Fin n → ℝ) :
    ∑ T : Fin n, a T * (scrambledColSum c σ T : ℝ) = ∑ j : Fin n, walkA σ a j (c j).val := by
  classical
  simp only [scrambledColSum, walkA, scrambledRowOnes, monotoneRowOnes]
  -- both sides sum `a (σ r j)` over pairs (r, j) with j a one of row r
  have hrow : ∀ r : Fin m, ∑ T : Fin n, a T * (if T ∈ (Finset.univ.filter fun j =>
      m - r.val ≤ (c j).val).image (σ r) then 1 else 0) =
      ∑ j : Fin n, if m - (c j).val ≤ r.val then a (σ r j) else 0 := by
    intro r
    have himg : ∀ T : Fin n, T ∈ (Finset.univ.filter fun j => m - r.val ≤ (c j).val).image (σ r) ↔
        m - r.val ≤ (c ((σ r).symm T)).val := by
      intro T
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨j, hj, rfl⟩; simpa using hj
      · intro h; exact ⟨(σ r).symm T, h, (σ r).apply_symm_apply T⟩
    have hle : ∀ j : Fin n, (m - r.val ≤ (c j).val ↔ m - (c j).val ≤ r.val) := by
      intro j; have := (c j).isLt; have := r.isLt; omega
    calc ∑ T : Fin n, a T * (if T ∈ (Finset.univ.filter fun j =>
          m - r.val ≤ (c j).val).image (σ r) then 1 else 0)
        = ∑ T : Fin n, if m - (c ((σ r).symm T)).val ≤ r.val then a T else 0 := by
          refine Finset.sum_congr rfl fun T _ => ?_
          have hiff := (himg T).trans (hle ((σ r).symm T))
          by_cases hT : m - (c ((σ r).symm T)).val ≤ r.val
          · rw [if_pos (hiff.2 hT), if_pos hT, mul_one]
          · rw [if_neg (fun h => hT (hiff.1 h)), if_neg hT, mul_zero]
      _ = ∑ j : Fin n, if m - (c j).val ≤ r.val then a (σ r j) else 0 := by
          refine Fintype.sum_equiv (σ r).symm _ _ fun T => ?_
          simp
  push_cast
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  trans ∑ r : Fin m, ∑ j : Fin n, if m - (c j).val ≤ r.val then a (σ r j) else 0
  · exact Finset.sum_congr rfl fun r _ => hrow r
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_filter]

theorem walkA_sub_le_walkY (σ : Scramble m n) (a : Fin n → ℝ) (lam : ℝ) (j : Fin n) {h : ℕ}
    (hh : h ≤ m) : walkA σ a j h - lam * h ≤ walkY σ a lam j :=
  Finset.le_sup' (fun h => walkA σ a j h - lam * h) (Finset.mem_range.2 (Nat.lt_succ_of_le hh))

/-- **Weighted duality** (one round): any drift `λ` charges the input mass `Σ_j c j`. -/
theorem weighted_duality (c : MonotoneColumnSums m n) (σ : Scramble m n) (a : Fin n → ℝ)
    (lam : ℝ) :
    ∑ T : Fin n, a T * (scrambledColSum c σ T : ℝ) ≤
      lam * ∑ j : Fin n, ((c j).val : ℝ) + ∑ j : Fin n, walkY σ a lam j := by
  rw [sum_weighted_scrambledColSum_eq, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  have := walkA_sub_le_walkY σ a lam j (h := (c j).val) (Nat.le_of_lt_succ (c j).isLt)
  linarith

end FringeDuality
