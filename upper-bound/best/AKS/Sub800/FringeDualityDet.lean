import AKS.Sub800.Round2Det
import AKS.Sub800.Round2Union

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

/-- The maximum of the walk against an arbitrary cost `φ` (round 2 uses a convex `φ`). -/
noncomputable def walkYφ (σ : Scramble m n) (a : Fin n → ℝ) (φ : ℕ → ℝ) (j : Fin n) : ℝ :=
  (Finset.range (m + 1)).sup' ⟨0, by simp⟩ fun h => walkA σ a j h - φ h

/-- **Duality with an arbitrary cost**: `Σ_T a T · count(T) ≤ Σ_j φ(c j) + Σ_j max_h (A_j(h) − φ(h))`. -/
theorem cost_duality (c : MonotoneColumnSums m n) (σ : Scramble m n) (a : Fin n → ℝ) (φ : ℕ → ℝ) :
    ∑ T : Fin n, a T * (scrambledColSum c σ T : ℝ) ≤
      ∑ j : Fin n, φ (c j).val + ∑ j : Fin n, walkYφ σ a φ j := by
  rw [sum_weighted_scrambledColSum_eq, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  have : walkA σ a j (c j).val - φ (c j).val ≤ walkYφ σ a φ j :=
    Finset.le_sup' (fun h => walkA σ a j h - φ h)
      (Finset.mem_range.2 (Nat.lt_succ_of_le (Nat.le_of_lt_succ (c j).isLt)))
  linarith

/-- **Escapes as a maximum over output sets**: `Σ_v (w v − f)₊ = max_S Σ_{v ∈ S} (w v − f)`; the
inequality used is that the positive part is attained by `S = {v : w v > f}`. -/
theorem sum_posPart_le_of_sets (w : Fin n → ℝ) (f : ℝ) (B : ℝ)
    (hB : ∀ S : Finset (Fin n), ∑ v ∈ S, (w v - f) ≤ B) :
    ∑ v : Fin n, max (w v - f) 0 ≤ B := by
  classical
  have h := hB (Finset.univ.filter fun v => f < w v)
  calc ∑ v : Fin n, max (w v - f) 0 = ∑ v ∈ Finset.univ.filter (fun v => f < w v), (w v - f) := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun v _ => ?_
        split_ifs with hv
        · exact max_eq_left (by linarith)
        · exact max_eq_right (by linarith)
    _ ≤ B := h

/-- Indicator weights of a set of output columns. -/
noncomputable def ind (S : Finset (Fin n)) : Fin n → ℝ := fun T => if T ∈ S then 1 else 0

/-- **Tall-column count.** If every column of `S` reaches height `≥ k` after the round, then
`k · |S| ≤ λ · (input mass) + Σ_j Y_j(1_S, λ)`. -/
theorem tall_count_le (c : MonotoneColumnSums m n) (σ : Scramble m n) (S : Finset (Fin n))
    (k : ℕ) (hk : ∀ T ∈ S, k ≤ scrambledColSum c σ T) (lam : ℝ) :
    (k : ℝ) * S.card ≤
      lam * ∑ j : Fin n, ((c j).val : ℝ) + ∑ j : Fin n, walkY σ (ind S) lam j := by
  classical
  have hdual := weighted_duality c σ (ind S) lam
  have hsum : ∑ T : Fin n, ind S T * (scrambledColSum c σ T : ℝ) =
      ∑ T ∈ S, (scrambledColSum c σ T : ℝ) := by
    simp only [ind, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  have hk' : (k : ℝ) * S.card ≤ ∑ T ∈ S, (scrambledColSum c σ T : ℝ) := by
    rw [mul_comm, ← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun T hT => by exact_mod_cast hk T hT
  linarith [hsum ▸ hdual]

theorem sq_eq_sum_odd (z : ℕ) : z ^ 2 = ∑ k ∈ Finset.range z, (2 * k + 1) := by
  induction z with
  | zero => simp
  | succ z ih => rw [Finset.sum_range_succ, ← ih]; ring

/-- **Energy from the tall-column counts**: `Σ_T z_T² = Σ_{k < M} (2k+1) · #{T : k < z_T}` for
heights `z ≤ M`. -/
theorem sum_sq_eq_sum_counts (z : Fin n → ℕ) (M : ℕ) (hz : ∀ T, z T ≤ M) :
    ∑ T : Fin n, z T ^ 2 =
      ∑ k ∈ Finset.range M, (2 * k + 1) * (Finset.univ.filter fun T => k < z T).card := by
  classical
  have h1 : ∀ T, z T ^ 2 = ∑ k ∈ Finset.range M, if k < z T then 2 * k + 1 else 0 := by
    intro T
    rw [sq_eq_sum_odd, ← Finset.sum_filter]
    congr 1
    ext k
    simp only [Finset.mem_range, Finset.mem_filter]
    constructor
    · intro hk; exact ⟨lt_of_lt_of_le hk (hz T), hk⟩
    · intro hk; exact hk.2
  simp_rw [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.card_eq_sum_ones, Finset.mul_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun T _ => ?_
  split_ifs <;> simp

/-- **Round-2 escapes from per-set walk bounds.** With `w = scrambledColSum c₁ σ₂`, if every set `S`
has `Σ_u Y_u(1_S, φ) ≤ X |S|` and `X s − f s ≤ B` for all `s`, then
`Σ_v (w_v − f)₊ ≤ Σ_u φ(c₁ u) + B`. -/
theorem escapes_le (c₁ : MonotoneColumnSums m n) (σ₂ : Scramble m n) (φ : ℕ → ℝ) (f B : ℝ)
    (X : ℕ → ℝ) (hX : ∀ S : Finset (Fin n), ∑ u : Fin n, walkYφ σ₂ (ind S) φ u ≤ X S.card)
    (hB : ∀ s : ℕ, X s - f * s ≤ B) :
    ∑ v : Fin n, max ((scrambledColSum c₁ σ₂ v : ℝ) - f) 0 ≤
      ∑ u : Fin n, φ (c₁ u).val + B := by
  classical
  refine sum_posPart_le_of_sets _ f _ fun S => ?_
  have hdual := cost_duality c₁ σ₂ (ind S) φ
  have hsum : ∑ T : Fin n, ind S T * (scrambledColSum c₁ σ₂ T : ℝ) =
      ∑ T ∈ S, (scrambledColSum c₁ σ₂ T : ℝ) := by
    simp only [ind, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  have hsub : ∑ v ∈ S, ((scrambledColSum c₁ σ₂ v : ℝ) - f) =
      ∑ v ∈ S, (scrambledColSum c₁ σ₂ v : ℝ) - f * S.card := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_comm]
  have := hX S
  have := hB S.card
  linarith [hsum ▸ hdual]

/-- **Mass conservation**: the round preserves the number of ones. -/
theorem sum_scrambledColSum (c : MonotoneColumnSums m n) (σ : Scramble m n) :
    ∑ T : Fin n, (scrambledColSum c σ T : ℝ) = ∑ j : Fin n, ((c j).val : ℝ) := by
  classical
  have h := sum_weighted_scrambledColSum_eq c σ (fun _ => 1)
  simp only [one_mul] at h
  rw [h]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold walkA
  rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  have hc := Nat.le_of_lt_succ (c j).isLt
  have : (Finset.univ.filter fun r : Fin m => m - (c j).val ≤ r.val).card = (c j).val :=
    Round2Union.card_rows_top (c j).val hc
  rw [this]

/-- **Shifted energy from the counts**: `Σ_T ((z_T − b)₊)² = Σ_{b ≤ k < M} (2(k−b)+1) · #{T : k < z_T}`
for heights `z ≤ M` (as naturals, `z − b` truncated). -/
theorem sum_sq_sub_eq_sum_counts (z : Fin n → ℕ) (b M : ℕ) (hz : ∀ T, z T ≤ M) :
    ∑ T : Fin n, (z T - b) ^ 2 =
      ∑ k ∈ Finset.Ico b M, (2 * (k - b) + 1) * (Finset.univ.filter fun T => k < z T).card := by
  classical
  have h1 : ∀ T, (z T - b) ^ 2 = ∑ k ∈ Finset.Ico b M, if k < z T then 2 * (k - b) + 1 else 0 := by
    intro T
    rw [sq_eq_sum_odd, ← Finset.sum_filter]
    -- range (z − b) ≃ {k ∈ [b, M) : k < z} via k ↦ k + b
    refine Finset.sum_bij (fun i _ => i + b) ?_ ?_ ?_ ?_
    · intro i hi
      simp only [Finset.mem_range] at hi
      simp only [Finset.mem_filter, Finset.mem_Ico]
      have := hz T; omega
    · intro i _ i' _ h
      dsimp only at h; omega
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_Ico] at hk
      exact ⟨k - b, by simp only [Finset.mem_range]; omega, by dsimp only; omega⟩
    · intro i _
      dsimp only
      congr 1; omega
  simp_rw [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.card_eq_sum_ones, Finset.mul_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun T _ => ?_
  split_ifs <;> simp

end FringeDuality
