import Ville
import Mathlib.Tactic

/-! # Round 2, one column: the dual variable as two Ville walks (ROUND2.md §3)

On row subsets `ω : Fin m → Finset (Fin n)` (row `r` = the input columns that the scramble
sends into `S`), the column walk is `W(h) = #{r ≥ m-h : j ∈ ω r} - p h`. Fix a base row `b ≤ m`.
Complementing the rows `r ≥ m - b` (`unflip`), the excess over the cone around `b` splits into
* a forward walk over the rows `m-b-1, …, 0` (increments `[j ∈ ζ] - p - λ`), which becomes an
  increasing walk after `Fin.rev`, and
* a backward walk over the rows `m-b, …, m-1` (increments `[j ∈ ζ] - (1-p) - λ`). -/

open Finset BigOperators

namespace Round2Col

variable {m n : ℕ}

def Nω (ω : Fin m → Finset (Fin n)) (j : Fin n) (h : ℕ) : ℕ :=
  (Finset.univ.filter fun r : Fin m => m - h ≤ r.val ∧ j ∈ ω r).card

noncomputable def Wω (p : ℝ) (ω : Fin m → Finset (Fin n)) (j : Fin n) (h : ℕ) : ℝ :=
  (Nω ω j h : ℝ) - p * h

noncomputable def Yω (p lam : ℝ) (ω : Fin m → Finset (Fin n)) (j : Fin n) (b : ℕ) : ℝ :=
  (Finset.range (m + 1)).sup' ⟨0, by simp⟩ fun h =>
    Wω p ω j h - Wω p ω j b - lam * |(h : ℝ) - b|

/-- The column's bit in a row subset. -/
def bit (j : Fin n) (T : Finset (Fin n)) : ℝ := if j ∈ T then 1 else 0

/-- Complement the rows `r ≥ m - b`. -/
def unflip (b : ℕ) (ζ : Fin m → Finset (Fin n)) : Fin m → Finset (Fin n) :=
  fun r => if r.val < m - b then ζ r else Finset.univ \ ζ r

noncomputable def Dfwd (p lam : ℝ) (j : Fin n) (b : ℕ) : Fin m → Finset (Fin n) → ℝ :=
  fun r' T => if b ≤ r'.val then bit j T - p - lam else 0

noncomputable def Dbwd (p lam : ℝ) (j : Fin n) (b : ℕ) : Fin m → Finset (Fin n) → ℝ :=
  fun r T => if m - b ≤ r.val then bit j T - (1 - p) - lam else 0

noncomputable def Yplus (p lam : ℝ) (j : Fin n) (b : ℕ) (ζ : Fin m → Finset (Fin n)) : ℝ :=
  (Finset.range (m + 1)).sup' ⟨0, by simp⟩ fun h =>
    Ville.prefixSum (Dfwd p lam j b) (fun r => ζ (Fin.rev r)) h

noncomputable def Yminus (p lam : ℝ) (j : Fin n) (b : ℕ) (ζ : Fin m → Finset (Fin n)) : ℝ :=
  (Finset.range (m + 1)).sup' ⟨0, by simp⟩ fun h => Ville.prefixSum (Dbwd p lam j b) ζ h

theorem Nω_eq_sum (ω : Fin m → Finset (Fin n)) (j : Fin n) (h : ℕ) :
    (Nω ω j h : ℝ) = ∑ r : Fin m, if m - h ≤ r.val then bit j (ω r) else 0 := by
  classical
  simp only [Nω, bit]
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun r _ => ?_
  by_cases h1 : m - h ≤ r.val <;> by_cases h2 : j ∈ ω r <;> simp [h1, h2]

theorem card_rows_between (a c : ℕ) (hc : c ≤ m) :
    ((c - a : ℕ) : ℝ) = ∑ r : Fin m, if a ≤ r.val ∧ r.val < c then (1 : ℝ) else 0 := by
  classical
  rw [Finset.sum_boole]
  congr 1
  rw [show c - a = (Finset.Ico a c).card by rw [Nat.card_Ico]]
  symm
  refine Finset.card_bij (fun r _ => r.val) ?_ ?_ ?_
  · intro r hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
    exact Finset.mem_Ico.2 hr
  · intro a _ b _ hab; exact Fin.ext hab
  · intro x hx
    rw [Finset.mem_Ico] at hx
    exact ⟨⟨x, by omega⟩, by simp [hx.1, hx.2], rfl⟩

/-- Forward identity, `b ≤ h ≤ m`. -/
theorem fwd_identity (p lam : ℝ) (j : Fin n) (b h : ℕ) (hbh : b ≤ h) (hh : h ≤ m)
    (ζ : Fin m → Finset (Fin n)) :
    Wω p (unflip b ζ) j h - Wω p (unflip b ζ) j b - lam * |(h : ℝ) - b| =
      Ville.prefixSum (Dfwd p lam j b) (fun r => ζ (Fin.rev r)) h := by
  classical
  have hcnt := card_rows_between (m := m) (m - h) (m - b) (by omega)
  have hhb : ((m - b - (m - h) : ℕ) : ℝ) = (h : ℝ) - b := by
    rw [show m - b - (m - h) = h - b by omega]; push_cast [Nat.cast_sub hbh]; ring
  rw [hhb] at hcnt
  have habs : |(h : ℝ) - b| = (h : ℝ) - b := abs_of_nonneg (by
    have : (b : ℝ) ≤ h := by exact_mod_cast hbh
    linarith)
  simp only [Wω, Nω_eq_sum, habs]
  -- left side as one sum over rows in [m-h, m-b)
  have hL : (∑ r : Fin m, if m - h ≤ r.val then bit j (unflip b ζ r) else 0) -
      p * h - ((∑ r : Fin m, if m - b ≤ r.val then bit j (unflip b ζ r) else 0) - p * b) -
      lam * ((h : ℝ) - b) =
      ∑ r : Fin m, if m - h ≤ r.val ∧ r.val < m - b then bit j (ζ r) - p - lam else 0 := by
    have e1 : (∑ r : Fin m, if m - h ≤ r.val then bit j (unflip b ζ r) else 0) -
        (∑ r : Fin m, if m - b ≤ r.val then bit j (unflip b ζ r) else 0) =
        ∑ r : Fin m, if m - h ≤ r.val ∧ r.val < m - b then bit j (ζ r) else 0 := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun r _ => ?_
      by_cases h1 : m - h ≤ r.val <;> by_cases h2 : m - b ≤ r.val
      · have : ¬ r.val < m - b := by omega
        simp [h1, h2, this]
      · have h3 : r.val < m - b := by omega
        simp [h1, h2, h3, unflip]
      · omega
      · simp [h1, h2]
    have e2 : p * h - p * b + lam * ((h : ℝ) - b) =
        ∑ r : Fin m, if m - h ≤ r.val ∧ r.val < m - b then p + lam else 0 := by
      rw [show (∑ r : Fin m, if m - h ≤ r.val ∧ r.val < m - b then p + lam else 0) =
          (p + lam) * ∑ r : Fin m, if m - h ≤ r.val ∧ r.val < m - b then (1 : ℝ) else 0 by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun r _ => ?_; split_ifs <;> ring]
      rw [← hcnt]; ring
    have e3 : (∑ r : Fin m, if m - h ≤ r.val ∧ r.val < m - b then bit j (ζ r) - p - lam else 0) =
        (∑ r : Fin m, if m - h ≤ r.val ∧ r.val < m - b then bit j (ζ r) else 0) -
          ∑ r : Fin m, if m - h ≤ r.val ∧ r.val < m - b then p + lam else 0 := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun r _ => ?_
      split_ifs <;> ring
    rw [e3, ← e1, ← e2]; ring
  rw [hL]
  -- right side: reindex by `Fin.rev`
  simp only [Ville.prefixSum, Dfwd]
  refine (Fintype.sum_equiv Fin.revPerm _ _ fun r' => ?_).symm
  simp only [Fin.revPerm_apply, Fin.val_rev, Fin.rev_rev]
  have hr := r'.isLt
  split_ifs with h1 h2 h3 h4 h5 <;> first | rfl | (exfalso; omega)

theorem bit_compl (j : Fin n) (T : Finset (Fin n)) : bit j (Finset.univ \ T) = 1 - bit j T := by
  classical
  by_cases h : j ∈ T <;> simp [bit, h]

/-- Backward identity, `h ≤ b ≤ m`. -/
theorem bwd_identity (p lam : ℝ) (j : Fin n) (b h : ℕ) (hhb : h ≤ b) (hb : b ≤ m)
    (ζ : Fin m → Finset (Fin n)) :
    Wω p (unflip b ζ) j h - Wω p (unflip b ζ) j b - lam * |(h : ℝ) - b| =
      Ville.prefixSum (Dbwd p lam j b) ζ (m - h) := by
  classical
  have hcnt := card_rows_between (m := m) (m - b) (m - h) (by omega)
  have hbh : ((m - h - (m - b) : ℕ) : ℝ) = (b : ℝ) - h := by
    rw [show m - h - (m - b) = b - h by omega]; push_cast [Nat.cast_sub hhb]; ring
  rw [hbh] at hcnt
  have habs : |(h : ℝ) - b| = (b : ℝ) - h := by
    rw [abs_sub_comm]
    exact abs_of_nonneg (by
      have : (h : ℝ) ≤ b := by exact_mod_cast hhb
      linarith)
  simp only [Wω, Nω_eq_sum, habs]
  have e1 : (∑ r : Fin m, if m - h ≤ r.val then bit j (unflip b ζ r) else 0) -
      (∑ r : Fin m, if m - b ≤ r.val then bit j (unflip b ζ r) else 0) =
      ∑ r : Fin m, if m - b ≤ r.val ∧ r.val < m - h then bit j (ζ r) - 1 else 0 := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    by_cases h1 : m - h ≤ r.val <;> by_cases h2 : m - b ≤ r.val
    · have : ¬ r.val < m - h := by omega
      simp [h1, h2, this]
    · omega
    · have h3 : r.val < m - h := by omega
      have h4 : ¬ r.val < m - b := by omega
      simp only [h1, h2, h3, if_true, if_false, and_self, unflip, h4, bit_compl]
      ring
    · simp [h1, h2]
  have e2 : (∑ r : Fin m, if m - b ≤ r.val ∧ r.val < m - h then (1 - p) + lam else 0) =
      ((1 - p) + lam) * ((b : ℝ) - h) := by
    rw [hcnt, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    split_ifs <;> ring
  have e3 : (∑ r : Fin m, if m - b ≤ r.val ∧ r.val < m - h then bit j (ζ r) - 1 else 0) =
      (∑ r : Fin m, if m - b ≤ r.val ∧ r.val < m - h then bit j (ζ r) - (1 - p) - lam else 0) +
        ∑ r : Fin m, if m - b ≤ r.val ∧ r.val < m - h then -p + lam else 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    split_ifs <;> ring
  have e4 : (∑ r : Fin m, if m - b ≤ r.val ∧ r.val < m - h then -p + lam else 0) =
      (-p + lam) * ((b : ℝ) - h) := by
    rw [hcnt, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    split_ifs <;> ring
  have hR : Ville.prefixSum (Dbwd p lam j b) ζ (m - h) =
      ∑ r : Fin m, if m - b ≤ r.val ∧ r.val < m - h then bit j (ζ r) - (1 - p) - lam else 0 := by
    simp only [Ville.prefixSum, Dbwd]
    refine Finset.sum_congr rfl fun r _ => ?_
    by_cases h1 : r.val < m - h <;> by_cases h2 : m - b ≤ r.val <;> simp [h1, h2]
  rw [hR]
  have := e1
  rw [e3, e4] at this
  linarith

theorem Yplus_nonneg (p lam : ℝ) (j : Fin n) (b : ℕ) (ζ : Fin m → Finset (Fin n)) :
    0 ≤ Yplus p lam j b ζ := by
  have := Finset.le_sup' (s := Finset.range (m + 1))
    (f := fun h => Ville.prefixSum (Dfwd p lam j b) (fun r => ζ (Fin.rev r)) h)
    (Finset.mem_range.2 (Nat.succ_pos m))
  simpa [Yplus, Ville.prefixSum_zero] using this

theorem Yminus_nonneg (p lam : ℝ) (j : Fin n) (b : ℕ) (ζ : Fin m → Finset (Fin n)) :
    0 ≤ Yminus p lam j b ζ := by
  have := Finset.le_sup' (s := Finset.range (m + 1))
    (f := fun h => Ville.prefixSum (Dbwd p lam j b) ζ h) (Finset.mem_range.2 (Nat.succ_pos m))
  simpa [Yminus, Ville.prefixSum_zero] using this

/-- The dual variable is at most the larger of the two walk maxima. -/
theorem Yω_le_max (p lam : ℝ) (j : Fin n) (b : ℕ) (hb : b ≤ m) (ζ : Fin m → Finset (Fin n)) :
    Yω p lam (unflip b ζ) j b ≤ max (Yplus p lam j b ζ) (Yminus p lam j b ζ) := by
  apply Finset.sup'_le
  intro h hh
  rw [Finset.mem_range] at hh
  by_cases hbh : b ≤ h
  · rw [fwd_identity p lam j b h hbh (by omega) ζ]
    refine le_trans ?_ (le_max_left _ _)
    exact Finset.le_sup' (f := fun h => Ville.prefixSum (Dfwd p lam j b) (fun r => ζ (Fin.rev r)) h)
      (Finset.mem_range.2 hh)
  · push_neg at hbh
    rw [bwd_identity p lam j b h hbh.le hb ζ]
    refine le_trans ?_ (le_max_right _ _)
    exact Finset.le_sup' (f := fun h => Ville.prefixSum (Dbwd p lam j b) ζ h)
      (Finset.mem_range.2 (by omega))

end Round2Col
