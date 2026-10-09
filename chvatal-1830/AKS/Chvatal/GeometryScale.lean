module

public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-! # Scaling a separator template into the paper's m-range (DCS-TR-294 §5/§7)

Template `(m', f0, b0)` with `0 < m' < 2^37` is scaled by the largest `r` with `2^r·m' ≤ 2^60`. -/

@[expose] public section

namespace Chvatal

/-- For `0 < m' ≤ 2^60` there is `r` with `2^59 < 2^r * m' ≤ 2^60`. -/
theorem exists_pow_scale : ∀ m' : ℕ, 0 < m' → m' ≤ 2^60 → ∃ r : ℕ, 2^59 < 2^r * m' ∧ 2^r * m' ≤ 2^60 := by
  intro m' hm'_pos hm'_le
  have hP0 : (fun r => 2 ^ r * m' ≤ 2 ^ 60) 0 := by simpa using hm'_le
  set r := Nat.findGreatest (fun r => 2 ^ r * m' ≤ 2 ^ 60) 60 with hr
  have hspec : 2 ^ r * m' ≤ 2 ^ 60 := Nat.findGreatest_spec (P := fun r => 2 ^ r * m' ≤ 2 ^ 60)
    (Nat.zero_le 60) hP0
  have hr60 : r ≤ 60 := Nat.findGreatest_le 60
  refine ⟨r, ?_, hspec⟩
  by_cases h60 : r = 60
  · rw [h60]
    have : 2 ^ 60 * 1 ≤ 2 ^ 60 * m' := Nat.mul_le_mul_left _ hm'_pos
    omega
  · have hn : ¬ (2 ^ (r + 1) * m' ≤ 2 ^ 60) :=
      Nat.findGreatest_is_greatest (P := fun r => 2 ^ r * m' ≤ 2 ^ 60) (Nat.lt_succ_self r)
        (by omega)
    rw [pow_succ, mul_right_comm] at hn
    omega

/-- `m' = 2*f0 + k*b0` is preserved by scaling by `2^r`. -/
theorem scaled_m_eq : ∀ f0 b0 k r m' : ℕ, m' = 2*f0 + k*b0 → 2^r*m' = 2*(2^r*f0) + k*(2^r*b0) := by
  intro f0 b0 k r m' hm_eq
  rw [hm_eq]
  ring

/-- Ratio form: `f0 · 2^37 ≥ 4095 · m'` (true for every §5 template) gives `2^r f0` big and even. -/
theorem scaled_fringe_big_ratio (f0 m' r : ℕ) (hm' : 0 < m') (hmle : m' ≤ 2 ^ 37)
    (hratio : 4095 * m' ≤ f0 * 2 ^ 37) (hr : 2 ^ 59 < 2 ^ r * m') :
    17000000000 < 2 ^ r * f0 ∧ Even (2 ^ r * f0) := by
  have h22 : 2 ^ 22 < 2 ^ r := by
    by_contra hc
    push_neg at hc
    have : 2 ^ r * m' ≤ 2 ^ 22 * 2 ^ 37 := Nat.mul_le_mul hc hmle
    omega
  have hr1 : 1 ≤ r := by
    by_contra hc
    obtain rfl : r = 0 := by omega
    norm_num at h22
  refine ⟨?_, (Nat.even_pow.mpr ⟨by decide, by omega⟩ : Even (2 ^ r)).mul_right _⟩
  have h1 : 4095 * (2 ^ r * m') ≤ 2 ^ r * f0 * 2 ^ 37 := by
    calc 4095 * (2 ^ r * m') = 2 ^ r * (4095 * m') := by ring
      _ ≤ 2 ^ r * (f0 * 2 ^ 37) := Nat.mul_le_mul_left _ hratio
      _ = 2 ^ r * f0 * 2 ^ 37 := by ring
  have h2 : 4095 * 2 ^ 59 < 2 ^ r * f0 * 2 ^ 37 :=
    lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_left hr (by norm_num)) h1
  have h3 : 4095 * 2 ^ 22 * 2 ^ 37 < 2 ^ r * f0 * 2 ^ 37 := by
    have : 4095 * 2 ^ 22 * 2 ^ 37 = 4095 * 2 ^ 59 := by norm_num
    omega
  have h4 := Nat.lt_of_mul_lt_mul_right h3
  omega

end Chvatal
