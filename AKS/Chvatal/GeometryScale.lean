module

/-
  # Scaling a separator template into the paper's m-range (DCS-TR-294 §5/§7)

  The paper picks a template (m', f0, b0) with 0 < m' < 2^37 (equation (5.2):
  m' < 2A²k² = 2^37) and scales by the largest r with 2^r·m' ≤ 2^60, setting
  m = 2^r m', f = 2^r f0. This module proves the key scaling invariants.
-/

public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

@[expose] public section

namespace Chvatal

/-! **Scaling template existence: finding the largest r such that 2^r · m' ≤ 2^60** -/

/-- For any m' with 0 < m' ≤ 2^60, there exists an r such that 2^59 < 2^r * m' ≤ 2^60.
    This is the key existence result for scaling: we can always find the optimal doubling scale. -/
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
    have : 1 ≤ m' := hm'_pos
    calc 2 ^ 59 < 2 ^ 60 * 1 := by norm_num
      _ ≤ 2 ^ 60 * m' := Nat.mul_le_mul_left _ this
  · have hlt : r < 60 := by omega
    have hn : ¬ (2 ^ (r + 1) * m' ≤ 2 ^ 60) :=
      Nat.findGreatest_is_greatest (P := fun r => 2 ^ r * m' ≤ 2 ^ 60) (Nat.lt_succ_self r)
        (by omega)
    rw [pow_succ] at hn
    have h2 : 2 ^ 60 = 2 * 2 ^ 59 := by norm_num
    have e : 2 ^ r * 2 * m' = 2 * (2 ^ r * m') := by ring
    omega

/-! **Bounds on scaled fringe size** -/

/-- After scaling by 2^r, the fringe size 2^r * f0 is large enough and even.
    This ensures the scaled fringe has enough resources and proper parity. -/
theorem scaled_fringe_big : ∀ f0 m' r : ℕ, 4095 ≤ f0 → 0 < m' → m' < 2^37 → 2^59 < 2^r * m' →
    17000000000 < 2^r * f0 ∧ Even (2^r * f0) := by
  intro f0 m' r hf0_ge hm'_pos hm'_lt hr_scale
  constructor
  · -- Show 17000000000 < 2^r * f0
    -- From 2^r * m' > 2^59 and m' < 2^37, we derive 2^r > 2^22
    have h_lower : 2^59 < 2^r * m' := hr_scale
    have h_upper : m' < 2^37 := hm'_lt

    -- Key lemma: if 2^r ≤ 2^22, then 2^r * m' < 2^59
    have hr_gt_22 : 2^22 < 2^r := by
      by_contra h_neg
      push_neg at h_neg
      -- h_neg: 2^r ≤ 2^22
      -- From h_upper: m' < 2^37
      -- So: 2^r * m' ≤ 2^22 * m' < 2^22 * 2^37 = 2^59
      have h1 : 2^r * m' ≤ 2^22 * m' := Nat.mul_le_mul_right m' h_neg
      have h2 : 2^22 * m' < 2^22 * 2^37 := Nat.mul_lt_mul_of_pos_left h_upper (by norm_num : 0 < 2^22)
      have eq : (2 : ℕ)^22 * 2^37 = 2^59 := by norm_num
      linarith

    -- From 2^22 < 2^r, we can deduce 22 < r
    have h_r_gt_22_nat : 22 < r := by
      by_contra h_not
      push_neg at h_not
      -- If r ≤ 22, then 2^r ≤ 2^22
      have : 2^r ≤ 2^22 := Nat.pow_le_pow_right (by norm_num : 0 < 2) h_not
      omega

    -- Therefore r ≥ 23, so 2^23 ≤ 2^r
    have h_r_ge_23 : 2^23 ≤ 2^r := by
      -- Since 22 < r, we have 23 ≤ r
      have : 23 ≤ r := by omega
      exact Nat.pow_le_pow_right (by norm_num : 0 < 2) this

    -- Therefore: 2^r * f0 ≥ 2^23 * 4095
    have h_prod : 2^23 * 4095 ≤ 2^r * f0 := Nat.mul_le_mul h_r_ge_23 hf0_ge

    -- We know 2^23 * 4095 = 34351349760 > 17000000000
    calc 2^r * f0 ≥ 2^23 * 4095 := h_prod
         _ = 34351349760 := by norm_num
         _ > 17000000000 := by norm_num

  · -- Show Even (2^r * f0), i.e., ∃ k, 2^r * f0 = 2 * k
    -- First check if r = 0, which would lead to contradiction
    by_cases hr_zero : r = 0
    · -- If r = 0: 2^59 < 2^0 * m' = m' < 2^37
      rw [hr_zero] at hr_scale
      norm_num at hr_scale
      -- Now hr_scale says: 576460752303423488 < m'
      -- But m' < 2^37 = 137438953472
      -- This is impossible
      exfalso
      omega

    · -- If r ≠ 0, then r > 0, so 2^r = 2 * 2^(r-1)
      have hr_pos : 0 < r := by omega
      use 2^(r - 1) * f0

      -- Show 2^r * f0 = 2 * (2^(r - 1) * f0)
      have h_pow : 2^r = 2 * 2^(r - 1) := by
        -- For r > 0: 2^r = 2^(1 + (r-1)) = 2 * 2^(r-1)
        have h_sub : r = r - 1 + 1 := by omega
        rw [h_sub, Nat.pow_add]
        norm_num [Nat.pow_one, mul_comm]
      rw [h_pow]
      ring

/-! **Ratios are preserved under uniform scaling** -/

/-- Scaling numerator and denominator by the same factor 2^r preserves the ratio in ℚ. -/
theorem scaled_ratio : ∀ f0 m' r : ℕ, 0 < m' → (2^r*f0 : ℚ) / (2^r*m') = (f0 : ℚ) / m' := by
  intro f0 m' r hm'_pos
  field_simp [Nat.cast_pos.mpr hm'_pos]

/-! **Dimension equation under scaling** -/

/-- If m' = 2*f0 + k*b0, then after scaling by 2^r we have 2^r*m' = 2*(2^r*f0) + k*(2^r*b0). -/
theorem scaled_m_eq : ∀ f0 b0 k r m' : ℕ, m' = 2*f0 + k*b0 → 2^r*m' = 2*(2^r*f0) + k*(2^r*b0) := by
  intro f0 b0 k r m' hm_eq
  rw [hm_eq]
  ring

end Chvatal
