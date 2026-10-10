module

public import AKS.Paterson.BagParams
public import Mathlib.Algebra.Order.Floor.Ring

/-! # Even subtree rounding for Paterson's bags

Paterson (1990), Section 7, rounds the content of each active subtree upward
to the next even integer. A bag is the subtree minus its four active
granddaughter subtrees. Rounding subtree totals, rather than independent bag
sizes, keeps that conservation identity exact.
-/

@[expose] public section

namespace Paterson.Bags

def evenCeil (x : ℚ) : ℕ := 2 * ⌈x / 2⌉₊

theorem evenCeil_even (x : ℚ) : 2 ∣ evenCeil x :=
  dvd_mul_right 2 _

theorem le_evenCeil (x : ℚ) : x ≤ (evenCeil x : ℚ) := by
  have h := Nat.le_ceil (x / 2)
  simp only [evenCeil, Nat.cast_mul, Nat.cast_ofNat]
  linarith

theorem evenCeil_lt_add_two {x : ℚ} (hx : 0 ≤ x) :
    (evenCeil x : ℚ) < x + 2 := by
  have h := Nat.ceil_lt_add_one (show 0 ≤ x / 2 by linarith)
  simp only [evenCeil, Nat.cast_mul, Nat.cast_ofNat]
  linarith

def roundedBag (subtree grandchildren : ℚ) : ℕ :=
  evenCeil subtree - 4 * evenCeil grandchildren

/-- A full bag loses fewer than eight wires and gains fewer than two wires
under the subtree rounding recipe. The capacity lower bound makes natural
subtraction agree with the exact conservation difference. -/
theorem roundedBag_bounds {a b g : ℚ} (hg : 0 ≤ g)
    (hab : a = b + 4 * g) (hb : 8 ≤ b) :
    b - 8 < (roundedBag a g : ℚ) ∧ (roundedBag a g : ℚ) < b + 2 := by
  have ha : 0 ≤ a := by linarith
  have hga := le_evenCeil g
  have hgb := evenCeil_lt_add_two hg
  have haa := le_evenCeil a
  have hab' := evenCeil_lt_add_two ha
  have hleQ : (4 : ℚ) * evenCeil g ≤ evenCeil a := by linarith
  have hle : 4 * evenCeil g ≤ evenCeil a := by exact_mod_cast hleQ
  simp only [roundedBag, Nat.cast_sub hle, Nat.cast_mul, Nat.cast_ofNat]
  constructor <;> linarith

theorem roundedBag_even (a g : ℚ) : 2 ∣ roundedBag a g := by
  unfold roundedBag
  exact Nat.dvd_sub (evenCeil_even a) (dvd_mul_of_dvd_right (evenCeil_even g) 4)

/-- The lower bag-size estimate, together with the support slack, is enough
to apply the small-cohort separator to every cohort allowed by the invariant. -/
theorem support_of_rounded_size {mu support b : ℚ} {n : ℕ}
    (hsupport : 0 ≤ support) (hsize : b - 8 ≤ (n : ℚ))
    (hslack : 8 * support ≤ (support - mu) * b) :
    mu * b ≤ support * n := by
  have h := mul_le_mul_of_nonneg_left hsize hsupport
  nlinarith

theorem roundedParams_support_slack {b : ℚ} (hb : 1600 ≤ b) :
    8 * roundedParams.support ≤
      (roundedParams.support - roundedParams.mu) * b := by
  norm_num [roundedParams, patersonMu] at *
  linarith

/-- One end fringe in the rounded subtree recipe. The two ends together
receive approximately `lambda * b` registers. -/
def roundedFringe (a b lambda : ℚ) : ℕ :=
  ⌈a / 2⌉₊ - ⌈(a - lambda * b) / 2⌉₊

theorem roundedFringe_bounds {a b lambda : ℚ}
    (ha : 0 ≤ a) (hrest : 0 ≤ a - lambda * b) (hremoved : 0 ≤ lambda * b) :
    lambda * b / 2 - 1 < (roundedFringe a b lambda : ℚ) ∧
      (roundedFringe a b lambda : ℚ) < lambda * b / 2 + 1 := by
  have hmono : ⌈(a - lambda * b) / 2⌉₊ ≤ ⌈a / 2⌉₊ :=
    Nat.ceil_mono (by linarith)
  have h₁ := Nat.le_ceil (a / 2)
  have h₂ := Nat.ceil_lt_add_one (show 0 ≤ a / 2 by linarith)
  have h₃ := Nat.le_ceil ((a - lambda * b) / 2)
  have h₄ := Nat.ceil_lt_add_one (show 0 ≤ (a - lambda * b) / 2 by linarith)
  simp only [roundedFringe, Nat.cast_sub hmono]
  constructor <;> linarith

/-- Sufficient slack for the rounded fringe to contain the five-level
separator's `n/32` fringe. This arithmetic obligation is independent of the
remaining arbitrary-arity separator correctness proof. -/
theorem roundedFringe_covers_thirtysecond {a b : ℚ} {n : ℕ}
    (ha : 0 ≤ a) (hrest : 0 ≤ a - roundedParams.lambda * b)
    (hb : roundedParams.minCapacity ≤ b) (hn : (n : ℚ) ≤ b + 2) :
    (n : ℚ) / 32 ≤ (roundedFringe a b roundedParams.lambda : ℚ) := by
  have hb0 : 0 ≤ b := roundedParams.minCapacity_pos.le.trans hb
  have hf := (roundedFringe_bounds ha hrest
    (mul_nonneg roundedParams.lambda_pos.le hb0)).1
  norm_num [roundedParams] at hb hf ⊢
  linarith

end Paterson.Bags
