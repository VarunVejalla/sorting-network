import AKS.Bounds.Minimum
import Mathlib.Analysis.Subadditive

/-! # A conditional limit theorem for sorting depth

A uniform additive defect in multiplicative composition would suffice for
convergence along powers of two. The composition hypothesis is NOT proved.
This module records precisely what follows from it via Fekete's lemma.
-/

namespace SortingDepth

open Filter
open scoped Topology

theorem exists_ratio_limit_of_bounded_defect (a : ℕ → ℝ) (C : ℝ)
    (ha : ∀ k, 0 ≤ a k) (hC : 0 ≤ C)
    (hdefect : ∀ j k, a (j+k) ≤ a j + a k + C) :
    ∃ L : ℝ, Tendsto (fun k : ℕ => a k / k) atTop (𝓝 L) := by
  let b : ℕ → ℝ := fun k => a k + C
  have hb : Subadditive b := by
    intro j k
    dsimp [b]
    have hh := hdefect j k
    linarith
  have hbelow : BddBelow (Set.range (fun k : ℕ => b k / k)) := by
    refine ⟨0, ?_⟩
    rintro x ⟨k, rfl⟩
    exact div_nonneg (add_nonneg (ha k) hC) (Nat.cast_nonneg k)
  have ht := hb.tendsto_lim hbelow
  have hc : Tendsto (fun k : ℕ => C / (k : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  refine ⟨hb.lim, ?_⟩
  have he : (fun k : ℕ => a k / k) = (fun k : ℕ => b k / k - C / k) := by
    funext k
    dsimp [b]
    rw [add_div]
    ring
  rw [he]
  simpa using ht.sub hc

/-- This is conditional: no bounded-defect product construction is supplied. -/
theorem exists_dyadic_depth_limit_of_bounded_defect (C : ℕ)
    (hdefect : ∀ j k, minimum (2^(j+k)) ≤
      minimum (2^j) + minimum (2^k) + C) :
    ∃ L : ℝ, Tendsto (fun k : ℕ => (minimum (2^k) : ℝ) / k) atTop (𝓝 L) := by
  apply exists_ratio_limit_of_bounded_defect (fun k => (minimum (2^k) : ℝ)) C
  · intro k; exact Nat.cast_nonneg _
  · exact Nat.cast_nonneg _
  · intro j k
    exact_mod_cast hdefect j k

end SortingDepth
