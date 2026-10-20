import Mathlib.Tactic

/-! # Fringe by double weak duality: level crossing (UB-34)

The sparse-regime tail of a walk maximum `Y = max_h (N(h) − D(h))`, with `N` a nondecreasing count
and `D` a nondecreasing drift, is controlled by the times at which the count first reaches each level:
if `Y > y`, then some level `k > y` is reached by height `T`, where `T` is any height beyond which
`D ≥ k − y`. `level_crossing` states this deterministically, so a union bound over `k` reduces the
tail to binomial tails `P(N(T_k) ≥ k)`. -/

namespace FringeDuality

/-- **Level crossing.** If `N` is monotone, `D` is monotone, and `N h − D h > y` for some `h ≤ H`,
then for `k = N h` we have `y < k` and, for every `T` with `D h < k − y → h ≤ T` (in particular for `T`
the last height with `D T < k − y`), `k ≤ N T`. -/
theorem level_crossing (N : ℕ → ℕ) (D : ℕ → ℝ) (hN : Monotone N) (hD0 : ∀ h, 0 ≤ D h) (y : ℝ)
    (h : ℕ) (hy : y < (N h : ℝ) - D h) (T : ℕ) (hT : ∀ h', D h' < (N h : ℝ) - y → h' ≤ T) :
    y < (N h : ℝ) ∧ N h ≤ N T := by
  have hD : D h < (N h : ℝ) - y := by linarith
  exact ⟨by linarith [hD0 h], hN (hT h hD)⟩

/-- The union form: `Y > y` implies that some level `k ∈ (y, K]` is reached by its deadline `T k`,
where the deadline satisfies `D h' < k − y → h' ≤ T k`. -/
theorem exists_level_of_gt (N : ℕ → ℕ) (D : ℕ → ℝ) (hN : Monotone N) (hD0 : ∀ h, 0 ≤ D h)
    (y : ℝ) (h : ℕ) (hy : y < (N h : ℝ) - D h) (T : ℕ → ℕ)
    (hT : ∀ (k : ℕ) (h' : ℕ), D h' < (k : ℝ) - y → h' ≤ T k) :
    ∃ k : ℕ, y < (k : ℝ) ∧ k ≤ N (T k) :=
  ⟨N h, level_crossing N D hN hD0 y h hy (T (N h)) (hT (N h))⟩

end FringeDuality
