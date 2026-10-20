import AKS.Sub800.RowMgf
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

open Finset in
/-- **Chernoff for the hit count of one column.** Over independent rows, each a uniform `s`-subset
of the `n` output columns, the number `N` of rows in `R` whose subset contains the column `j`
satisfies `#{ζ : k ≤ N} ≤ e^{−θk} · Π_{r ∈ R} (1 − p + p e^θ) · C(n,s)^m`, `p = s/n`, `θ ≥ 0`. -/
theorem card_hits_ge_le {m n : ℕ} (hn : 0 < n) (s : ℕ) (j : Fin n) (R : Finset (Fin m)) (k : ℕ)
    (θ : ℝ) (hθ : 0 ≤ θ) :
    (((Fintype.piFinset fun _ : Fin m => (univ : Finset (Fin n)).powersetCard s).filter
        fun ζ => k ≤ (R.filter fun r => j ∈ ζ r).card).card : ℝ) ≤
      Real.exp (-(θ * k)) * (1 - (s : ℝ) / n + (s : ℝ) / n * Real.exp θ) ^ R.card *
        ((n.choose s : ℝ) ^ m) := by
  classical
  set Z := Fintype.piFinset fun _ : Fin m => (univ : Finset (Fin n)).powersetCard s
  set g : Fin m → Finset (Fin n) → ℝ := fun r T =>
    if r ∈ R then Real.exp (θ * (if j ∈ T then 1 else 0)) else 1
  -- indicator ≤ e^{θ(N − k)} = e^{−θk} Π_r g r (ζ r)
  have hpt : ∀ ζ ∈ Z, (if k ≤ (R.filter fun r => j ∈ ζ r).card then (1 : ℝ) else 0) ≤
      Real.exp (-(θ * k)) * ∏ r, g r (ζ r) := by
    intro ζ _
    have hprod : ∏ r, g r (ζ r) = Real.exp (θ * (R.filter fun r => j ∈ ζ r).card) := by
      have : ∏ r, g r (ζ r) = ∏ r, Real.exp (if r ∈ R ∧ j ∈ ζ r then θ else 0) := by
        refine Finset.prod_congr rfl fun r _ => ?_
        simp only [g]
        by_cases h1 : r ∈ R <;> by_cases h2 : j ∈ ζ r <;> simp [h1, h2]
      have hc : (univ.filter fun r => r ∈ R ∧ j ∈ ζ r) = R.filter fun r => j ∈ ζ r := by
        ext r; simp
      rw [this, ← Real.exp_sum, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
        nsmul_eq_mul, hc, mul_comm]
    rw [hprod, ← Real.exp_add]
    split_ifs with hk
    · apply Real.one_le_exp
      have : (k : ℝ) ≤ (R.filter fun r => j ∈ ζ r).card := by exact_mod_cast hk
      nlinarith
    · exact (Real.exp_pos _).le
  have hcard : ((Z.filter fun ζ => k ≤ (R.filter fun r => j ∈ ζ r).card).card : ℝ) =
      ∑ ζ ∈ Z, (if k ≤ (R.filter fun r => j ∈ ζ r).card then (1 : ℝ) else 0) := by
    rw [Finset.sum_boole]
  rw [hcard]
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [← Finset.mul_sum]
  -- factorise over rows
  have hfac : ∑ ζ ∈ Z, ∏ r, g r (ζ r) = ∏ r, ∑ T ∈ (univ : Finset (Fin n)).powersetCard s, g r T :=
    (Finset.prod_univ_sum (fun _ => (univ : Finset (Fin n)).powersetCard s) g).symm
  rw [hfac]
  have hrow : ∀ r, ∑ T ∈ (univ : Finset (Fin n)).powersetCard s, g r T =
      (n.choose s : ℝ) * (if r ∈ R then (1 - (s : ℝ) / n + (s : ℝ) / n * Real.exp θ) else 1) := by
    intro r
    by_cases hr : r ∈ R
    · have := RowMgf.sum_bit n s j hn (fun β => Real.exp (θ * (if β then 1 else 0)))
      simp only [g, hr, if_true]
      have e : ∀ T : Finset (Fin n), Real.exp (θ * (if j ∈ T then 1 else 0)) =
          Real.exp (θ * (if decide (j ∈ T) then 1 else 0)) := fun T => by
        by_cases h : j ∈ T <;> simp [h]
      simp_rw [e]
      rw [this]
      simp
    · simp only [g, hr, if_false, Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_powersetCard,
        Finset.card_univ, Fintype.card_fin]
  simp_rw [hrow]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]
  ring_nf
  exact le_refl _

end FringeDuality
