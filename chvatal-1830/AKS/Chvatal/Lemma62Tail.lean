module

public import AKS.Chvatal.Lemma62
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # Per-column-set tail estimate (Chvátal Lemma 6.2 (i), uses Lemma 6.3)

`scramble_tail_union_top`: for a monotone `c` with `j ≥ 1` ones, the fraction of scrambles putting at
least `T ≥ j s/n` ones of the top rows into some `s`-set of columns is at most
`C(n,s) (e j s/(n T))^T` (Poisson-type exponential moment, then Markov with `e^λ = T/μ`). -/

@[expose] public section

namespace Chvatal

/-- Ones that the scramble `σ` places in the columns `S`, counted only over the rows `R`. -/
def onesInRows {m n : Nat} (c : MonotoneColumnSums m n) (σ : Scramble m n)
    (R : Finset (Fin m)) (S : Finset (Fin n)) : Nat :=
  ∑ r ∈ R, ((scrambledRowOnes c σ r) ∩ S).card

/-- Poisson-type exponential moment over a row subset `R`. -/
theorem avg_exp_onesInRows_le {m n : Nat} (hn : 0 < n)
    (c : MonotoneColumnSums m n) (R : Finset (Fin m)) (S : Finset (Fin n)) (lam : ℝ)
    (hlam : 0 ≤ lam) :
    (∑ σ : Scramble m n, Real.exp (lam * (onesInRows c σ R S : ℝ))) /
        Fintype.card (Scramble m n) ≤
      Real.exp ((Real.exp lam - 1) *
        ((∑ r ∈ R, ((monotoneRowOnes c r).card : ℝ)) / n) * S.card) := by
  classical
  set F : Fin m → Equiv.Perm (Fin n) → ℝ := fun r π =>
    if r ∈ R then Real.exp (lam * (rowHit c S r π : ℝ)) else 1 with hF
  have hpos : (0 : ℝ) < Fintype.card (Equiv.Perm (Fin n)) := by exact_mod_cast Fintype.card_pos
  have hσ (σ : Scramble m n) :
      Real.exp (lam * (onesInRows c σ R S : ℝ)) = ∏ r : Fin m, F r (σ r) := by
    have hX : (onesInRows c σ R S : ℝ) = ∑ r ∈ R, (rowHit c S r (σ r) : ℝ) := by
      simp [onesInRows, rowHit, scrambledRowOnes]
    rw [hX, Finset.mul_sum, Real.exp_sum, hF]
    simp only
    rw [Finset.prod_ite_mem Finset.univ R, Finset.univ_inter]
  have havg : (∑ σ : Scramble m n, Real.exp (lam * (onesInRows c σ R S : ℝ))) /
        Fintype.card (Scramble m n) =
      ∏ r : Fin m, (∑ π, F r π) / Fintype.card (Equiv.Perm (Fin n)) := by
    have hsum : ∑ σ : Scramble m n, ∏ r : Fin m, F r (σ r) = ∏ r, ∑ π, F r π :=
      (Fintype.prod_sum F).symm
    simp_rw [hσ]
    rw [hsum, Finset.prod_div_distrib]
    simp [card_scramble]
  have hrow (r : Fin m) : (∑ π, F r π) / Fintype.card (Equiv.Perm (Fin n)) ≤
      Real.exp (if r ∈ R then
        (Real.exp lam - 1) * (((monotoneRowOnes c r).card : ℝ) / n) * S.card else 0) := by
    by_cases hr : r ∈ R
    · simp only [hF, hr, if_true]
      set pr : ℝ := ((monotoneRowOnes c r).card : ℝ) / n
      have hp0 : (0 : ℝ) ≤ pr := by positivity
      have hbase : (0 : ℝ) ≤ 1 - pr + pr * Real.exp lam := by
        nlinarith [row_density_le_one hn c r, Real.exp_nonneg lam]
      calc _ ≤ (1 - pr + pr * Real.exp lam) ^ S.card := avg_exp_rowHit_le hn c S r lam hlam
        _ ≤ (Real.exp (pr * (Real.exp lam - 1))) ^ S.card :=
            pow_le_pow_left₀ hbase (by linarith [Real.add_one_le_exp (pr * (Real.exp lam - 1))]) _
        _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
    · simp [hF, hr]
  rw [havg]
  calc _ ≤ ∏ r : Fin m, Real.exp (if r ∈ R then
          (Real.exp lam - 1) * (((monotoneRowOnes c r).card : ℝ) / n) * S.card else 0) :=
        Finset.prod_le_prod
          (fun r _ => div_nonneg (Finset.sum_nonneg fun π _ => by
            simp only [hF]; split_ifs <;> positivity) hpos.le) (fun r _ => hrow r)
    _ = _ := by
        rw [← Real.exp_sum, Finset.sum_ite_mem, Finset.univ_inter, ← Finset.sum_mul,
          ← Finset.mul_sum, ← Finset.sum_div]

/-- **S1** (paper Lemma 6.3 + inequality (6.2), Poisson/Chernoff form): a set `bad` of scrambles
putting at least `T ≥ J s/n` ones into the columns `S` within the rows `R` (which carry at most `J`
ones of `c`) has fraction at most `(e J s / (n T))^T`. -/
theorem scramble_tail_fixed_set {m n : Nat} (hn : 0 < n)
    (c : MonotoneColumnSums m n) (R : Finset (Fin m)) (S : Finset (Fin n))
    (J T : ℝ) (hJ : 0 < J) (hS : 0 < S.card)
    (hR : (∑ r ∈ R, ((monotoneRowOnes c r).card : ℝ)) ≤ J)
    (hT : J * S.card / n ≤ T)
    (bad : Finset (Scramble m n))
    (hbad : ∀ σ ∈ bad, T ≤ (onesInRows c σ R S : ℝ)) :
    (bad.card : ℝ) / Fintype.card (Scramble m n) ≤
      (Real.exp 1 * J * S.card / (n * T)) ^ T := by
  classical
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hs0 : (0 : ℝ) < S.card := by exact_mod_cast hS
  set μ : ℝ := J * S.card / n with hμ
  have hμ0 : 0 < μ := by positivity
  have hT0 : 0 < T := hμ0.trans_le hT
  set lam : ℝ := Real.log T - Real.log μ with hlam
  have hlam0 : 0 ≤ lam := by linarith [Real.log_le_log hμ0 hT]
  have hexplam : Real.exp lam = T / μ := by
    rw [hlam, Real.exp_sub, Real.exp_log hT0, Real.exp_log hμ0]
  have htot : (0 : ℝ) < Fintype.card (Scramble m n) := by exact_mod_cast Fintype.card_pos
  have hmarkov : (bad.card : ℝ) ≤ Real.exp (-lam * T) *
      ∑ σ : Scramble m n, Real.exp (lam * (onesInRows c σ R S : ℝ)) := by
    calc (bad.card : ℝ) = ∑ σ ∈ bad, (1 : ℝ) := by simp
      _ ≤ ∑ σ ∈ bad, Real.exp (lam * ((onesInRows c σ R S : ℝ) - T)) :=
          Finset.sum_le_sum fun σ hσ =>
            Real.one_le_exp (mul_nonneg hlam0 (sub_nonneg.mpr (hbad σ hσ)))
      _ ≤ ∑ σ : Scramble m n, Real.exp (lam * ((onesInRows c σ R S : ℝ) - T)) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            fun _ _ _ => Real.exp_nonneg _
      _ = _ := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun σ _ => by rw [← Real.exp_add]; congr 1; ring
  have hμ' : (∑ r ∈ R, ((monotoneRowOnes c r).card : ℝ)) / n * S.card ≤ μ := by
    rw [hμ, ← div_mul_eq_mul_div]
    gcongr
  have hel : 0 ≤ Real.exp lam - 1 := by linarith [Real.add_one_le_exp lam]
  have hmgf2 := (avg_exp_onesInRows_le hn c R S lam hlam0).trans (Real.exp_le_exp.mpr
    (show _ ≤ (Real.exp lam - 1) * μ by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hμ' hel))
  rw [div_le_iff₀ htot] at hmgf2 ⊢
  have hfrac : (bad.card : ℝ) ≤
      Real.exp (-lam * T + (Real.exp lam - 1) * μ) * Fintype.card (Scramble m n) := by
    rw [Real.exp_add, mul_assoc]
    exact hmarkov.trans (mul_le_mul_of_nonneg_left hmgf2 (Real.exp_nonneg _))
  refine hfrac.trans (mul_le_mul_of_nonneg_right ?_ htot.le)
  have hbase : Real.exp 1 * J * S.card / (n * T) = Real.exp 1 * μ / T := by
    rw [hμ]; field_simp
  rw [hbase, Real.rpow_def_of_pos (by positivity)]
  refine Real.exp_le_exp.mpr ?_
  have hlog : Real.log (Real.exp 1 * μ / T) = 1 + Real.log μ - Real.log T := by
    rw [Real.log_div (by positivity) hT0.ne', Real.log_mul (Real.exp_pos 1).ne' hμ0.ne',
      Real.log_exp]
  rw [hlog, hexplam, show (T / μ - 1) * μ = T - μ by field_simp, hlam]
  nlinarith [hμ0]

/-- Event "some `s`-subset of columns carries at least `T` ones within the rows `R`". -/
noncomputable def tailBadSet {m n : Nat} (c : MonotoneColumnSums m n) (R : Finset (Fin m))
    (s : Nat) (T : ℝ) : Finset (Scramble m n) := by
  classical
  exact Finset.univ.filter fun σ =>
    ∃ S ∈ (Finset.univ : Finset (Fin n)).powersetCard s, T ≤ (onesInRows c σ R S : ℝ)

/-- **S2** (union bound over the `C(n,s)` column sets, top rows): for `j = totalColumnOnes c ≥ 1`,
`h = f/2` and `T ≥ j s / n`: `p(s) ≤ C(n,s) (e j s / (n T))^T`. -/
theorem scramble_tail_union_top {m n : Nat} (hn : 0 < n)
    (c : MonotoneColumnSums m n) (h s : Nat) (T : ℝ)
    (hj : 0 < totalColumnOnes c) (hs : 0 < s)
    (hT : (totalColumnOnes c : ℝ) * s / n ≤ T) :
    ((tailBadSet c (topRows m h) s T).card : ℝ) / Fintype.card (Scramble m n) ≤
      (n.choose s : ℝ) * (Real.exp 1 * (totalColumnOnes c : ℝ) * s / (n * T)) ^ T := by
  classical
  have htot : (0 : ℝ) < Fintype.card (Scramble m n) := by exact_mod_cast Fintype.card_pos
  have hR : (∑ r ∈ topRows m h, ((monotoneRowOnes c r).card : ℝ)) ≤ (totalColumnOnes c : ℝ) := by
    rw [show (totalColumnOnes c : ℝ) = ∑ r : Fin m, ((monotoneRowOnes c r).card : ℝ) by
      exact_mod_cast totalColumnOnes_eq_sum_rowOnes c]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      fun _ _ _ => Nat.cast_nonneg _
  set P := (Finset.univ : Finset (Fin n)).powersetCard s
  set B : Finset (Fin n) → Finset (Scramble m n) := fun S =>
    Finset.univ.filter fun σ => T ≤ (onesInRows c σ (topRows m h) S : ℝ)
  have hsub : tailBadSet c (topRows m h) s T ⊆ P.biUnion B := by
    intro σ hσ
    simp only [tailBadSet, Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    obtain ⟨S, hS, hX⟩ := hσ
    exact Finset.mem_biUnion.mpr ⟨S, hS, by simp [B, hX]⟩
  have hper : ∀ S ∈ P, ((B S).card : ℝ) ≤
      (Real.exp 1 * totalColumnOnes c * s / (n * T)) ^ T * Fintype.card (Scramble m n) := by
    intro S hS
    have hcS : S.card = s := (Finset.mem_powersetCard.mp hS).2
    have := scramble_tail_fixed_set hn c _ S _ T (by exact_mod_cast hj) (by rwa [hcS]) hR
      (by rwa [hcS]) (B S) fun σ hσ => (Finset.mem_filter.mp hσ).2
    rw [hcS] at this
    exact (div_le_iff₀ htot).mp this
  rw [div_le_iff₀ htot]
  calc ((tailBadSet c (topRows m h) s T).card : ℝ) ≤ ∑ S ∈ P, ((B S).card : ℝ) := by
        exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    _ ≤ ∑ S ∈ P, (Real.exp 1 * totalColumnOnes c * s / (n * T)) ^ T *
          Fintype.card (Scramble m n) := Finset.sum_le_sum hper
    _ = _ := by
        rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
        ring

end Chvatal
