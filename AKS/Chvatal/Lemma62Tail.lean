module
/-
  # Per-column-set tail estimate (Chvátal Lemma 6.2, claim (i), items A4 S1-S2)

  Source: V. Chvátal, Lecture Notes on the New AKS Sorting Network,
  Rutgers DCS-TR-294 (1992), proof of Lemma 6.2, claim (i); uses Lemma 6.3.

  Status: kernel-checked.
  * `avg_exp_onesInRows_le`: Poisson-type exponential moment of the number of ones that a
    uniformly random row-wise scramble puts in a fixed set `S` of columns, counted over an
    arbitrary set `R` of rows (e.g. the top `m - f/2` rows):
    `E exp(λ X) ≤ exp((e^λ - 1) · (ones in R) · |S| / n)`.
    (This reuses the exact hypergeometric-to-binomial row bound `avg_exp_rowHit_le` of
    `Lemma63`; it does NOT use the quadratic Hoeffding form of `avg_exp_onesInColumns_le`,
    which cannot give the `(e μ / T)^T` shape.)
  * `scramble_tail_fixed_set` (S1): `P[X ≥ T] ≤ (e J s / (n T))^T` by Markov with
    `e^λ = T / μ`, `μ = J s / n`.
  * `scramble_tail_union` (S2): union bound `p(s) ≤ C(n,s) (e J s/(n T))^T`.
  The real-analysis ratio bounds for `g` (S3) are NOT proved here.
-/

public import AKS.Chvatal.Lemma63
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

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
  have hcard :
      (Fintype.card (Scramble m n) : ℝ) =
        (Fintype.card (Equiv.Perm (Fin n)) : ℝ) ^ m := by
    exact_mod_cast card_scramble m n
  have hσ (σ : Scramble m n) :
      Real.exp (lam * (onesInRows c σ R S : ℝ)) = ∏ r : Fin m, F r (σ r) := by
    have hX : (onesInRows c σ R S : ℝ) = ∑ r ∈ R, (rowHit c S r (σ r) : ℝ) := by
      simp [onesInRows, rowHit, scrambledRowOnes]
    rw [hX, Finset.mul_sum, Real.exp_sum, hF]
    simp only
    rw [Finset.prod_ite_mem Finset.univ R, Finset.univ_inter]
  have hrewrite :
      ∑ σ : Scramble m n, Real.exp (lam * (onesInRows c σ R S : ℝ)) =
        ∏ r : Fin m, ∑ π : Equiv.Perm (Fin n), F r π := by
    simp_rw [hσ]
    exact (Fintype.prod_sum F).symm
  have havg_prod :
      (∑ σ : Scramble m n, Real.exp (lam * (onesInRows c σ R S : ℝ))) /
          Fintype.card (Scramble m n) =
        ∏ r : Fin m, ((∑ π : Equiv.Perm (Fin n), F r π) /
            Fintype.card (Equiv.Perm (Fin n))) := by
    rw [hrewrite, hcard]
    have hpow :
        ((Fintype.card (Equiv.Perm (Fin n)) : ℝ) ^ m) =
          ∏ _r : Fin m, (Fintype.card (Equiv.Perm (Fin n)) : ℝ) := by
      simp [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [hpow, ← Finset.prod_div_distrib]
  have hpos : (0 : ℝ) < Fintype.card (Equiv.Perm (Fin n)) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (Equiv.Perm (Fin n)))
  have hrow (r : Fin m) :
      ((∑ π : Equiv.Perm (Fin n), F r π) / Fintype.card (Equiv.Perm (Fin n))) ≤
        Real.exp (if r ∈ R then
          (Real.exp lam - 1) * (((monotoneRowOnes c r).card : ℝ) / n) * S.card else 0) := by
    by_cases hr : r ∈ R
    · simp only [hF, hr, if_true]
      set pr : ℝ := ((monotoneRowOnes c r).card : ℝ) / n
      have hp0 : (0 : ℝ) ≤ pr := by positivity
      have hbin := avg_exp_rowHit_le hn c S r lam hlam
      have hbase : (0 : ℝ) ≤ 1 - pr + pr * Real.exp lam := by
        have h1 : pr ≤ 1 := row_density_le_one hn c r
        have : (0 : ℝ) ≤ 1 - pr := sub_nonneg.mpr h1
        linarith [mul_nonneg hp0 (Real.exp_nonneg lam)]
      have hexp1 : 1 - pr + pr * Real.exp lam ≤ Real.exp (pr * (Real.exp lam - 1)) := by
        have := Real.add_one_le_exp (pr * (Real.exp lam - 1))
        linarith
      calc ((∑ π : Equiv.Perm (Fin n), Real.exp (lam * (rowHit c S r π : ℝ))) /
            Fintype.card (Equiv.Perm (Fin n)))
          ≤ (1 - pr + pr * Real.exp lam) ^ S.card := hbin
        _ ≤ (Real.exp (pr * (Real.exp lam - 1))) ^ S.card :=
            pow_le_pow_left₀ hbase hexp1 _
        _ = Real.exp ((Real.exp lam - 1) * pr * S.card) := by
            rw [← Real.exp_nat_mul]; congr 1; ring
    · simp only [hF, hr, if_false, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        mul_one, Real.exp_zero]
      rw [div_self hpos.ne']
  rw [havg_prod]
  calc ∏ r : Fin m, ((∑ π : Equiv.Perm (Fin n), F r π) / Fintype.card (Equiv.Perm (Fin n)))
      ≤ ∏ r : Fin m, Real.exp (if r ∈ R then
          (Real.exp lam - 1) * (((monotoneRowOnes c r).card : ℝ) / n) * S.card else 0) :=
        Finset.prod_le_prod
          (fun r _ => div_nonneg (Finset.sum_nonneg fun π _ => by
            simp only [hF]; split_ifs <;> positivity) hpos.le) (fun r _ => hrow r)
    _ = Real.exp ((Real.exp lam - 1) *
          ((∑ r ∈ R, ((monotoneRowOnes c r).card : ℝ)) / n) * S.card) := by
        rw [← Real.exp_sum]
        congr 1
        rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ R)]
        have h1 : ∑ r ∈ Finset.univ.filter (· ∈ R),
            (if r ∈ R then (Real.exp lam - 1) * (((monotoneRowOnes c r).card : ℝ) / n) * S.card
              else 0) =
            ∑ r ∈ R, (Real.exp lam - 1) * (((monotoneRowOnes c r).card : ℝ) / n) * S.card := by
          rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
          exact Finset.sum_congr rfl fun r hr => by simp [hr]
        have h2 : ∑ r ∈ Finset.univ.filter (¬ · ∈ R),
            (if r ∈ R then (Real.exp lam - 1) * (((monotoneRowOnes c r).card : ℝ) / n) * S.card
              else 0) = 0 :=
          Finset.sum_eq_zero fun r hr => by
            simp [Finset.mem_filter] at hr; simp [hr]
        rw [h1, h2, add_zero, ← Finset.sum_mul, ← Finset.mul_sum, ← Finset.sum_div]

/-- **S1** (paper Lemma 6.3 + inequality (6.2), Poisson/Chernoff form).
Let `R` be a set of rows (the top `m - f/2` rows in the paper) containing at most `J` ones of
`c` in total, `S` a fixed set of `s ≥ 1` columns and `T` a threshold with `J s / n ≤ T`.
Any set `bad` of scrambles that put at least `T` ones into the columns `S` within the rows `R`
has fraction at most `(e J s / (n T))^T`.  Proof: Markov on `exp(λ X)` with
`e^λ = T/μ`, `μ = J s / n`, using `avg_exp_onesInRows_le` and `1 + x ≤ e^x`. -/
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
  have hT0 : 0 < T := lt_of_lt_of_le hμ0 hT
  set lam : ℝ := Real.log T - Real.log μ with hlam
  have hlam0 : 0 ≤ lam := by
    have := Real.log_le_log hμ0 hT
    linarith
  have hexplam : Real.exp lam = T / μ := by
    rw [hlam, Real.exp_sub, Real.exp_log hT0, Real.exp_log hμ0]
  have htot : (0 : ℝ) < Fintype.card (Scramble m n) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (Scramble m n))
  have hmarkov :
      (bad.card : ℝ) ≤
        Real.exp (-lam * T) *
          ∑ σ : Scramble m n, Real.exp (lam * (onesInRows c σ R S : ℝ)) := by
    calc (bad.card : ℝ) = ∑ σ ∈ bad, (1 : ℝ) := by simp
      _ ≤ ∑ σ ∈ bad, Real.exp (lam * ((onesInRows c σ R S : ℝ) - T)) :=
          Finset.sum_le_sum fun σ hσ =>
            Real.one_le_exp (mul_nonneg hlam0 (sub_nonneg.mpr (hbad σ hσ)))
      _ ≤ ∑ σ : Scramble m n, Real.exp (lam * ((onesInRows c σ R S : ℝ) - T)) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            fun _ _ _ => Real.exp_nonneg _
      _ = Real.exp (-lam * T) *
            ∑ σ : Scramble m n, Real.exp (lam * (onesInRows c σ R S : ℝ)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun σ _ => ?_
          rw [← Real.exp_add]; congr 1; ring
  have hmgf := avg_exp_onesInRows_le hn c R S lam hlam0
  have hμ' : (∑ r ∈ R, ((monotoneRowOnes c r).card : ℝ)) / n * S.card ≤ μ := by
    rw [hμ]
    have : (∑ r ∈ R, ((monotoneRowOnes c r).card : ℝ)) / n ≤ J / n :=
      div_le_div_of_nonneg_right hR hn0.le
    calc (∑ r ∈ R, ((monotoneRowOnes c r).card : ℝ)) / n * S.card ≤ J / n * S.card :=
          mul_le_mul_of_nonneg_right this hs0.le
      _ = J * S.card / n := by ring
  have hel : 0 ≤ Real.exp lam - 1 := by
    have := Real.add_one_le_exp lam; linarith
  have hmgf2 :
      (∑ σ : Scramble m n, Real.exp (lam * (onesInRows c σ R S : ℝ))) /
          Fintype.card (Scramble m n) ≤ Real.exp ((Real.exp lam - 1) * μ) := by
    refine hmgf.trans (Real.exp_le_exp.mpr ?_)
    calc (Real.exp lam - 1) * ((∑ r ∈ R, ((monotoneRowOnes c r).card : ℝ)) / n) * S.card
        = (Real.exp lam - 1) *
            ((∑ r ∈ R, ((monotoneRowOnes c r).card : ℝ)) / n * S.card) := by ring
      _ ≤ (Real.exp lam - 1) * μ := mul_le_mul_of_nonneg_left hμ' hel
  have hsum_le :
      ∑ σ : Scramble m n, Real.exp (lam * (onesInRows c σ R S : ℝ)) ≤
        Real.exp ((Real.exp lam - 1) * μ) * Fintype.card (Scramble m n) :=
    (div_le_iff₀ htot).mp hmgf2
  have hfrac : (bad.card : ℝ) / Fintype.card (Scramble m n) ≤
      Real.exp (-lam * T + (Real.exp lam - 1) * μ) := by
    rw [div_le_iff₀ htot, Real.exp_add]
    calc (bad.card : ℝ) ≤ Real.exp (-lam * T) *
          ∑ σ : Scramble m n, Real.exp (lam * (onesInRows c σ R S : ℝ)) := hmarkov
      _ ≤ Real.exp (-lam * T) *
          (Real.exp ((Real.exp lam - 1) * μ) * Fintype.card (Scramble m n)) :=
          mul_le_mul_of_nonneg_left hsum_le (Real.exp_nonneg _)
      _ = _ := by ring
  refine hfrac.trans ?_
  have hbase : Real.exp 1 * J * S.card / (n * T) = Real.exp 1 * μ / T := by
    rw [hμ]; field_simp
  rw [hbase]
  have hbpos : 0 < Real.exp 1 * μ / T := by positivity
  rw [Real.rpow_def_of_pos hbpos]
  refine Real.exp_le_exp.mpr ?_
  have hlog : Real.log (Real.exp 1 * μ / T) = 1 + Real.log μ - Real.log T := by
    rw [Real.log_div (by positivity) hT0.ne', Real.log_mul (Real.exp_pos 1).ne' hμ0.ne',
      Real.log_exp]
  rw [hlog, hexplam]
  have : (T / μ - 1) * μ = T - μ := by field_simp
  rw [this, hlam]
  nlinarith [hμ0]

/-- Event "some `s`-subset of columns carries at least `T` ones within the rows `R`". -/
noncomputable def tailBadSet {m n : Nat} (c : MonotoneColumnSums m n) (R : Finset (Fin m))
    (s : Nat) (T : ℝ) : Finset (Scramble m n) := by
  classical
  exact Finset.univ.filter fun σ =>
    ∃ S ∈ (Finset.univ : Finset (Fin n)).powersetCard s, T ≤ (onesInRows c σ R S : ℝ)

/-- **S2** (union bound over the `C(n,s)` column sets):
`p(s) ≤ C(n,s) · (e J s / (n T))^T`, where `p(s)` is the fraction of scrambles for which some
`s`-set of columns carries at least `T` ones within the rows `R`. -/
theorem scramble_tail_union {m n : Nat} (hn : 0 < n)
    (c : MonotoneColumnSums m n) (R : Finset (Fin m)) (s : Nat) (J T : ℝ)
    (hJ : 0 < J) (hs : 0 < s)
    (hR : (∑ r ∈ R, ((monotoneRowOnes c r).card : ℝ)) ≤ J)
    (hT : J * s / n ≤ T) :
    ((tailBadSet c R s T).card : ℝ) / Fintype.card (Scramble m n) ≤
      (n.choose s : ℝ) * (Real.exp 1 * J * s / (n * T)) ^ T := by
  classical
  have htot : (0 : ℝ) < Fintype.card (Scramble m n) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (Scramble m n))
  have hsub : tailBadSet c R s T ⊆
      ((Finset.univ : Finset (Fin n)).powersetCard s).biUnion fun S =>
        Finset.univ.filter fun σ : Scramble m n => T ≤ (onesInRows c σ R S : ℝ) := by
    intro σ hσ
    simp only [tailBadSet, Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    obtain ⟨S, hS, hX⟩ := hσ
    exact Finset.mem_biUnion.mpr ⟨S, hS, by simp [hX]⟩
  have hcard_le : ((tailBadSet c R s T).card : ℝ) ≤
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard s,
        ((Finset.univ.filter fun σ : Scramble m n => T ≤ (onesInRows c σ R S : ℝ)).card : ℝ) := by
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_biUnion_le (s := (Finset.univ : Finset (Fin n)).powersetCard s)
      (t := fun S => Finset.univ.filter fun σ : Scramble m n => T ≤ (onesInRows c σ R S : ℝ))
    exact_mod_cast h1.trans h2
  have hper : ∀ S ∈ (Finset.univ : Finset (Fin n)).powersetCard s,
      ((Finset.univ.filter fun σ : Scramble m n => T ≤ (onesInRows c σ R S : ℝ)).card : ℝ) ≤
        (Real.exp 1 * J * s / (n * T)) ^ T * Fintype.card (Scramble m n) := by
    intro S hS
    have hcS : S.card = s := (Finset.mem_powersetCard.mp hS).2
    have := scramble_tail_fixed_set hn c R S J T hJ (by rw [hcS]; exact hs) hR
      (by rw [hcS]; exact hT)
      (Finset.univ.filter fun σ : Scramble m n => T ≤ (onesInRows c σ R S : ℝ))
      (fun σ hσ => (Finset.mem_filter.mp hσ).2)
    rw [hcS] at this
    exact (div_le_iff₀ htot).mp this
  rw [div_le_iff₀ htot]
  calc ((tailBadSet c R s T).card : ℝ)
      ≤ ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard s,
        (Real.exp 1 * J * s / (n * T)) ^ T * Fintype.card (Scramble m n) :=
        hcard_le.trans (Finset.sum_le_sum hper)
    _ = (n.choose s : ℝ) * (Real.exp 1 * J * s / (n * T)) ^ T *
          Fintype.card (Scramble m n) := by
        rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
        ring

/-- The rows strictly above the bottom `h` rows (the "top `m - h` rows"). -/
def topRows (m h : Nat) : Finset (Fin m) :=
  Finset.univ.filter fun r => r.val < m - h

/-- Ones in the top rows are at most all the ones of the matrix (`totalColumnOnes c`). -/
theorem sum_topRows_le_totalColumnOnes {m n : Nat} (c : MonotoneColumnSums m n) (h : Nat) :
    (∑ r ∈ topRows m h, ((monotoneRowOnes c r).card : ℝ)) ≤ (totalColumnOnes c : ℝ) := by
  have hsum : (totalColumnOnes c : ℝ) = ∑ r : Fin m, ((monotoneRowOnes c r).card : ℝ) := by
    exact_mod_cast totalColumnOnes_eq_sum_rowOnes c
  rw [hsum]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    fun _ _ _ => Nat.cast_nonneg _

/-- **S2, paper form.** For `j = totalColumnOnes c ≥ 1` ones, the top `m - h` rows
(`h = f/2`), and threshold `T ≥ j s / n`:
`p(s) ≤ C(n,s) (e j s / (n T))^T`. -/
theorem scramble_tail_union_top {m n : Nat} (hn : 0 < n)
    (c : MonotoneColumnSums m n) (h s : Nat) (T : ℝ)
    (hj : 0 < totalColumnOnes c) (hs : 0 < s)
    (hT : (totalColumnOnes c : ℝ) * s / n ≤ T) :
    ((tailBadSet c (topRows m h) s T).card : ℝ) / Fintype.card (Scramble m n) ≤
      (n.choose s : ℝ) *
        (Real.exp 1 * (totalColumnOnes c : ℝ) * s / (n * T)) ^ T :=
  scramble_tail_union hn c (topRows m h) s _ T (by exact_mod_cast hj) hs
    (sum_topRows_le_totalColumnOnes c h) hT

end Chvatal
