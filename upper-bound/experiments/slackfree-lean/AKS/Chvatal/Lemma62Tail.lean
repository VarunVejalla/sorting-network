module

public import AKS.Chvatal.Lemma63
public import AKS.Chvatal.Lemma62Ratio
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # Per-column-set tail estimate (Chvátal Lemma 6.2 (i), uses Lemma 6.3)

`scramble_tail_union_top`: for a monotone `c` with `j ≥ 1` ones, the fraction of scrambles putting at
least `T ≥ j s/n` ones of the top rows into some `s`-set of columns is at most
`C(n,s) (e j s/(n T))^T` (Poisson-type exponential moment, then Markov with `e^λ = T/μ`). -/

@[expose] public section

namespace Chvatal

/-- The rows strictly above the bottom `h` rows (the "top `m - h` rows"). -/
def topRows (m h : Nat) : Finset (Fin m) :=
  Finset.univ.filter fun r => r.val < m - h

def onesAboveHalfFringe {m n : Nat} (f : Nat) (c : MonotoneColumnSums m n) (σ : Scramble m n) (S : Finset (Fin n)) : Nat :=
  ∑ r ∈ topRows m (f / 2), rowHit c S r (σ r)

/-- Paper event `E` at `(c,j,S)` for a fixed scramble (Lemma 6.2). -/
def fringeColumnEventBad {m n : Nat} (f : Nat) (c : MonotoneColumnSums m n) (σ : Scramble m n) (j : Nat) (S : Finset (Fin n)) :
    Prop :=
  (f / 2 : ℝ) * S.card + eps * j ≤ (onesAboveHalfFringe f c σ S : ℝ)

/-- Corrected paper Property F. -/
def HasPaperPropertyF {m n : ℕ} (f : ℕ) (σ : Scramble m n) : Prop :=
  ∀ (c : MonotoneColumnSums m n) (j : ℕ), totalColumnOnes c = j → 0 < j →
    (j : ℝ) ≤ 128 / 4095 * (f * n) → ∀ S : Finset (Fin n), ¬ fringeColumnEventBad f c σ j S

theorem cast_half_of_even {f : ℕ} (hf : Even f) : ((f / 2 : ℕ) : ℝ) = (f : ℝ) / 2 := by
  obtain ⟨k, rfl⟩ := hf
  push_cast [show (k + k) / 2 = k by omega]; ring

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
  have hmarkov := scramble_markov (fun σ => (onesInRows c σ R S : ℝ)) bad lam T hlam0 hbad
  have hμ' : (∑ r ∈ R, ((monotoneRowOnes c r).card : ℝ)) / n * S.card ≤ μ := by
    rw [hμ, ← div_mul_eq_mul_div]
    gcongr
  have hel : 0 ≤ Real.exp lam - 1 := by linarith [Real.add_one_le_exp lam]
  have hmgf2 := (avg_exp_onesInRows_le hn c R S lam hlam0 (fun p => p * (Real.exp lam - 1))
    fun p h0 _ => by linarith [Real.add_one_le_exp (p * (Real.exp lam - 1))]).trans
    (Real.exp_le_exp.mpr (show _ ≤ (Real.exp lam - 1) * μ by
      rw [show ∑ r ∈ R, ((monotoneRowOnes c r).card : ℝ) / n * (Real.exp lam - 1) * S.card =
        (Real.exp lam - 1) * ((∑ r ∈ R, ((monotoneRowOnes c r).card : ℝ)) / n * S.card) by
        simp only [← Finset.sum_mul, ← Finset.sum_div]; ring]
      exact mul_le_mul_of_nonneg_left hμ' hel))
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
