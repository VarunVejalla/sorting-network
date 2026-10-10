import AKS.Chvatal.Bulk2Elem
open Finset

namespace Chvatal

/-- Bernstein-type tail for one `(c, S)` cell at exact mass. -/
theorem lemma63BernsteinBound {m n : Nat} (hn : 0 < n) (c : MonotoneColumnSums m n) (i : Nat)
    (hc : totalColumnOnes c = n * i) (S : Finset (Fin n)) (lam T : ℝ) (hl0 : 0 ≤ lam)
    (hl1 : lam ≤ 1) (bad : Finset (Scramble m n))
    (hbad : ∀ σ ∈ bad, (i : ℝ) * S.card + T ≤ (onesInColumns c σ S : ℝ)) :
    (bad.card : ℝ) ≤
      Real.exp (-lam * T + S.card * (lam ^ 2 * (1 / 2 + 2 * lam / 9)) *
        ∑ r : Fin m, (((monotoneRowOnes c r).card : ℝ) / n) * (1 - ((monotoneRowOnes c r).card : ℝ) / n)) *
        (Fintype.card (Scramble m n) : ℝ) := by
  classical
  set cl : ℝ := lam ^ 2 * (1 / 2 + 2 * lam / 9)
  set V : ℝ := ∑ r : Fin m, (((monotoneRowOnes c r).card : ℝ) / n) * (1 - ((monotoneRowOnes c r).card : ℝ) / n)
  have hmarkov := scramble_markov (fun σ => (onesInColumns c σ S : ℝ)) bad lam
    ((i : ℝ) * S.card + T) hl0 hbad
  have hmgf := avg_exp_onesInRows_le hn c Finset.univ S lam hl0
    (fun p => p * lam + cl * (p * (1 - p)))
    fun p h0 h1 => bernoulli_mgf_bernstein h0 h1 hl0 hl1
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hsumP : ∑ r : Fin m, ((monotoneRowOnes c r).card : ℝ) / n = i := by
    rw [← Finset.sum_div]
    have : (∑ r : Fin m, ((monotoneRowOnes c r).card : ℝ)) = n * i := by
      exact_mod_cast (totalColumnOnes_eq_sum_rowOnes c ▸ hc)
    rw [this]; field_simp
  have hexp : ∑ r : Fin m, (((monotoneRowOnes c r).card : ℝ) / n * lam +
      cl * (((monotoneRowOnes c r).card : ℝ) / n * (1 - ((monotoneRowOnes c r).card : ℝ) / n))) * S.card =
      S.card * (lam * i + cl * V) := by
    simp only [add_mul, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
    rw [hsumP]; simp only [V]
    ring
  have htotpos : (0 : ℝ) < Fintype.card (Scramble m n) := by exact_mod_cast Fintype.card_pos
  rw [hexp, div_le_iff₀ htotpos] at hmgf
  calc (bad.card : ℝ) ≤ _ := hmarkov
    _ ≤ Real.exp (-lam * ((i : ℝ) * S.card + T)) *
          (Real.exp (S.card * (lam * i + cl * V)) * (Fintype.card (Scramble m n) : ℝ)) :=
        mul_le_mul_of_nonneg_left hmgf (Real.exp_nonneg _)
    _ = _ := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring

end Chvatal
