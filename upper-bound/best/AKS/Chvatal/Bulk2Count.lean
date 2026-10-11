module

/- Two-round bulk lemma (B2): the round-2 combinatorial predicate, the per-cell Bernstein tail
at exact mass, and the union bound over `(c, S)`. -/

public import AKS.Chvatal.Bulk2Elem
public import AKS.Chvatal.Lemma63

@[expose] public section

open Finset

namespace Chvatal

/-- Round-2 combinatorial Property B2: exact mass `n·i`, small excess above `i` in the
intermediate matrix, gives small excess above `i` after the second scramble. -/
def HasCombinatorialPropertyB2 {m n : Nat} (σ2 : Scramble m n) (E1 d : ℝ) : Prop :=
  ∀ (c : MonotoneColumnSums m n) (i : Nat), totalColumnOnes c = n * i → 1 ≤ i → i ≤ m →
    (excessAbove c i : ℝ) < (E1 / 2) * (m * n) →
      (onesAboveBottom c σ2 i : ℝ) < (d / 2) * (m * n)

end Chvatal
namespace Chvatal

theorem variance_le_of_excess {m n : Nat} (hn : 0 < n) (c : MonotoneColumnSums m n) (i : Nat)
    (hc : totalColumnOnes c = n * i) :
    ∑ r : Fin m, (((monotoneRowOnes c r).card : ℝ) / n) * (1 - ((monotoneRowOnes c r).card : ℝ) / n)
      ≤ 2 * (excessAbove c i : ℝ) / n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h := sum_rowOnes_mul_compl_le c i hc
  have hle : ∀ r : Fin m, (monotoneRowOnes c r).card ≤ n := fun r => by
    simpa [Fintype.card_fin] using (monotoneRowOnes c r).card_le_univ
  have h' : ∑ r : Fin m, ((monotoneRowOnes c r).card : ℝ) * (n - (monotoneRowOnes c r).card) ≤
      2 * n * (excessAbove c i : ℝ) := by
    have := (Nat.cast_le (α := ℝ)).2 h
    push_cast [Nat.cast_sub (hle _)] at this
    simpa using this
  have e : ∑ r : Fin m, (((monotoneRowOnes c r).card : ℝ) / n) * (1 - ((monotoneRowOnes c r).card : ℝ) / n)
      = (∑ r : Fin m, ((monotoneRowOnes c r).card : ℝ) * (n - (monotoneRowOnes c r).card)) / n ^ 2 := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun r _ => ?_
    field_simp
  rw [e, div_le_iff₀ (by positivity)]
  have : 2 * (excessAbove c i : ℝ) / n * n ^ 2 = 2 * n * (excessAbove c i : ℝ) := by
    field_simp
  rw [this]; exact h'

end Chvatal

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
