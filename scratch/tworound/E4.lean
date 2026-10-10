import AKS.Chvatal.Bulk2Elem
import AKS.Chvatal.Lemma63
import AKS.Chvatal.Bulk2Elem
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
