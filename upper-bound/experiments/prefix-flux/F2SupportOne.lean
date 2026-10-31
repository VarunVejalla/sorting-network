import AKS.Sub800.Round2Det
import AKS.Misc.Fin

/-! A deterministic edge-provider lemma: if a sender has at most one
opposite-color key, any two-round row-scramble leaves fewer than two such
keys in every output region. This isolates the global invariant needed to
use a zero-probability local provider at an extreme boundary. -/

namespace Chvatal.RaggedF2SupportOne

open Chvatal

theorem sum_scrambledColSum_eq_total {m n : Nat}
    (c : MonotoneColumnSums m n) (σ : Scramble m n) :
    (∑ j : Fin n, scrambledColSum c σ j) = totalColumnOnes c := by
  rw [Round2.sum_scrambledColSum_eq c σ Finset.univ]
  have hwalk : ∀ j : Fin n,
      Round2.walkN σ Finset.univ j (c j).val = (c j).val := by
    intro j
    unfold Round2.walkN
    rw [show (Finset.univ.filter fun r : Fin m =>
        m - (c j).val ≤ r.val ∧ σ r j ∈ Finset.univ) =
        Finset.univ.filter fun r : Fin m => m - (c j).val ≤ r.val by
      ext r
      simp]
    have hc := (c j).isLt
    rw [card_filter_val_ge m (m - (c j).val) (by omega)]
    omega
  simp_rw [hwalk]
  rfl

theorem onesAboveBottom_le_total {m n : Nat}
    (c : MonotoneColumnSums m n) (σ : Scramble m n) (i : Nat) :
    onesAboveBottom c σ i ≤ totalColumnOnes c := by
  unfold onesAboveBottom
  calc
    (∑ j : Fin n, (scrambledColSum c σ j - i))
        ≤ ∑ j : Fin n, scrambledColSum c σ j := by
          apply Finset.sum_le_sum
          intro j hj
          exact Nat.sub_le _ _
    _ = totalColumnOnes c := sum_scrambledColSum_eq_total c σ

theorem two_round_escape_lt_two {m n : Nat}
    (c c1 : MonotoneColumnSums m n) (σ1 σ2 : Scramble m n) (i : Nat)
    (hc1 : ∀ col, (c1 col).val = scrambledColSum c σ1 col)
    (hMass : totalColumnOnes c ≤ 1) :
    onesAboveBottom c1 σ2 i < 2 := by
  have hMass1 : totalColumnOnes c1 = totalColumnOnes c := by
    unfold totalColumnOnes
    calc
      (∑ col : Fin n, (c1 col).val)
          = ∑ col : Fin n, scrambledColSum c σ1 col := by
              apply Finset.sum_congr rfl
              intro col hcol
              exact hc1 col
      _ = totalColumnOnes c := sum_scrambledColSum_eq_total c σ1
  have h := onesAboveBottom_le_total c1 σ2 i
  omega

end Chvatal.RaggedF2SupportOne
