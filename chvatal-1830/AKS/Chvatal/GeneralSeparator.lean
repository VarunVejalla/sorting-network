module

/-
  # Thm 5.1 separators for every geometry `m ≥ 100`, `n ≥ 16`, `f ≥ 1.7·10^10`

  Combines the pipeline Property B failure bound (`lemma61_failFactor < 1/100`) with the
  corrected paper Property F failure bound (`≤ 0.44`, `Lemma62Round` + `Lemma62FailE`) by
  pigeonhole, and the corrected F-bridge (`Lemma62Bridge`) to the canonical
  sort–scramble–sort pack. This replaces the `δ_F n < 1` shortcut (valid only for `n ≤ 31`).
-/

public import AKS.Chvatal.Lemma62FailE
public import AKS.Chvatal.Lemma62Round
public import AKS.Chvatal.Lemma62Bridge

@[expose] public section

namespace Chvatal

open Classical in
/-- The corrected paper Property F fails for at most `44%` of the scrambles. -/
theorem paperF_fail_fraction_final {m n f : ℕ} (hf : Even f) (hfm : f ≤ m)
    (hfbig : 17 * 10 ^ 9 ≤ f) (hn : 16 ≤ n) :
    (((Finset.univ.filter fun σ : Scramble m n =>
        ¬ HasPaperPropertyF hf σ (128 / 4095) eps).card : ℝ) ≤
      44 / 100 * (Fintype.card (Scramble m n) : ℝ)) :=
  paperF_fail_fraction hf hfm hfbig hn
    (fun j E hE1 hE P => fail_prob_at_E hf (128 / 4095) j E hE1 hE P)

/-- Semantic Property F is monotone in `δ_F` (down) and `ε_F` (up). -/
theorem HasPackSemanticPropertyF.mono {m n f : ℕ} (hn : 0 < n) {σ : Scramble m n}
    (pack : SortScrambleSortPack m n hn σ) (hfm : f ≤ m) {δ δ' ε ε' : ℝ}
    (hδ : δ' ≤ δ) (hε : ε ≤ ε') (h : HasPackSemanticPropertyF hn pack f hfm δ ε) :
    HasPackSemanticPropertyF hn pack f hfm δ' ε' := by
  unfold HasPackSemanticPropertyF at h ⊢
  intro v j hj hjδ
  have hfn : (0 : ℝ) ≤ (f : ℝ) * n := by positivity
  have hjδ0 : (j : ℝ) ≤ δ * (f * n) :=
    le_trans hjδ (mul_le_mul_of_nonneg_right hδ hfn)
  have h1 := h v j hj hjδ0
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  calc _ < ε * j := h1
    _ ≤ ε' * j := mul_le_mul_of_nonneg_right hε hj0

end Chvatal
