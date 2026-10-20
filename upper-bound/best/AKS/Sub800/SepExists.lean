import AKS.Sub800.R1Cells
import AKS.Sub800.R2Cells
import AKS.Sub800.Fringe7934
import AKS.Sub800.Fringe406109
import AKS.Sub800.TruncatedScrambleMeasure
import AKS.Chvatal.F2Exists

/-! # Existence of the separator scrambles for the R1 sub-800 point

For a rectangle with `M = m + 1` rows, `50859009 ≤ M ≤ 2^26`, and `n ≥ 16` columns, and for each
fringe class `P ∈ {Fringe7934.P, Fringe406109.P}`: there are `σ1, σ2 : Scramble (m+1) n` with
two-round semantic Property B2 at `ε_B = 1/105000` (bulk, `R1Cells`/`R2Cells`) and the SR, R1, R2
witnesses of `P` on the bottom-truncated `m`-row scrambles (fringe), for the pair and for the
flipped pair. This is the hypothesis of the padded separator (`BaselineFringeD`,
`paddedPack2Net_all_cut_bounds`). -/

namespace Sub800

open Chvatal Tapered945 Classical

/-- Generic form: bulk numerics plus any fringe parameters with failure fractions `≤ 1/10000`. -/
theorem sep_pair_exists_of (P : F2PD)
    (hF : ∀ {m n : ℕ}, 16 ≤ n →
      ((Finset.univ.filter fun σ : Scramble m n => ¬ SRd P σ).card : ℝ) ≤
          (1 / 10000) * Fintype.card (Scramble m n) ∧
        ((Finset.univ.filter fun σ : Scramble m n => ¬ R1d P σ).card : ℝ) ≤
          (1 / 10000) * Fintype.card (Scramble m n) ∧
        ((Finset.univ.filter fun σ : Scramble m n => ¬ R2nd P σ).card : ℝ) ≤
          (1 / 10000) * Fintype.card (Scramble m n))
    {m n : ℕ} (hmlo : (50859009 : ℝ) ≤ ((m + 1 : ℕ) : ℝ)) (hmhi : m + 1 ≤ 2 ^ 26) (hn : 16 ≤ n) :
    ∃ σ1 σ2 : Scramble (m + 1) n,
      (SRd P (truncateBottomScramble σ1) ∧ R1d P (truncateBottomScramble σ1) ∧
        R2nd P (truncateBottomScramble σ2) ∧
        HasPackSemanticPropertyB2 (by omega : 0 < n) σ1 σ2 (1 / 105000)) ∧
      (SRd P (truncateBottomScramble (flipScramble σ1)) ∧
        R1d P (truncateBottomScramble (flipScramble σ1)) ∧
        R2nd P (truncateBottomScramble (flipScramble σ2)) ∧
        HasPackSemanticPropertyB2 (by omega : 0 < n) (flipScramble σ1) (flipScramble σ2)
          (1 / 105000)) := by
  obtain ⟨hSR, hR1, hR2⟩ := hF (m := m) hn
  have hB1 := R1Cells.round1_numeric (m := m + 1) (n := n) hn hmlo (by omega)
  have hB2 := R2Cells.round2_numeric (m := m + 1) (n := n) hn hmlo hmhi (by omega)
  -- fringe on the truncated prefix
  have hPF1 := card_fail_and_le (fun σ : Scramble m n => SRd P σ) (fun σ => R1d P σ) hSR hR1
  have hPF1' := truncate_bad_fraction (fun σ : Scramble m n => SRd P σ ∧ R1d P σ) (1 / 10000 + 1 / 10000)
    (by convert hPF1 using 2; congr 1; ext σ; simp)
  have hPF2' := truncate_bad_fraction (fun σ : Scramble m n => R2nd P σ) _ hR2
  have hfail1 := card_fail_and_le
    (fun σ : Scramble (m + 1) n => HasCombinatorialPropertyBOnPipeline σ (18421 / 50000000))
    (fun σ => SRd P (truncateBottomScramble σ) ∧ R1d P (truncateBottomScramble σ)) hB1 hPF1'
  have hfail2 := card_fail_and_le
    (fun σ : Scramble (m + 1) n => HasCombinatorialPropertyB2 σ (18421 / 50000000) (1 / 105000))
    (fun σ => R2nd P (truncateBottomScramble σ)) hB2 hPF2'
  obtain ⟨σ1, h1, h1'⟩ := exists_and_flip (m := m + 1) (n := n)
    (fun σ => HasCombinatorialPropertyBOnPipeline σ (18421 / 50000000) ∧
      (SRd P (truncateBottomScramble σ) ∧ R1d P (truncateBottomScramble σ)))
    (c := 1 / 100 + (1 / 10000 + 1 / 10000)) (by norm_num)
    (by convert hfail1 using 2; congr 1; ext σ; simp)
  obtain ⟨σ2, h2, h2'⟩ := exists_and_flip (m := m + 1) (n := n)
    (fun σ => HasCombinatorialPropertyB2 σ (18421 / 50000000) (1 / 105000) ∧
      R2nd P (truncateBottomScramble σ))
    (c := 1 / 1000 + 1 / 10000) (by norm_num)
    (by convert hfail2 using 2; congr 1; ext σ; simp)
  exact ⟨σ1, σ2,
    ⟨h1.2.1, h1.2.2, h2.2, HasPackSemanticPropertyB2.of_combinatorial _ h1.1 h2.1⟩,
    ⟨h1'.2.1, h1'.2.2, h2'.2, HasPackSemanticPropertyB2.of_combinatorial _ h1'.1 h2'.1⟩⟩

end Sub800
