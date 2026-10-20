import AKS.Sub800.F2D
import AKS.Sub800.TruncatedScrambleMeasure
import AKS.Chvatal.F2Exists

/-! # Existence of the separator scrambles (generic in the bulk and fringe certificates)

`BulkCert`: the walk-bound bulk at `(E1, ε_B)` on rectangles with `Mlo ≤ M ≤ 2^q` rows and `n ≥ 16`
columns (round 1 fails on at most 1/100 of the scrambles, round 2 on at most 1/1000).
`FringeCert`: fringe parameters `P` whose SR, R1 and R2 witnesses each fail on at most 1/10000 of
the scrambles, for every shape with `n ≥ 16`.

`sep_pair_exists_of`: for `M = m + 1` rows in the window, there are `σ1, σ2 : Scramble (m+1) n` with
two-round semantic Property B2 at `ε_B` and the witnesses of `P` on the bottom-truncated `m`-row
scrambles, for the pair and for the flipped pair. This is the hypothesis of the padded separator
(`BaselineFringeD`, `paddedPack2Net_all_cut_bounds`). The concrete certificates are
`R1Cells`/`R2Cells` (bulk) and `Fringe7934`/`Fringe406109` (fringe). -/

namespace Sub800

open Chvatal Tapered945 Classical

/-- Bulk certificates on the row window `[Mlo, 2^q]`. -/
structure BulkCert where
  E1 : ℝ
  epsB : ℝ
  Mlo : ℕ
  q : ℕ
  r1 : ∀ {m n : ℕ}, 16 ≤ n → (Mlo : ℝ) ≤ m → 0 < m →
    ((Finset.univ.filter fun σ : Scramble m n => ¬ HasCombinatorialPropertyBOnPipeline σ E1).card : ℝ) ≤
      (1 / 100 : ℝ) * ((Fintype.card (Scramble m n) : ℕ) : ℝ)
  r2 : ∀ {m n : ℕ}, 16 ≤ n → (Mlo : ℝ) ≤ m → m ≤ 2 ^ q → 0 < m →
    ((Finset.univ.filter fun σ : Scramble m n => ¬ HasCombinatorialPropertyB2 σ E1 epsB).card : ℝ) ≤
      (1 / 1000 : ℝ) * ((Fintype.card (Scramble m n) : ℕ) : ℝ)

/-- Fringe certificates for the parameters `P`. -/
structure FringeCert where
  P : F2PD
  fail : ∀ {m n : ℕ}, 16 ≤ n →
    ((Finset.univ.filter fun σ : Scramble m n => ¬ SRd P σ).card : ℝ) ≤
        (1 / 10000) * Fintype.card (Scramble m n) ∧
      ((Finset.univ.filter fun σ : Scramble m n => ¬ R1d P σ).card : ℝ) ≤
        (1 / 10000) * Fintype.card (Scramble m n) ∧
      ((Finset.univ.filter fun σ : Scramble m n => ¬ R2nd P σ).card : ℝ) ≤
        (1 / 10000) * Fintype.card (Scramble m n)

/-- **The separator pair** for a bulk certificate and fringe parameters. -/
theorem sep_pair_exists_of (B : BulkCert) (F : FringeCert)
    {m n : ℕ} (hmlo : (B.Mlo : ℝ) ≤ ((m + 1 : ℕ) : ℝ)) (hmhi : m + 1 ≤ 2 ^ B.q) (hn : 16 ≤ n) :
    ∃ σ1 σ2 : Scramble (m + 1) n,
      (SRd F.P (truncateBottomScramble σ1) ∧ R1d F.P (truncateBottomScramble σ1) ∧
        R2nd F.P (truncateBottomScramble σ2) ∧
        HasPackSemanticPropertyB2 (by omega : 0 < n) σ1 σ2 B.epsB) ∧
      (SRd F.P (truncateBottomScramble (flipScramble σ1)) ∧
        R1d F.P (truncateBottomScramble (flipScramble σ1)) ∧
        R2nd F.P (truncateBottomScramble (flipScramble σ2)) ∧
        HasPackSemanticPropertyB2 (by omega : 0 < n) (flipScramble σ1) (flipScramble σ2)
          B.epsB) := by
  obtain ⟨hSR, hR1, hR2⟩ := F.fail (m := m) hn
  have hB1 := B.r1 (m := m + 1) (n := n) hn hmlo (by omega)
  have hB2 := B.r2 (m := m + 1) (n := n) hn hmlo hmhi (by omega)
  -- fringe on the truncated prefix
  have hPF1 := card_fail_and_le (fun σ : Scramble m n => SRd F.P σ) (fun σ => R1d F.P σ) hSR hR1
  have hPF1' := truncate_bad_fraction (fun σ : Scramble m n => SRd F.P σ ∧ R1d F.P σ)
    (1 / 10000 + 1 / 10000) (by convert hPF1 using 2; congr 1; ext σ; simp)
  have hPF2' := truncate_bad_fraction (fun σ : Scramble m n => R2nd F.P σ) _ hR2
  have hfail1 := card_fail_and_le
    (fun σ : Scramble (m + 1) n => HasCombinatorialPropertyBOnPipeline σ B.E1)
    (fun σ => SRd F.P (truncateBottomScramble σ) ∧ R1d F.P (truncateBottomScramble σ)) hB1 hPF1'
  have hfail2 := card_fail_and_le
    (fun σ : Scramble (m + 1) n => HasCombinatorialPropertyB2 σ B.E1 B.epsB)
    (fun σ => R2nd F.P (truncateBottomScramble σ)) hB2 hPF2'
  obtain ⟨σ1, h1, h1'⟩ := exists_and_flip (m := m + 1) (n := n)
    (fun σ => HasCombinatorialPropertyBOnPipeline σ B.E1 ∧
      (SRd F.P (truncateBottomScramble σ) ∧ R1d F.P (truncateBottomScramble σ)))
    (c := 1 / 100 + (1 / 10000 + 1 / 10000)) (by norm_num)
    (by convert hfail1 using 2; congr 1; ext σ; simp)
  obtain ⟨σ2, h2, h2'⟩ := exists_and_flip (m := m + 1) (n := n)
    (fun σ => HasCombinatorialPropertyB2 σ B.E1 B.epsB ∧ R2nd F.P (truncateBottomScramble σ))
    (c := 1 / 1000 + 1 / 10000) (by norm_num)
    (by convert hfail2 using 2; congr 1; ext σ; simp)
  exact ⟨σ1, σ2,
    ⟨h1.2.1, h1.2.2, h2.2, HasPackSemanticPropertyB2.of_combinatorial _ h1.1 h2.1⟩,
    ⟨h1'.2.1, h1'.2.2, h2'.2, HasPackSemanticPropertyB2.of_combinatorial _ h1'.1 h2'.1⟩⟩

end Sub800
