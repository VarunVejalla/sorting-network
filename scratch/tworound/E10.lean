import AKS.Chvatal.Bulk2Fail
import AKS.Chvatal.Bulk2Bridge
import AKS.Chvatal.FlipSpec
open Finset

namespace Chvatal

open Classical in
/-- Round-1 pipeline Property B at `E1 = 371/10^8` together with an abstract predicate `PF` of
failure fraction at most `483/1000` (the F share) fails on at most `493/1000` of the scrambles. -/
theorem round1_and_PF_fail_fraction {m n : ℕ} (hm : 2 ^ 42 ≤ m) (hn : 16 ≤ n)
    (PF : Scramble m n → Prop)
    (hPF : ((Finset.univ.filter fun σ : Scramble m n => ¬ PF σ).card : ℝ) ≤
      483 / 1000 * (Fintype.card (Scramble m n) : ℝ)) :
    ((Finset.univ.filter fun σ : Scramble m n =>
        ¬ (HasCombinatorialPropertyBOnPipeline σ (371 / 10 ^ 8) ∧ PF σ)).card : ℝ) ≤
      (1 / 100 + 483 / 1000) * (Fintype.card (Scramble m n) : ℝ) := by
  have hm100 : 100 ≤ m := le_trans (by norm_num) hm
  have hB := lemma61FailBound_onPipeline (m := m) (n := n) (371 / 10 ^ 8) (by omega) (by omega)
    (epsB1_le hm)
  have hfac := lemma61_failFactor_lt_one_hundredth m n hm100 hn
  simp only [not_and_or, Finset.filter_or]
  have h3 := (Nat.cast_le (α := ℝ)).2 (Finset.card_union_le
    (Finset.univ.filter fun σ : Scramble m n => ¬ HasCombinatorialPropertyBOnPipeline σ (371 / 10 ^ 8))
    (Finset.univ.filter fun σ : Scramble m n => ¬ PF σ))
  have h4 : lemma61_failFactor m n * (Fintype.card (Scramble m n) : ℝ) ≤
      1 / 100 * Fintype.card (Scramble m n) := by gcongr
  push_cast at h3
  linarith

open Classical in
/-- **T3 (two-sided two-round existence, abstract F share).** For `m ≥ 2^42`, `n ≥ 16`, and any
predicate `PF` on first-round scrambles failing on at most a `483/1000` fraction, there are
`σ1, σ2` such that `PF` and two-round semantic Property B2 (at `d = 1/59000000`) hold for
`(σ1, σ2)` and for `(flipScramble σ1, flipScramble σ2)`. -/
theorem ExistsScrambleSeparator_twoSided_B2 {m n : ℕ} (hm : 2 ^ 42 ≤ m) (hn : 16 ≤ n)
    (PF : Scramble m n → Prop)
    (hPF : ((Finset.univ.filter fun σ : Scramble m n => ¬ PF σ).card : ℝ) ≤
      483 / 1000 * (Fintype.card (Scramble m n) : ℝ)) :
    ∃ σ1 σ2 : Scramble m n,
      (PF σ1 ∧ HasPackSemanticPropertyB2 (lt_of_lt_of_le (by norm_num) hn) σ1 σ2 (1 / 59000000)) ∧
      (PF (flipScramble σ1) ∧
        HasPackSemanticPropertyB2 (lt_of_lt_of_le (by norm_num) hn)
          (flipScramble σ1) (flipScramble σ2) (1 / 59000000)) := by
  have hfail := round1_and_PF_fail_fraction hm hn PF hPF
  obtain ⟨σ1, h1, h1'⟩ := exists_and_flip (m := m) (n := n)
    (fun σ => HasCombinatorialPropertyBOnPipeline σ (371 / 10 ^ 8) ∧ PF σ)
    (c := 1 / 100 + 483 / 1000) (by norm_num) (by convert hfail using 2; congr 1; ext σ; simp)
  obtain ⟨σ2, h2, h2'⟩ := exists_and_flip (m := m) (n := n)
    (fun σ => HasCombinatorialPropertyB2 σ (371 / 10 ^ 8) (1 / 59000000))
    (c := 1 / 1000) (by norm_num) (bulk2_fail_fraction_le hm hn)
  exact ⟨σ1, σ2, ⟨h1.2, HasPackSemanticPropertyB2.of_combinatorial _ h1.1 h2⟩,
    ⟨h1'.2, HasPackSemanticPropertyB2.of_combinatorial _ h1'.1 h2'⟩⟩


open Classical in
/-- Concrete two-round, two-sided separator existence: two-round Properties B2 and F2 for
`(σ1, σ2)` and for the flipped pair, on a scramble geometry with `m ≥ 2^42`. -/
theorem ExistsScrambleSeparator_twoSided_two {g : ScrambleGeometry} (hfbig : 85 * 10 ^ 8 ≤ g.f)
    (hm : 2 ^ 42 ≤ g.m) {deltaF epsF : ℝ} (hδ : deltaF ≤ 128 / 4095) (hε : eps ≤ epsF) :
    ∃ σ1 σ2 : Scramble g.m g.n,
      (HasPackSemanticPropertyB2 (scrambleGeometry_hn g) σ1 σ2 (1 / 59000000) ∧
        HasPackSemanticPropertyF2 (scrambleGeometry_hn g) σ1 σ2 g.f
          (scrambleGeometry_f_le_m g) deltaF epsF) ∧
      (HasPackSemanticPropertyB2 (scrambleGeometry_hn g) (flipScramble σ1) (flipScramble σ2)
          (1 / 59000000) ∧
        HasPackSemanticPropertyF2 (scrambleGeometry_hn g) (flipScramble σ1) (flipScramble σ2)
          g.f (scrambleGeometry_f_le_m g) deltaF epsF) := by
  have hn := scrambleGeometry_hn g
  obtain ⟨σ1, σ2, ⟨hF1, hB1⟩, ⟨hF2, hB2⟩⟩ := ExistsScrambleSeparator_twoSided_B2 (m := g.m)
    (n := g.n) hm g.hn (HasPaperPropertyF g.f)
    (paperF_fail_fraction g.hfeven (scrambleGeometry_f_le_m g) hfbig g.hn)
  exact ⟨σ1, σ2,
    ⟨hB1, HasPackSemanticPropertyF2.of_F hn σ2
      ((HasPackSemanticPropertyF.of_paperF g.hfeven hn (scrambleGeometry_f_le_m g) hF1).mono hn
        (scrambleGeometry_f_le_m g) hδ hε)⟩,
    ⟨hB2, HasPackSemanticPropertyF2.of_F hn (flipScramble σ2)
      ((HasPackSemanticPropertyF.of_paperF g.hfeven hn (scrambleGeometry_f_le_m g) hF2).mono hn
        (scrambleGeometry_f_le_m g) hδ hε)⟩⟩

end Chvatal
