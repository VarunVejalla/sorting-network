import TruncatedScrambleMeasure
import CandidateBulkProvider
import AKS.Chvatal.F2SR
import AKS.Chvatal.F2R1Fail
import AKS.Chvatal.F2R2Fail

namespace Tapered945

open Chvatal Classical

/-! Simultaneous bulk and padding-safe rare-rank witnesses. The bulk event is
on all rows; SR/R1/R2n are imposed on the retained prefix, whose failure
fractions are preserved exactly under truncation. -/

theorem truncated_F2_aux_fractions {m n : Nat} (hm : 131040 ≤ m) (hn : 16 ≤ n) :
    let PF₁ : Scramble (m + 1) n → Prop := fun σ =>
      F2SmallRank F2Params.std (truncateBottomScramble σ) ∧
        F2R1 F2Params.std (truncateBottomScramble σ)
    let PF₂ : Scramble (m + 1) n → Prop := fun σ =>
      F2R2n F2Params.std (truncateBottomScramble σ)
    ((Finset.univ.filter fun σ : Scramble (m + 1) n => ¬ PF₁ σ).card : Real) ≤
        (1/5000) * Fintype.card (Scramble (m + 1) n) ∧
      ((Finset.univ.filter fun σ : Scramble (m + 1) n => ¬ PF₂ σ).card : Real) ≤
        (1/10000) * Fintype.card (Scramble (m + 1) n) := by
  dsimp
  have hr : 131040 ≤ m := by omega
  have hrf : F2Params.std.f ≤ m := by norm_num [F2Params.std]; omega
  have hSR := F2SR_fail_card_le_std hn hrf
  have hR1 := F2R1_fail_std hn hr
  have hR2 := F2R2n_fail_std hn hr
  have hBoth := conjunction_fail_fraction
    (F2SmallRank F2Params.std) (F2R1 F2Params.std)
    (1/10000) (1/10000) hSR hR1
  have hBoth' : ((Finset.univ.filter fun σ : Scramble m n =>
      ¬ (F2SmallRank F2Params.std σ ∧ F2R1 F2Params.std σ)).card : Real) ≤
      (1/5000) * Fintype.card (Scramble m n) := by
    norm_num at hBoth ⊢
    exact hBoth
  have hLiftBoth := truncate_bad_fraction
    (fun σ : Scramble m n => F2SmallRank F2Params.std σ ∧ F2R1 F2Params.std σ)
    (1/5000) (by simpa using hBoth')
  have hLiftR2 := truncate_bad_fraction
    (F2R2n F2Params.std) (1/10000) hR2
  exact ⟨by simpa using hLiftBoth, by simpa using hLiftR2⟩

theorem truncated_fringe_bulk_pair_exists {m n : Nat}
    (hm : 2^34 ≤ m + 1) (hretained : 131040 ≤ m) (hn : 16 ≤ n) :
    ∃ σ₁ σ₂ : Scramble (m + 1) n,
      (F2SmallRank F2Params.std (truncateBottomScramble σ₁) ∧
        F2R1 F2Params.std (truncateBottomScramble σ₁) ∧
        F2R2n F2Params.std (truncateBottomScramble σ₂) ∧
        HasPackSemanticPropertyB2 (by omega : 0<n) σ₁ σ₂ (1/2^21)) ∧
      (F2SmallRank F2Params.std (truncateBottomScramble (flipScramble σ₁)) ∧
        F2R1 F2Params.std (truncateBottomScramble (flipScramble σ₁)) ∧
        F2R2n F2Params.std (truncateBottomScramble (flipScramble σ₂)) ∧
        HasPackSemanticPropertyB2 (by omega : 0<n)
          (flipScramble σ₁) (flipScramble σ₂) (1/2^21)) := by
  have hm0 : 0 < m + 1 := by omega
  have hPF := truncated_F2_aux_fractions hretained hn
  have hE := candidate_round_one_gap (m + 1) hm
  have hG := candidate_round_two_gap (m + 1) hm
  obtain ⟨σ₁, σ₂, hnormal, hflip⟩ := bulk_pair_with_two_aux_of_gaps
    (m := m + 1) hm0 hn (38/10^6) (1/2^21) (1/80) (1/5000) (1/10000)
    (by norm_num) (by norm_num) (by norm_num) hE hG
    (fun σ => F2SmallRank F2Params.std (truncateBottomScramble σ) ∧
      F2R1 F2Params.std (truncateBottomScramble σ))
    (fun σ => F2R2n F2Params.std (truncateBottomScramble σ))
    (by norm_num) (by norm_num) (by simpa using hPF.1) (by simpa using hPF.2)
  exact ⟨σ₁, σ₂,
    ⟨hnormal.1.1, hnormal.1.2, hnormal.2.1, hnormal.2.2⟩,
    ⟨hflip.1.1, hflip.1.2, hflip.2.1, hflip.2.2⟩⟩

end Tapered945
