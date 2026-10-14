import CyclicFixed16Provider
import TruncatedFringeProvider
import Mathlib.Tactic

namespace Tapered945
open Chvatal
open Classical

set_option maxHeartbeats 0

/-- Fixed-width replacement for the random bulk pair: at sixteen columns,
the cyclic first scramble supplies B2 from `2^30` rows, while the second
scramble simultaneously satisfies the truncated R2 condition in both flip
orientations. -/
theorem cyclic_truncated_fringe_pair_exists {m : Nat}
    (hm : 2^30 ≤ m + 1) (hretained : 131040 ≤ m) :
    ∃ σ₁ σ₂ : Scramble (m + 1) 16,
      (F2SmallRank F2Params.std (truncateBottomScramble σ₁) ∧
        F2R1 F2Params.std (truncateBottomScramble σ₁) ∧
        F2R2n F2Params.std (truncateBottomScramble σ₂) ∧
        HasPackSemanticPropertyB2 (by norm_num : 0 < 16)
          σ₁ σ₂ (1/2^21)) ∧
      (F2SmallRank F2Params.std (truncateBottomScramble (flipScramble σ₁)) ∧
        F2R1 F2Params.std (truncateBottomScramble (flipScramble σ₁)) ∧
        F2R2n F2Params.std (truncateBottomScramble (flipScramble σ₂)) ∧
        HasPackSemanticPropertyB2 (by norm_num : 0 < 16)
          (flipScramble σ₁) (flipScramble σ₂) (1/2^21)) := by
  let σ₁ : Scramble (m + 1) 16 := cyclicScramble16
  have hcap := cyclic_and_flip_FirstRoundCap16 (m := m + 1)
  have hfirst := exact_bulk_of_firstRoundCap16 hm σ₁ hcap.1
  have hfirstFlip := exact_bulk_of_firstRoundCap16 hm (flipScramble σ₁) hcap.2
  have hR2 := (truncated_F2_aux_fractions hretained (by norm_num : 16 ≤ 16)).2
  let Good : Scramble (m + 1) 16 → Prop := fun σ₂ =>
    ExactBulk σ₂ (IntermediateAdm (1/2^24)) (1/2^21) ∧
      F2R2n F2Params.std (truncateBottomScramble σ₂)
  have hfail := cyclic_card_fail_and_le
    (fun σ₂ : Scramble (m + 1) 16 =>
      ExactBulk σ₂ (IntermediateAdm (1/2^24)) (1/2^21))
    (fun σ₂ : Scramble (m + 1) 16 =>
      F2R2n F2Params.std (truncateBottomScramble σ₂))
    (cyclic_round2_fail_fraction hm) hR2
  have hfrac : (1/1000 : Real) + 1/10000 < 1/2 := by norm_num
  obtain ⟨σ₂, hGood, hGoodFlip⟩ := exists_and_flip Good hfrac (by
    simpa [Good] using hfail)
  have hSRR1 := any_scramble_SR_R1_16 (truncateBottomScramble σ₁)
  have hSRR1Flip := any_scramble_SR_R1_16
    (truncateBottomScramble (flipScramble σ₁))
  have hnormal :
      F2SmallRank F2Params.std (truncateBottomScramble σ₁) ∧
        F2R1 F2Params.std (truncateBottomScramble σ₁) ∧
        F2R2n F2Params.std (truncateBottomScramble σ₂) ∧
        HasPackSemanticPropertyB2 (by norm_num : 0 < 16)
          σ₁ σ₂ (1/2^21) := by
    exact ⟨hSRR1.1, hSRR1.2, hGood.2,
      semantic_B2_of_exact (by norm_num) hfirst hGood.1⟩
  have hflip :
      F2SmallRank F2Params.std (truncateBottomScramble (flipScramble σ₁)) ∧
        F2R1 F2Params.std (truncateBottomScramble (flipScramble σ₁)) ∧
        F2R2n F2Params.std (truncateBottomScramble (flipScramble σ₂)) ∧
        HasPackSemanticPropertyB2 (by norm_num : 0 < 16)
          (flipScramble σ₁) (flipScramble σ₂) (1/2^21) := by
    exact ⟨hSRR1Flip.1, hSRR1Flip.2, hGoodFlip.2,
      semantic_B2_of_exact (by norm_num) hfirstFlip hGoodFlip.1⟩
  exact ⟨σ₁, σ₂, hnormal, hflip⟩

end Tapered945
