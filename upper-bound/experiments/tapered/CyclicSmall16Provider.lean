import CyclicSmallF2Params
import CyclicBulkRate
import CyclicFixed16Provider
import TruncatedScrambleMeasure
import AKS.Chvatal.F2Det
import AKS.Chvatal.FlipSpec
import Mathlib.Tactic

namespace Tapered945
open Chvatal
open Classical

set_option maxHeartbeats 0

/-- The cyclic first scramble has a two-sided B2 partner at the smaller row
floor; no probabilistic R2 restriction is needed for these tuned parameters. -/
theorem cyclicSmall16_B2_pair_exists {m : Nat} (hm : 2^30 ≤ m) :
    ∃ σ₂ : Scramble m 16,
      HasPackSemanticPropertyB2 (by norm_num : 0 < 16)
        (cyclicScramble16 (m := m)) σ₂ (1/2^21) ∧
      HasPackSemanticPropertyB2 (by norm_num : 0 < 16)
        (flipScramble (cyclicScramble16 (m := m))) (flipScramble σ₂) (1/2^21) := by
  have hcap := cyclic_and_flip_FirstRoundCap16 (m := m)
  have hfirst := exact_bulk_of_firstRoundCap16 hm (cyclicScramble16 (m := m)) hcap.1
  have hfirstFlip := exact_bulk_of_firstRoundCap16 hm
    (flipScramble (cyclicScramble16 (m := m))) hcap.2
  obtain ⟨σ₂, hsecond, hsecondFlip⟩ := exists_and_flip
    (fun σ : Scramble m 16 =>
      ExactBulk σ (IntermediateAdm (1/2^24)) (1/2^21))
    (c := 1/1000) (by norm_num) (cyclic_round2_fail_fraction hm)
  exact ⟨σ₂, semantic_B2_of_exact (by norm_num) hfirst hsecond,
    semantic_B2_of_exact (by norm_num) hfirstFlip hsecondFlip⟩

/-- The selected B2 pair also gives the two-sided F2 contract with the tuned
width-16 parameters: SR/R1 are deterministic and R2n is vacuous. -/
theorem cyclicSmall16_B2_F2_pair {m : Nat}
    (σ₂ : Scramble m 16) :
    (F2SmallRank cyclicSmall16Params (cyclicScramble16 (m := m)) ∧
      F2R1 cyclicSmall16Params (cyclicScramble16 (m := m)) ∧
      F2R2n cyclicSmall16Params σ₂) ∧
    (F2SmallRank cyclicSmall16Params (flipScramble (cyclicScramble16 (m := m))) ∧
      F2R1 cyclicSmall16Params (flipScramble (cyclicScramble16 (m := m))) ∧
      F2R2n cyclicSmall16Params (flipScramble σ₂)) := by
  have h1 := any_scramble_small16_F2Inputs (cyclicScramble16 (m := m))
  have h1f := any_scramble_small16_F2Inputs
    (flipScramble (cyclicScramble16 (m := m)))
  have h2 := any_scramble_small16_R2n σ₂
  have h2f := any_scramble_small16_R2n (flipScramble σ₂)
  exact ⟨⟨h1.1, h1.2.1, h2⟩, ⟨h1f.1, h1f.2.1, h2f⟩⟩

/-- One simultaneous fixed-width pair supplies B2 and tuned F2 in both
orientations. The F2 rank-tail coefficient is `1/9,000,000`. -/
theorem cyclicSmall16_pair_exists {m : Nat} (hm : 2^30 ≤ m) :
    ∃ σ₂ : Scramble m 16,
      (HasPackSemanticPropertyB2 (by norm_num : 0 < 16)
        (cyclicScramble16 (m := m)) σ₂ (1/2^21) ∧
       HasPackSemanticPropertyB2 (by norm_num : 0 < 16)
        (flipScramble (cyclicScramble16 (m := m))) (flipScramble σ₂) (1/2^21)) ∧
      (HasPackSemanticPropertyF2 (by norm_num : 0 < 16)
        (cyclicScramble16 (m := m)) σ₂ 16000 (by omega) (128/4095)
        (1/(cyclicSmall16Params.J : Real)) ∧
       HasPackSemanticPropertyF2 (by norm_num : 0 < 16)
        (flipScramble (cyclicScramble16 (m := m))) (flipScramble σ₂)
        16000 (by omega) (128/4095)
        (1/(cyclicSmall16Params.J : Real))) := by
  obtain ⟨σ₂, hB⟩ := cyclicSmall16_B2_pair_exists hm
  have hF := F2_both_orientations cyclicSmall16Params (by norm_num)
    (by norm_num [cyclicSmall16Params]; omega)
    (cyclicSmall16_B2_F2_pair σ₂).1
    (cyclicSmall16_B2_F2_pair σ₂).2
  have hf : cyclicSmall16Params.f = 16000 := by
    norm_num [cyclicSmall16Params]
  refine ⟨σ₂, ?_⟩
  refine ⟨?_, hF⟩
  exact hB

/-- Truncating the bottom row preserves the deterministic tuned F2 inputs;
the same full-row pair continues to satisfy B2. -/
theorem cyclicSmall16_truncated_fringe_pair_exists {m : Nat}
    (hm : 2^30 ≤ m + 1) :
    ∃ σ₁ σ₂ : Scramble (m + 1) 16,
      (F2SmallRank cyclicSmall16Params (truncateBottomScramble σ₁) ∧
        F2R1 cyclicSmall16Params (truncateBottomScramble σ₁) ∧
        F2R2n cyclicSmall16Params (truncateBottomScramble σ₂) ∧
        HasPackSemanticPropertyB2 (by norm_num : 0 < 16)
          σ₁ σ₂ (1/2^21)) ∧
      (F2SmallRank cyclicSmall16Params
          (truncateBottomScramble (flipScramble σ₁)) ∧
        F2R1 cyclicSmall16Params
          (truncateBottomScramble (flipScramble σ₁)) ∧
        F2R2n cyclicSmall16Params
          (truncateBottomScramble (flipScramble σ₂)) ∧
        HasPackSemanticPropertyB2 (by norm_num : 0 < 16)
          (flipScramble σ₁) (flipScramble σ₂) (1/2^21)) := by
  obtain ⟨σ₂, hpair⟩ := cyclicSmall16_pair_exists hm
  have hB := hpair.1.1
  have hBflip := hpair.1.2
  let σ₁ : Scramble (m + 1) 16 := cyclicScramble16 (m := m + 1)
  have h1 := any_scramble_small16_F2Inputs (truncateBottomScramble σ₁)
  have h1f := any_scramble_small16_F2Inputs
    (truncateBottomScramble (flipScramble σ₁))
  exact ⟨σ₁, σ₂,
    ⟨h1.1, h1.2.1, any_scramble_small16_R2n _, hB⟩,
    ⟨h1f.1, h1f.2.1, any_scramble_small16_R2n _, hBflip⟩⟩

end Tapered945
