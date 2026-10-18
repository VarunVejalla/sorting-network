import CyclicBulkRate
import CyclicFixed16SRR1
import CyclicFlipBridge
import AKS.Chvatal.F2Det
import AKS.Chvatal.F2R2Fail
import AKS.Chvatal.FlipSpec
import Mathlib.Tactic

namespace Tapered945
open Chvatal
open Classical

set_option maxHeartbeats 0

/-- A union bound for two failure sets in a finite scramble space. -/
theorem cyclic_card_fail_and_le {α : Type*} [Fintype α]
    (A B : α → Prop) {a b : Real}
    (hA : ((Finset.univ.filter fun x => ¬ A x).card : Real) ≤
      a * Fintype.card α)
    (hB : ((Finset.univ.filter fun x => ¬ B x).card : Real) ≤
      b * Fintype.card α) :
    ((Finset.univ.filter fun x => ¬ (A x ∧ B x)).card : Real) ≤
      (a+b) * Fintype.card α := by
  have hsubset : (Finset.univ.filter fun x => ¬ (A x ∧ B x)) ⊆
      (Finset.univ.filter fun x => ¬ A x) ∪ (Finset.univ.filter fun x => ¬ B x) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union] at hx ⊢
    tauto
  have hcard := (Nat.cast_le (α := Real)).2
    ((Finset.card_le_card hsubset).trans (Finset.card_union_le _ _))
  push_cast at hcard
  linarith

/-- Both deterministic first-round predicates hold for the fixed cyclic map
and for its actual repository flip. -/
theorem cyclic_and_flip_SR_R1_16 {m : Nat} :
    (F2SmallRank F2Params.std (cyclicScramble16 (m := m)) ∧
      F2R1 F2Params.std (cyclicScramble16 (m := m))) ∧
    (F2SmallRank F2Params.std (flipScramble (cyclicScramble16 (m := m))) ∧
      F2R1 F2Params.std (flipScramble (cyclicScramble16 (m := m)))) := by
  exact ⟨any_scramble_SR_R1_16 (cyclicScramble16 (m := m)),
    any_scramble_SR_R1_16 (flipScramble (cyclicScramble16 (m := m)))⟩

/-- The cyclic and flipped cyclic maps satisfy the exact-mass contract at
width 16. This is the cyclic residue-count cap specialized to the provider. -/
theorem cyclic_and_flip_FirstRoundCap16 {m : Nat} :
    FirstRoundCap16 (cyclicScramble16 (m := m)) ∧
      FirstRoundCap16 (flipScramble (cyclicScramble16 (m := m))) := by
  constructor
  · intro c i hmass hi j
    exact cyclicScramble16_firstRoundCap c i hmass hi j
  · intro c i hmass hi j
    exact repositoryFlipCyclic16_firstRoundCap c i hmass hi j

/-- At width 16 and rows `m ≥ 2^30`, the cyclic first scramble admits one
second scramble giving the improved semantic B2 bound and the standard F2
contract, simultaneously in both flip orientations.

The B2 error is `2^-21`; the F2 parameters are the repository's standard
`f=131040` parameters. -/
theorem cyclic_fixed16_B2_and_F2 {m : Nat} (hm : 2^30 ≤ m) :
    ∃ σ₂ : Scramble m 16,
      (HasPackSemanticPropertyB2 (by norm_num : 0 < 16)
          (cyclicScramble16 (m := m)) σ₂ (1/2^21) ∧
        HasPackSemanticPropertyB2 (by norm_num : 0 < 16)
          (flipScramble (cyclicScramble16 (m := m))) (flipScramble σ₂) (1/2^21)) ∧
      (HasPackSemanticPropertyF2 (by norm_num : 0 < 16)
          (cyclicScramble16 (m := m)) σ₂ 131040 (by omega) (128/4095) eps ∧
        HasPackSemanticPropertyF2 (by norm_num : 0 < 16)
          (flipScramble (cyclicScramble16 (m := m))) (flipScramble σ₂)
          131040 (by omega) (128/4095) eps) := by
  let Good : Scramble m 16 → Prop := fun σ₂ =>
    ExactBulk σ₂ (IntermediateAdm (1/2^24)) (1/2^21) ∧
      F2R2n F2Params.std σ₂
  have hR2 : ((Finset.univ.filter fun σ₂ : Scramble m 16 =>
      ¬ F2R2n F2Params.std σ₂).card : Real) ≤
        (1/10000) * Fintype.card (Scramble m 16) := by
    apply F2R2n_fail_std (by norm_num)
    have hm0 : 131040 ≤ 2^30 := by norm_num
    exact hm0.trans hm
  have hfail := cyclic_card_fail_and_le
    (fun σ₂ : Scramble m 16 =>
      ExactBulk σ₂ (IntermediateAdm (1/2^24)) (1/2^21))
    (fun σ₂ : Scramble m 16 => F2R2n F2Params.std σ₂)
    (cyclic_round2_fail_fraction hm) hR2
  have hfrac : (1/1000 : Real) + 1/10000 < 1/2 := by norm_num
  obtain ⟨σ₂, hGood, hGoodFlip⟩ := exists_and_flip Good hfrac (by
    simpa [Good] using hfail)
  have hcaps := cyclic_and_flip_FirstRoundCap16 (m := m)
  have hfirst := exact_bulk_of_firstRoundCap16 hm (cyclicScramble16 (m := m)) hcaps.1
  have hfirstFlip := exact_bulk_of_firstRoundCap16 hm
    (flipScramble (cyclicScramble16 (m := m))) hcaps.2
  have hB2 :
      HasPackSemanticPropertyB2 (by norm_num : 0 < 16)
        (cyclicScramble16 (m := m)) σ₂ (1/2^21) ∧
      HasPackSemanticPropertyB2 (by norm_num : 0 < 16)
        (flipScramble (cyclicScramble16 (m := m))) (flipScramble σ₂) (1/2^21) := by
    exact ⟨semantic_B2_of_exact (by norm_num) hfirst hGood.1,
      semantic_B2_of_exact (by norm_num) hfirstFlip hGoodFlip.1⟩
  have hSRR1 := cyclic_and_flip_SR_R1_16 (m := m)
  have hF2 := F2_both_orientations F2Params.std (by norm_num)
    (by simpa [F2Params.std] using (show 131040 ≤ m by omega))
    ⟨hSRR1.1.1, hSRR1.1.2, hGood.2⟩
    ⟨hSRR1.2.1, hSRR1.2.2, hGoodFlip.2⟩
  have heps : (1 / (F2Params.std.J : Real)) = eps := by
    norm_num [eps, F2Params.std]
  rw [heps] at hF2
  exact ⟨σ₂, hB2, hF2⟩

end Tapered945
