import CandidateBulkFail
import Mathlib.Tactic

set_option maxHeartbeats 0

namespace Tapered945
open Chvatal
open Classical

/-- Logarithmic union cost at the proposed `2^30` row floor. -/
theorem cyclic_union_log_bound_30 (m : Nat) (hm : 2^30 ≤ m) :
    Real.log (2*((m : Real)+1)) ≤
      31*Real.log 2 + ((m : Real)/2^30-1) + 1/2^30 := by
  have hM : (2 : Real)^30 ≤ m := by exact_mod_cast hm
  have hm0 : (0 : Real) < m := lt_of_lt_of_le (by positivity) hM
  have hlogm := Real.log_le_sub_one_of_pos (div_pos hm0 (by positivity : (0 : Real)<2^30))
  rw [Real.log_div hm0.ne' (by positivity), Real.log_pow] at hlogm
  have hlogp := Real.log_le_sub_one_of_pos (div_pos (by positivity : (0 : Real)<m+1) hm0)
  rw [Real.log_div (by positivity) hm0.ne'] at hlogp
  have hdiv : ((m : Real)+1)/m-1 = 1/m := by field_simp; ring
  rw [hdiv] at hlogp
  have hinv : 1/(m : Real) ≤ 1/(2 : Real)^30 :=
    one_div_le_one_div_of_le (by positivity) hM
  rw [Real.log_mul (by norm_num) (by positivity)]
  push_cast at hlogm
  nlinarith

/-- With the small deterministic first-round error budget `2^-24`, the existing
exact-mass Bernstein union closes at `m=2^30` for target error `2^-21`.
The first-round construction is deliberately not assumed here. -/
theorem cyclic_round2_gap_30 (m : Nat) (hm : 2^30 ≤ m) :
    Real.log (2*((m : Real)+1)) + 1/2 ≤ (m : Real)*
      ((1 : Real)*(1/2^21)/2 -
        (1 : Real)^2*(1/2+2*(1 : Real)/9)*(1/2^24)/2) := by
  have hb := cyclic_union_log_bound_30 m hm
  have hl := Real.log_two_lt_d9
  have hM : (2 : Real)^30 ≤ m := by exact_mod_cast hm
  have hcoef : (1 : Real)/2^22 - (13 : Real)/(36*2^24) ≥ 1/2^23 := by norm_num
  have hg := mul_le_mul_of_nonneg_right hM (show (0 : Real) ≤ 1/2^23 by positivity)
  norm_num at hb hl hg ⊢
  nlinarith

theorem cyclic_round2_fail_fraction {m : Nat} (hm : 2^30 ≤ m) :
    ((Finset.univ.filter (fun σ : Scramble m 16 =>
      ¬ ExactBulk σ (IntermediateAdm (1/2^24)) (1/2^21))).card : Real) ≤
      (1/1000)*(Fintype.card (Scramble m 16) : Real) := by
  have hm0 : 0 < m := lt_of_lt_of_le (by positivity) hm
  exact exact_round2_fail_fraction (m := m) (n := 16) hm0 (by norm_num)
    (1/2^24) (1/2^21) 1
    (by norm_num) (by norm_num) (cyclic_round2_gap_30 m hm)

/-- A sufficient deterministic first-round contract: every output column is at
most 15 above the exact-mass mean. At sixteen columns it implies the small
error budget needed by `cyclic_round2_fail_fraction`. -/
def FirstRoundCap16 {m : Nat} (σ : Scramble m 16) : Prop :=
  ∀ c : MonotoneColumnSums m 16, ∀ i : Nat,
    totalColumnOnes c = 16*i → i ≤ m →
      ∀ j : Fin 16, scrambledColSum c σ j ≤ i+15

theorem exact_bulk_of_firstRoundCap16 {m : Nat} (hm : 2^30 ≤ m)
    (σ : Scramble m 16) (hcap : FirstRoundCap16 σ) :
    ExactBulk σ (fun _ _ => True) (1/2^24) := by
  intro c i hmass hi _
  have hsum : onesAboveBottom c σ i ≤ 16*15 := by
    unfold onesAboveBottom
    calc
      _ ≤ ∑ _j : Fin 16, 15 := Finset.sum_le_sum fun j _ => by
        have h := hcap c i hmass hi j
        omega
      _ = 16*15 := by simp
  have hmR : (2^30 : Real) ≤ m := by exact_mod_cast hm
  have hstrict : (16*15 : Real) < ((1/2^24 : Real)/2)*((m : Real)*16) := by
    rw [show ((1/2^24 : Real)/2)*((m : Real)*16) = (m : Real)/2^21 by ring]
    norm_num
    nlinarith
  exact lt_of_le_of_lt (by exact_mod_cast hsum) hstrict

/-- The remaining local B2 gate after the cyclic discrepancy lemma: a capped
first-round scramble, and its flipped version, can be paired with a second
scramble at the lower row floor. -/
theorem pair_B2_of_firstRoundCap16 {m : Nat} (hm : 2^30 ≤ m)
    (σ₁ : Scramble m 16) (hcap : FirstRoundCap16 σ₁)
    (hcapFlip : FirstRoundCap16 (flipScramble σ₁)) :
    ∃ σ₂ : Scramble m 16,
      HasPackSemanticPropertyB2 (by norm_num : 0 < 16) σ₁ σ₂ (1/2^21) ∧
      HasPackSemanticPropertyB2 (by norm_num : 0 < 16)
        (flipScramble σ₁) (flipScramble σ₂) (1/2^21) := by
  have hfirst := exact_bulk_of_firstRoundCap16 hm σ₁ hcap
  have hfirstFlip := exact_bulk_of_firstRoundCap16 hm (flipScramble σ₁) hcapFlip
  obtain ⟨σ₂, hsecond, hsecondFlip⟩ := exists_and_flip
    (fun σ : Scramble m 16 => ExactBulk σ (IntermediateAdm (1/2^24)) (1/2^21))
    (c := 1/1000) (by norm_num) (cyclic_round2_fail_fraction hm)
  exact ⟨σ₂,
    semantic_B2_of_exact (by norm_num) hfirst hsecond,
    semantic_B2_of_exact (by norm_num) hfirstFlip hsecondFlip⟩

end Tapered945
