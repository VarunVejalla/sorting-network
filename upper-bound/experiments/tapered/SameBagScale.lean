import CandidateFrontier
import SignedReserve
import Mathlib.Tactic

namespace Tapered945

/-- A linear family of late scheduled stages has active lower-bound capacity
exactly `2^34`, below the `2^38` threshold of the current padded witness.
The parameter range ensures the lower frontier level is nonnegative. -/
theorem candidate_late_small_capacity_exponent (d k : Nat)
    (hd : 14 ≤ d) (hk : 4 * k + 8 ≤ d) :
    let t := candidateTf d - (6 * k + 1)
    candidateCapacityExponent d (candidateAlpha d t) t = 34 := by
  dsimp
  have htf : candidateTf d = 3 * d - 20 := rfl
  have ht : candidateTf d - (6 * k + 1) = 3 * d - 21 - 6 * k := by omega
  have hquot : (2 * (3 * d - 21 - 6 * k) + 23) / 3 = 2 * d - 4 * k - 7 := by
    have hdecomp : 2 * (3 * d - 21 - 6 * k) + 23 =
        3 * (2 * d - 4 * k - 7) + 2 := by omega
    omega
  have hbase : candidateAlphaBase d (3 * d - 21 - 6 * k) = d - 4 * k - 7 := by
    unfold candidateAlphaBase
    rw [hquot]
    omega
  have hpar : (d - 4 * k - 7) % 2 = (3 * d - 21 - 6 * k) % 2 := by omega
  have halpha : candidateAlpha d (3 * d - 21 - 6 * k) = d - 4 * k - 7 := by
    unfold candidateAlpha Chvatal.ceilParity
    rw [hbase]
    simp [hpar]
  rw [ht, halpha]
  unfold candidateCapacityExponent
  omega

/-- The low-capacity level is genuinely present in the scheduled active band:
the address with index zero is an active bag at this stage. -/
theorem candidate_late_small_active_bag_exists (d k : Nat)
    (hd : 14 ≤ d) (hk : 4 * k + 8 ≤ d) :
    let t := candidateTf d - (6 * k + 1)
    ∃ b : Chvatal.KBag 64 d,
      candidateScheduledActive d t b ∧
        candidateAlpha d t + 2 ≤ candidateOmega t ∧
        candidateReferenceCapacity d b.l t = 2 ^ 34 := by
  dsimp
  let t := candidateTf d - (6 * k + 1)
  have htform : t = 3 * d - 21 - 6 * k := by
    dsimp [t, candidateTf]
    omega
  have ht : t ≤ candidateTf d := by
    dsimp [t]
    omega
  have hdecompAlpha : 2 * (3 * d - 21 - 6 * k) + 23 =
      3 * (2 * d - 4 * k - 7) + 2 := by omega
  have hquotAlpha : (2 * (3 * d - 21 - 6 * k) + 23) / 3 =
      2 * d - 4 * k - 7 := by omega
  have hbaseAlpha : candidateAlphaBase d (3 * d - 21 - 6 * k) = d - 4 * k - 7 := by
    unfold candidateAlphaBase
    rw [hquotAlpha]
    omega
  have hparAlpha : (d - 4 * k - 7) % 2 = (3 * d - 21 - 6 * k) % 2 := by omega
  have hAlpha : candidateAlpha d t = d - 4 * k - 7 := by
    rw [htform]
    unfold candidateAlpha Chvatal.ceilParity
    rw [hbaseAlpha]
    simp [hparAlpha]
  have hdecompOmega : 3 * d - 21 - 6 * k + 4 =
      3 * (d - 2 * k - 6) + 1 := by omega
  have hquotOmega : (3 * d - 21 - 6 * k + 4) / 3 = d - 2 * k - 6 := by omega
  have hbaseOmega : candidateOmegaBase (3 * d - 21 - 6 * k) = d - 2 * k - 6 := by
    unfold candidateOmegaBase
    rw [hquotOmega]
  have hparOmega : (d - 2 * k - 6) % 2 ≠ (3 * d - 21 - 6 * k) % 2 := by omega
  have hOmega : candidateOmega t = d - 2 * k - 5 := by
    rw [htform]
    unfold candidateOmega Chvatal.ceilParity
    rw [hbaseOmega]
    simp [hparOmega] <;> omega
  have hlevel : candidateAlpha d t ≤ d := by
    calc
      candidateAlpha d t ≤ candidateOmega t := candidate_frontiers_order d hd t ht
      _ ≤ d := candidate_omega_le_depth d hd t ht
  let b : Chvatal.KBag 64 d := ⟨candidateAlpha d t, 0, hlevel, by simp⟩
  refine ⟨b, ?_, ?_, ?_⟩
  · unfold candidateScheduledActive candidateActive b
    refine ⟨⟨le_rfl, candidate_frontiers_order d hd t ht⟩,
      candidate_alpha_parity d t⟩
  · rw [hAlpha, hOmega]
    omega
  · have hexp : candidateCapacityExponent d (candidateAlpha d t) t = 34 := by
      simpa [t] using candidate_late_small_capacity_exponent d k hd hk
    change (2 : Rat) ^ (candidateCapacityExponent d b.l t) = 2 ^ 34
    rw [hexp]

/-- If the intended 69-wire occupancy invariant holds at one of these bags,
its actual local register is still below the padded-witness existence floor. -/
theorem candidate_late_small_occupancy_below_provider_floor (d k : Nat)
    (eta : Rat) (count : Nat) (hd : 14 ≤ d) (hk : 4 * k + 8 ≤ d)
    (heta : |eta| ≤ 69)
    (hcount : (count : Rat) = (1 - 1 / cap) *
      candidateReferenceCapacity d (candidateAlpha d
        (candidateTf d - (6 * k + 1))) (candidateTf d - (6 * k + 1)) + eta) :
    count < 2 ^ 38 := by
  have hcap : candidateReferenceCapacity d (candidateAlpha d
      (candidateTf d - (6 * k + 1))) (candidateTf d - (6 * k + 1)) = 2 ^ 34 := by
    unfold candidateReferenceCapacity
    rw [candidate_late_small_capacity_exponent d k hd hk]
  have hetaHi : eta ≤ 69 := abs_le.mp heta |>.2
  have hreal : (count : Rat) < 2 ^ 38 := by
    rw [hcount, hcap]
    have hcoef : 0 ≤ 1 - 1 / cap ∧ 1 - 1 / cap ≤ 1 := by
      norm_num [cap]
    norm_num [cap] at ⊢
    nlinarith
  exact_mod_cast hreal

end Tapered945
