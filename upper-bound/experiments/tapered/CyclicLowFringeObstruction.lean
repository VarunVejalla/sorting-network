import RaggedIntegerSchedule
import SignedReserve
import AKS.Chvatal.F2Defs
import SameBagScale
import Mathlib.Tactic

namespace Tapered945
open Chvatal

set_option maxHeartbeats 0

/-- At the repeated minimum reference capacity `2^34`, the signed address
flow and its one-wire rounding allowance cap the upward port below 263,106.
This is a kernel-checked certificate for the low-fringe scale bottleneck. -/
theorem local_upflow_lt_263106_at_min_capacity {d : Nat}
    (b : KBag 64 d) (eta : Rat) (count : Nat)
    (flow : LocalIntegerFlow b (2^34) eta count) :
    (flow.up : Rat) < 263106 := by
  have hdebt := bagAddressDebt_bounds b
  have hC : (0 : Rat) ≤ 2^34 := by positivity
  have hdebtScaled : -bagAddressDebt b * (2^34 : Rat) ≤
      eAbs * (2^34 : Rat) := by
    have h := mul_le_mul_of_nonneg_right hdebt.1 hC
    unfold eAbs at h ⊢
    nlinarith
  have hrounded := flow.upError
  rw [abs_le] at hrounded
  have hupper : (flow.up : Rat) ≤
      (upFlow + eAbs) * (2^34 : Rat) + 1 := by
    unfold addressUpAt at hrounded
    nlinarith [hdebtScaled]
  have hnum : (upFlow + eAbs) * (2^34 : Rat) + 1 < 263106 := by
    norm_num [upFlow, eAbs]
  exact lt_of_le_of_lt hupper hnum

/-- The width-16 protected low fringe requires 2,096,656 wires, more than
eight times the largest up-port available at a `2^34` reference capacity. -/
theorem width16_low_fringe_exceeds_min_capacity_flow {d : Nat}
    (b : KBag 64 d) (eta : Rat) (count : Nat)
    (flow : LocalIntegerFlow b (2^34) eta count) :
    (131041 * 16 : Nat) > flow.up := by
  have hup := local_upflow_lt_263106_at_min_capacity b eta count flow
  have hupNat : flow.up < 263106 := by exact_mod_cast hup
  norm_num
  omega

/-- Consequently, no width-16 truncated padded witness can meet its low
protected-fringe fit premise at these minimum-capacity bags using the current
integer-flow profile. -/
theorem width16_witness_low_fit_impossible_at_min_capacity {d : Nat}
    (b : KBag 64 d) (eta : Rat) (count columns : Nat)
    (flow : LocalIntegerFlow b (2^34) eta count)
    (hcolumns : 16 ≤ columns) :
    ¬ ((F2Params.std.f + 1) * columns ≤ flow.up) := by
  have hup := width16_low_fringe_exceeds_min_capacity_flow b eta count flow
  have hthreshold : 131041 * 16 ≤ (F2Params.std.f + 1) * columns := by
    norm_num [F2Params.std]
    omega
  intro hfit
  omega

/-- Form of the obstruction that can be applied directly to an actual
scheduled capacity after rewriting it to `2^34`. -/
theorem width16_witness_low_fit_impossible_at_capacity {d : Nat}
    (b : KBag 64 d) {C : Rat} (hC : C = 2^34)
    (eta : Rat) (count columns : Nat)
    (flow : LocalIntegerFlow b C eta count) (hcolumns : 16 ≤ columns) :
    ¬ ((F2Params.std.f + 1) * columns ≤ flow.up) := by
  subst C
  exact width16_witness_low_fit_impossible_at_min_capacity
    b eta count columns flow hcolumns

/-- The obstruction occurs at actual scheduled ordinary-interior bags at
linearly many late stages, not merely at an abstract capacity value. -/
theorem candidate_late_bag_has_no_current_low_fringe_flow
    (d k : Nat) (hd : 14 ≤ d) (hk : 4 * k + 8 ≤ d) :
    ∃ b : KBag 64 d,
      candidateScheduledActive d (candidateTf d - (6 * k + 1)) b ∧
      candidateAlpha d (candidateTf d - (6 * k + 1)) + 2 ≤
        candidateOmega (candidateTf d - (6 * k + 1)) ∧
      candidateReferenceCapacity d b.l (candidateTf d - (6 * k + 1)) = 2^34 ∧
      ∀ eta count
        (flow : LocalIntegerFlow b
          (candidateReferenceCapacity d b.l (candidateTf d - (6 * k + 1)))
          eta count) (columns : Nat),
        16 ≤ columns →
          ¬ ((F2Params.std.f + 1) * columns ≤ flow.up) := by
  obtain ⟨b, hactive, hordinary, hcapacity⟩ :=
    candidate_late_small_active_bag_exists d k hd hk
  refine ⟨b, hactive, hordinary, hcapacity, ?_⟩
  intro eta count flow columns hcolumns hfit
  exact (width16_witness_low_fit_impossible_at_capacity b hcapacity
    eta count columns flow hcolumns) hfit

end Tapered945
