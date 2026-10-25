import AKS.Bounds.KahaleAsymptotic
import Mathlib.Topology.Instances.EReal.Lemmas

/-! # Kahale's asymptotic lower bound without any upper-bound construction

The real-valued headline `liminf_minimum_div_logb_ge_kahale` needs Mathlib's
`IsCoboundedUnder (· ≥ ·)` premise, which `minimum_div_logb_cobounded` discharges
with the legacy bound `D(n) ≤ 102·10^62·⌈lg n⌉`.  The statements here use only the
finite Kahale inequality (`minimum_logarithmic_bound`, `minimum_tendsto_atTop`):

* `eventually_mul_logb_le_minimum`: for every `c < 1/(1 - lg φ)`, eventually
  `c · lg n ≤ D(n)`;
* `ereal_liminf_minimum_div_logb_ge_kahale`: the same `liminf` bound in `EReal`,
  a complete lattice, where no boundedness premise exists;
* `liminf_minimum_div_logb_ge_kahale_of_cobounded`: the real `liminf` bound with
  the coboundedness premise left as an explicit hypothesis.

`D(n)` itself (`minimum`, legacy `AKS.Bounds.Upper`) is a `Nat.find` whose existence
witness is the bitonic network; none of these proofs uses `minimum_depth_le`.
-/

namespace SortingDepth

open Filter
open scoped Topology

/-- For every `c` below Kahale's constant `1/(1 - lg φ)`, eventually `c · lg n ≤ D(n)`. -/
theorem eventually_mul_logb_le_minimum {c : ℝ} (hc : c < Kahale.depthConstant) :
    ∀ᶠ n : ℕ in atTop, c * Real.logb 2 n ≤ (minimum n : ℝ) := by
  have h := eventually_minimum_depth_ge_kahale_logb (Kahale.depthConstant - c) (by linarith)
  simpa only [sub_sub_cancel] using h

/-- Kahale's bound as an extended-real `liminf`; no boundedness premise is needed. -/
theorem ereal_liminf_minimum_div_logb_ge_kahale :
    (Kahale.depthConstant : EReal) ≤
      liminf (fun n : ℕ ↦ (((minimum n : ℝ) / Real.logb 2 n : ℝ) : EReal)) atTop := by
  have ht := (continuous_coe_real_ereal.tendsto _).comp kahale_envelope_tendsto
  refine ht.liminf_eq.symm.le.trans (liminf_le_liminf ?_)
  filter_upwards [eventually_minimum_div_logb_ge_kahale_envelope] with n hn
  exact EReal.coe_le_coe_iff.2 hn

/-- The real `liminf` bound, with Mathlib's coboundedness premise as a hypothesis
instead of being discharged by an upper-bound construction. -/
theorem liminf_minimum_div_logb_ge_kahale_of_cobounded
    (h : atTop.IsCoboundedUnder (· ≥ ·) (fun n : ℕ ↦ (minimum n : ℝ) / Real.logb 2 n)) :
    Kahale.depthConstant ≤
      liminf (fun n : ℕ ↦ (minimum n : ℝ) / Real.logb 2 n) atTop := by
  rw [← kahale_envelope_tendsto.liminf_eq]
  exact liminf_le_liminf eventually_minimum_div_logb_ge_kahale_envelope
    kahale_envelope_tendsto.isBoundedUnder_ge h

end SortingDepth
