import UpperBoundContrib.Spec
import AKS.Bounds.Certificate

/-! Adapter: a closed network-family certificate `C * log₂ n + K` yields `BoundSpec C`. -/

namespace UpperBoundContrib

open Filter

theorem boundSpec_of_certificate {C K : ℝ} (cert : SortingDepth.UpperBoundCertificate C K) :
    BoundSpec C := by
  intro ε hε
  have hlog_atTop : Tendsto (fun n : ℕ => Real.logb 2 (n : ℝ)) atTop atTop :=
    (Real.tendsto_logb_atTop (by norm_num : (1 : ℝ) < 2)).comp tendsto_natCast_atTop_atTop
  have hK : ∀ᶠ n : ℕ in atTop, K / ε < Real.logb 2 (n : ℝ) :=
    hlog_atTop.eventually (eventually_gt_atTop (K / ε))
  filter_upwards [eventually_ge_atTop (max cert.threshold 2), hK] with n hn hk
  have hN : cert.threshold ≤ n := le_trans (Nat.le_max_left _ _) hn
  have hb := cert.minimum_bound hN
  have hK' : K < ε * Real.logb 2 (n : ℝ) := by
    have h' := (div_lt_iff₀ hε).1 hk
    nlinarith [h']
  nlinarith

end UpperBoundContrib
