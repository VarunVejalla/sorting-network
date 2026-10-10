module

public import AKS.Kahale.AmortizedAccounting

/-! # Candidate bank and coefficient conversion

The endpoint calculation is independent of the unproved local transition
inequality. Parameters are explicit so coefficients above four remain possible.
-/

@[expose] public section

namespace Kahale

def layerBank (beta kappa lambda : ℝ) (uniform fixed correlation : ℕ → ℝ)
    (t : ℕ) : ℝ :=
  kappa * uniform t - lambda * fixed t - beta * correlation t

theorem layerBank_endpoint (beta kappa lambda n : ℝ)
    (uniform fixed correlation : ℕ → ℝ) (d : ℕ)
    (hu0 : uniform 0 = n) (hud : uniform d = 0)
    (hv0 : fixed 0 = 0) (hvd : fixed d = n)
    (hq0 : correlation 0 = 0) (hqd : correlation d = 0) :
    layerBank beta kappa lambda uniform fixed correlation 0 -
      layerBank beta kappa lambda uniform fixed correlation d = (kappa + lambda) * n := by
  simp only [layerBank, hu0, hud, hv0, hvd, hq0, hqd]
  ring

theorem depth_of_information_budget (information overhead capacity : ℝ)
    (d : ℕ) (hcapacity : 0 < capacity)
    (hbudget : information ≤ (d : ℝ) * capacity + overhead) :
    (information - overhead) / capacity ≤ (d : ℝ) := by
  apply (div_le_iff₀ hcapacity).mpr
  linarith

theorem four_lt_saving_coefficient (rho : ℝ) (hlow : (1 : ℝ) / 2 < rho)
    (hhigh : rho < 1) : 4 < 2 / (1 - rho) := by
  apply (lt_div_iff₀ (show 0 < 1 - rho by linarith)).mpr
  linarith

end Kahale
