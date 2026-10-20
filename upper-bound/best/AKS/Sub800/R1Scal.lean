import Mathlib.Tactic

/-! # The scalar parameters of the R1 invariant (generic)

The schedule is fixed at `(k, A, ν) = (16, 32, 1/8)` (`R1Sched`), so `Aν = 4`, `Aνk = 64` and the
residual `r* = (k−1)/(2A²k²) = 15/524288` are constants. The scalars of R1-PROOF that move with the
separator and the fringe are fields of `R1Scal`: `μ`, `δ`, `ε_B`, `ε_F`, `η`, and the reserve `γ`
for the separator-geometry charge. The conditions the invariant uses are fields too:
(4.2′) (`cond42`), (4.5) (`cond45`), the sibling series (`cond_sib`), and three bounds on `μ`
against the schedule's capacities (`mu_final`, `mu_rise`, `mu_mid`). A concrete point proves
them by `norm_num`. -/

namespace R1T

/-- The design-P residual `r* = (k−1)/(2A²k²)` at the fixed schedule. -/
def rstar : ℚ := 15 / 524288

theorem rstar_nonneg : 0 ≤ rstar := by unfold rstar; norm_num

/-- The scalars of the outsider invariant and their conditions. -/
structure R1Scal where
  mu : ℚ
  delta : ℚ
  epsB : ℚ
  epsF : ℚ
  eta : ℚ
  /-- The reserve for the separator-geometry charge `γ` (per parent capacity). -/
  gam : ℚ
  mu_pos : 0 < mu
  delta_pos : 0 < delta
  delta_le_one : delta ≤ 1
  epsF_pos : 0 < epsF
  epsB_nonneg : 0 ≤ epsB
  eta_nonneg : 0 ≤ eta
  gam_nonneg : 0 ≤ gam
  /-- `δ² k² A² < 1`. -/
  cond_sib : delta ^ 2 * (16 : ℚ) ^ 2 * (32 : ℚ) ^ 2 < 1
  /-- (4.2′): `μ + (15 μ sib + r* + ε_B η + γ) + μ δ k A² ≤ μ A ν`. -/
  cond42 : mu + (15 * mu * (delta * 16 * 32 ^ 2 / (1 - delta ^ 2 * 16 ^ 2 * 32 ^ 2)) + rstar +
    epsB * eta + gam) + mu * delta * 16 * 32 ^ 2 ≤ mu * 4
  /-- (4.5): `ε_F/(Aν) + δ² A k/ν ≤ δ`. -/
  cond45 : epsF / 4 + delta ^ 2 * 32 * 16 / (1 / 8) ≤ delta
  /-- No order-0 outsiders survive at the final capacity `2^16` (Lemma 4.5). -/
  mu_final : mu * 2 ^ 16 < 1
  /-- The fringe range fits in half the up-flow of a rising top (`π/2 = c/8192`). -/
  mu_rise : mu * 8192 ≤ 1
  /-- The fringe range fits in half the up-flow of an interior sender (`π/2 = 63 c/2^19`). -/
  mu_mid : mu * 524288 ≤ 63

namespace R1Scal

variable (S : R1Scal)

/-- `δ k A² / (1 − δ² k² A²)`. -/
def sib : ℚ := S.delta * 16 * 32 ^ 2 / (1 - S.delta ^ 2 * 16 ^ 2 * 32 ^ 2)

/-- Order-0 send budget per parent capacity. -/
def B0 : ℚ := 15 * S.mu * S.sib + rstar + S.epsB * S.eta + S.gam

theorem epsF_nonneg : 0 ≤ S.epsF := S.epsF_pos.le

theorem sib_pos : 0 < S.sib := by
  unfold sib
  have := S.delta_pos
  have := S.cond_sib
  apply div_pos (by positivity)
  nlinarith

theorem B0_nonneg : 0 ≤ S.B0 := by
  unfold B0
  have := S.mu_pos; have := S.sib_pos; have := S.epsB_nonneg; have := S.eta_nonneg
  have := S.gam_nonneg; have := rstar_nonneg
  positivity

theorem cond42' : S.mu + S.B0 + S.mu * S.delta * 16 * 32 ^ 2 ≤ S.mu * 4 := S.cond42

end R1Scal

end R1T
