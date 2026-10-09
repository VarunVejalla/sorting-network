module
-- Chvátal §4 Lemmas 4.2-4.4: algebraic cores

public import AKS.Chvatal.OutsiderInvariant

@[expose] public section

namespace Chvatal

/-- Interior identity: `(k-1)Δ₂ - π/2 = slackCoeff · c` with
    `Δ₂ = ν c / (A k²)` and `π = (A ν k - 1) c / Q`. -/
theorem slackCoeff_of_delta2_pi (p : ScheduleParams) (c : Rat) :
    let Q := capacityRatio p
    let delta2 := p.nu / (p.A * (p.br : Rat) ^ 2) * c
    let pi := (p.A * p.nu * (p.br : Rat) - 1) / Q * c
    ((p.br : Rat) - 1) * delta2 - pi / 2 = slackCoeff p * c := by
  intro Q delta2 pi
  have hA : p.A ≠ 0 := ne_of_gt p.A_pos
  have hk : (p.br : Rat) ≠ 0 := ne_of_gt p.br_cast_pos
  unfold slackCoeff
  simp only [show Q = p.A ^ 2 * (p.br : Rat) ^ 2 from rfl, delta2, pi]
  field_simp [hA, hk]
  ring

/-- Cond (4.2) scaled by `c ≥ 0`. -/
theorem cond42_scaled (p : ScheduleParams) (ip : InvariantParams) (c : Rat) (hc : 0 ≤ c)
    (h : Cond42 p ip) :
    (ip.mu + ((p.br : Rat) - 1) * ip.mu * siblingFactor p ip + slackCoeff p + ip.epsB) * c +
        ip.mu * ip.delta * (p.br : Rat) * p.A ^ 2 * c ≤ ip.mu * (p.A * p.nu * c) := by
  have hA := p.A_pos
  have hnu := p.hnu_pos
  have := mul_le_mul_of_nonneg_right h (mul_nonneg (mul_pos hA hnu).le hc)
  convert this using 1
  field_simp

/-- Cond (4.5) scaled by `μ δ^{r-1} A ν c`. -/
theorem cond45_scaled (p : ScheduleParams) (ip : InvariantParams) (c : Rat) (hc : 0 ≤ c)
    (r : Nat) (hr : 1 ≤ r) (h : Cond45 p ip) :
    ip.epsF * (ip.mu * ip.delta ^ (r - 1) * c) +
        ip.delta ^ 2 * p.A * (p.br : Rat) / p.nu *
          (ip.mu * ip.delta ^ (r - 1) * (p.A * p.nu * c)) ≤
      ip.mu * ip.delta ^ r * (p.A * p.nu * c) := by
  have hA := p.A_pos
  have hnu := p.hnu_pos
  have hd := ip.delta_nonneg
  have := mul_le_mul_of_nonneg_right h
    (mul_nonneg (mul_nonneg (mul_nonneg ip.mu_nonneg (pow_nonneg hd (r - 1))) hc) (mul_pos hA hnu).le)
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at this ⊢
  convert this using 1 <;> field_simp
  ring

end Chvatal
