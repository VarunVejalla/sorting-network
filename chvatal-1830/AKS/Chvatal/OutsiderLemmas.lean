module
/-
  # Chvatal §4 Lemmas 4.1–4.4 (algebraic cores)

  Source: V. Chvatal, *Lecture Notes on the New AKS Sorting Network*,
  Rutgers DCS-TR-294 (1992), §4.

  Status:
  * Lemma 4.1 geometric envelope and parent-address bound: kernel-checked under
    `StageCounts` hypotheses (wire mass + bad-key bound from `P`).
  * Lemma 4.2 coefficient assembly: kernel-checked.
  * Lemmas 4.3–4.4: inductive step algebra under source-splitting hypotheses
    and (4.2)/(4.5); combinatorial stage dynamics deferred to the scheduler.
-/

public import AKS.Chvatal.SeparatorContract
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Field.GeomSum
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

namespace Chvatal

open Finset

/-! **Geometric envelope for Lemma 4.1** -/






/-! **Lemma 4.1** -/




/-! **Lemma 4.2** -/

/-- Interior identity: `(k-1)Δ₂ - π/2 = slackCoeff · c` with
    `Δ₂ = ν c / (A k²)` and `π = (A ν k - 1) c / Q`. -/
theorem slackCoeff_of_delta2_pi (p : ScheduleParams) (c : Rat) :
    let Q := capacityRatio p
    let delta2 := p.nu / (p.A * (p.br : Rat) ^ 2) * c
    let pi := (p.A * p.nu * (p.br : Rat) - 1) / Q * c
    ((p.br : Rat) - 1) * delta2 - pi / 2 = slackCoeff p * c := by
  intro Q delta2 pi
  have hQ : Q = p.A ^ 2 * (p.br : Rat) ^ 2 := rfl
  have hA : p.A ≠ 0 := ne_of_gt p.A_pos
  have hk : (p.br : Rat) ≠ 0 := ne_of_gt p.br_cast_pos
  unfold slackCoeff
  simp only [hQ, delta2, pi]
  field_simp [hA, hk]
  ring

theorem cond42_coeff_form (p : ScheduleParams) (ip : InvariantParams) :
    Cond42 p ip ↔
      lemma42_coeff p ip / (p.A * p.nu) +
          ip.mu * ip.delta * p.A * (p.br : Rat) / p.nu ≤ ip.mu := by
  simp only [Cond42, lemma42_coeff]

/-- Lemma 4.2 algebraic assembly: outsider mass, sibling mass, intrusion, slack. -/
theorem lemma42_of_parts (p : ScheduleParams) (ip : InvariantParams)
    (c outsiders sibMass intrusion slack : Rat)
    (hout : outsiders ≤ ip.mu * c)
    (hsib : sibMass ≤ ((p.br : Rat) - 1) * ip.mu * siblingFactor p ip * c)
    (hintrusion : intrusion ≤ ip.epsB * c)
    (hslack : slack ≤ slackCoeff p * c) :
    outsiders + sibMass + intrusion + slack ≤ lemma42_coeff p ip * c := by
  simp only [lemma42_coeff]
  linarith [hout, hsib, hintrusion, hslack]

/-! **Lemma 4.3** -/

/-- Capacity step: `c(i+1, t+1) = A ν c(i, t)`. -/
theorem capacity_child_stage (p : ScheduleParams) (d i t : Nat) :
    capacity p d (i + 1) (t + 1) = p.A * p.nu * capacity p d i t := by
  rw [capacity_succ_level, capacity_succ_stage]
  ring

/-- Scale Cond (4.2) by nonnegative capacity `c`:
    `lemma42_coeff·c + (μ δ k A²)·c ≤ μ·A·ν·c`. -/
theorem cond42_scaled (p : ScheduleParams) (ip : InvariantParams)
    (c : Rat) (hc : 0 ≤ c) (h42 : Cond42 p ip) :
    lemma42_coeff p ip * c + ip.mu * ip.delta * (p.br : Rat) * p.A ^ 2 * c ≤
      ip.mu * (p.A * p.nu * c) := by
  have h42' := (cond42_coeff_form p ip).mp h42
  have hAnu : (0 : Rat) < p.A * p.nu := mul_pos p.A_pos p.hnu_pos
  have hbr : (p.br : Rat) ≠ 0 := ne_of_gt p.br_cast_pos
  have hmul := mul_le_mul_of_nonneg_right h42' (mul_nonneg hAnu.le hc)
  rw [add_mul] at hmul
  have ha : lemma42_coeff p ip / (p.A * p.nu) * (p.A * p.nu * c) =
      lemma42_coeff p ip * c := by
    calc lemma42_coeff p ip / (p.A * p.nu) * (p.A * p.nu * c)
        = (lemma42_coeff p ip / (p.A * p.nu) * (p.A * p.nu)) * c := by ring
      _ = lemma42_coeff p ip * c := by rw [div_mul_cancel₀ _ (ne_of_gt hAnu)]
  have hb : ip.mu * ip.delta * p.A * (p.br : Rat) / p.nu * (p.A * p.nu * c) =
      ip.mu * ip.delta * (p.br : Rat) * p.A ^ 2 * c := by
    have hnu : p.nu ≠ 0 := ne_of_gt p.hnu_pos
    field_simp [hnu]
  rw [ha, hb] at hmul
  exact hmul

/-- Lemma 4.3 algebra under Cond (4.2) and source bounds. -/
theorem lemma43_of_sources (p : ScheduleParams) (ip : InvariantParams)
    (c : Rat) (hc : 0 < c)
    (src : Lemma43Sources)
    (hparent : src.fromParent ≤ lemma42_coeff p ip * c)
    (hchild : src.fromChildren ≤ ip.mu * ip.delta * (p.br : Rat) * p.A ^ 2 * c)
    (h42 : Cond42 p ip) :
    src.total ≤ ip.mu * (p.A * p.nu * c) := by
  have hbound := cond42_scaled p ip c (le_of_lt hc) h42
  linarith [src.hsplit, hparent, hchild, hbound]


/-! **Lemma 4.4** -/

/-- Scale Cond (4.5) by `μ δ^{r-1} A ν c`. -/
theorem cond45_scaled (p : ScheduleParams) (ip : InvariantParams)
    (c : Rat) (hc : 0 ≤ c) (r : Nat) (hr : 1 ≤ r) (h45 : Cond45 p ip) :
    ip.epsF * (ip.mu * ip.delta ^ (r - 1) * c) +
        ip.delta ^ 2 * p.A * (p.br : Rat) / p.nu *
          (ip.mu * ip.delta ^ (r - 1) * (p.A * p.nu * c)) ≤
      ip.mu * ip.delta ^ r * (p.A * p.nu * c) := by
  have h45' : ip.epsF / (p.A * p.nu) +
      ip.delta ^ 2 * p.A * (p.br : Rat) / p.nu ≤ ip.delta := h45
  have hAnu : (0 : Rat) < p.A * p.nu := mul_pos p.A_pos p.hnu_pos
  have hbase : 0 ≤ ip.mu * ip.delta ^ (r - 1) * c :=
    mul_nonneg (mul_nonneg ip.mu_nonneg (pow_nonneg ip.delta_nonneg _)) hc
  have hscale := mul_nonneg hbase hAnu.le
  have hmul := mul_le_mul_of_nonneg_right h45' hscale
  rw [add_mul] at hmul
  have ha : ip.epsF / (p.A * p.nu) *
      (ip.mu * ip.delta ^ (r - 1) * c * (p.A * p.nu)) =
      ip.epsF * (ip.mu * ip.delta ^ (r - 1) * c) := by
    calc ip.epsF / (p.A * p.nu) *
            (ip.mu * ip.delta ^ (r - 1) * c * (p.A * p.nu))
        = (ip.epsF / (p.A * p.nu) * (p.A * p.nu)) *
            (ip.mu * ip.delta ^ (r - 1) * c) := by ring
      _ = ip.epsF * (ip.mu * ip.delta ^ (r - 1) * c) := by
          rw [div_mul_cancel₀ _ (ne_of_gt hAnu)]
  have hb : ip.delta ^ 2 * p.A * (p.br : Rat) / p.nu *
      (ip.mu * ip.delta ^ (r - 1) * c * (p.A * p.nu)) =
      ip.delta ^ 2 * p.A * (p.br : Rat) / p.nu *
        (ip.mu * ip.delta ^ (r - 1) * (p.A * p.nu * c)) := by
    ring
  have hR : ip.delta * (ip.mu * ip.delta ^ (r - 1) * c * (p.A * p.nu)) =
      ip.mu * ip.delta ^ r * (p.A * p.nu * c) := by
    have hpow : ip.delta * ip.delta ^ (r - 1) = ip.delta ^ r := by
      calc ip.delta * ip.delta ^ (r - 1)
          = ip.delta ^ ((r - 1) + 1) := (pow_succ' _ _).symm
        _ = ip.delta ^ r := by rw [Nat.sub_add_cancel hr]
    rw [← hpow]; ring
  rw [ha, hb, hR] at hmul
  exact hmul

/-- Lemma 4.4 algebra under Cond (4.5) and fringe/child source bounds. -/
theorem lemma44_of_sources (p : ScheduleParams) (ip : InvariantParams)
    (c : Rat) (hc : 0 < c) (r : Nat) (hr : 1 ≤ r)
    (src : Lemma44Sources)
    (hparent : src.fromParent ≤
      ip.epsF * (ip.mu * ip.delta ^ (r - 1) * c))
    (hchild : src.fromChildren ≤
      ip.delta ^ 2 * p.A * (p.br : Rat) / p.nu *
        (ip.mu * ip.delta ^ (r - 1) * (p.A * p.nu * c)))
    (h45 : Cond45 p ip) :
    src.total ≤ ip.mu * ip.delta ^ r * (p.A * p.nu * c) := by
  have hbound := cond45_scaled p ip c (le_of_lt hc) r hr h45
  linarith [src.hsplit, hparent, hchild, hbound]

end Chvatal
