module
/-
  # Chvatal §3 send-up / send-down budgets

  Source: V. Chvatal, *Lecture Notes on the New AKS Sorting Network*,
  Rutgers DCS-TR-294 (1992), §3 (`π`, `χ`).

  Status: scalar send budgets. Order-0 children accounting uses the uniform
  `c/Q` upper bound (`sendUpBudget`); the level-dependent `π` formulas are
  recorded for the placement networks.
-/

public import AKS.Chvatal.Scheduler
public import Mathlib.Tactic.Positivity

@[expose] public section

namespace Chvatal

/-! **Uniform send-up budget** -/

/-- Order-0 children-send size budget: `c(i,t) / Q` with `Q = A² k²`. -/
def sendUpBudget (p : ScheduleParams) (d i t : Nat) : Rat :=
  capacity p d i t / capacityRatio p

theorem sendUpBudget_nonneg (p : ScheduleParams) (d i t : Nat) :
    0 ≤ sendUpBudget p d i t :=
  div_nonneg (capacity_pos p d i t).le (capacityRatio_pos p).le

theorem sendUpBudget_eq_cap_div_Q (p : ScheduleParams) (d i t : Nat) :
    sendUpBudget p d i t = capacity p d i t / (p.A ^ 2 * (p.br : Rat) ^ 2) := by
  simp [sendUpBudget, capacityRatio]

/-! **Paper `π(i,t)` (interior / boundary cases, `2 ≤ t`)** -/

/-- Interior send-up fraction of capacity: `(A ν k - 1) / Q`. -/
def sendUpFracInterior (p : ScheduleParams) : Rat :=
  (p.A * p.nu * (p.br : Rat) - 1) / capacityRatio p

/-- Paper interior `π(i,t) = (A ν k - 1) c(i,t) / Q` for `α(t) < i < ω(t)`. -/
def sendUpPiInterior (p : ScheduleParams) (d i t : Nat) : Rat :=
  sendUpFracInterior p * capacity p d i t

theorem sendUpBudget_le_pi_interior (p : ScheduleParams) (d i t : Nat)
    (h : 2 ≤ p.A * p.nu * (p.br : Rat)) :
    sendUpBudget p d i t ≤ sendUpPiInterior p d i t := by
  have hc := (capacity_pos p d i t).le
  have hfrac : (1 : Rat) / capacityRatio p ≤ sendUpFracInterior p := by
    unfold sendUpFracInterior
    have hden : 0 < capacityRatio p := capacityRatio_pos p
    rw [div_le_div_iff₀ hden hden]
    have : (1 : Rat) ≤ p.A * p.nu * (p.br : Rat) - 1 := by linarith
    nlinarith [hden.le]
  calc sendUpBudget p d i t
      = (1 / capacityRatio p) * capacity p d i t := by
        unfold sendUpBudget; ring
    _ ≤ sendUpFracInterior p * capacity p d i t :=
        mul_le_mul_of_nonneg_right hfrac hc
    _ = sendUpPiInterior p d i t := rfl

end Chvatal
