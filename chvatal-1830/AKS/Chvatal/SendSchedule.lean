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


/-! **Paper `π(i,t)` (interior / boundary cases, `2 ≤ t`)** -/




end Chvatal
