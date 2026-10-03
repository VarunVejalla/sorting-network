module

public import AKS.Bags.PatersonParams

/-! # Parameters for Paterson's rounded bag invariant

The separator support and the invariant coefficient are separate: a little
slack between them absorbs the loss of at most eight wires when bags are
rounded. The initial instance prioritizes a complete rounded proof over the
paper's approximate best constant. Source: Paterson (1990), Sections 4 and 7;
the local archived paper is `docs/paterson.pdf`.
-/

@[expose] public section

namespace Paterson.Bags

/-- Parameters consumed by the interior bag proof. `mu` and `delta` control
stranger counts; `support` and `tailError` belong to the local separator. -/
structure Params where
  A : ℚ
  mu : ℚ
  delta : ℚ
  nu : ℚ
  lambda : ℚ
  support : ℚ
  tailError : ℚ
  splitError : ℚ
  freshCost : ℚ
  minCapacity : ℚ
  roundingAllowance : ℚ
  A_gt_one : 1 < A
  mu_pos : 0 < mu
  delta_pos : 0 < delta
  delta_lt_one : delta < 1
  nu_pos : 0 < nu
  nu_lt_one : nu < 1
  lambda_pos : 0 < lambda
  lambda_lt_one : lambda < 1
  mu_lt_support : mu < support
  tailError_nonneg : 0 ≤ tailError
  splitError_nonneg : 0 ≤ splitError
  freshCost_nonneg : 0 ≤ freshCost
  minCapacity_pos : 0 < minCapacity
  roundingAllowance_nonneg : 0 ≤ roundingAllowance
  geometric : 4 * delta ^ 2 * A ^ 2 < 1
  capacity : nu = 2 * lambda * A + (1 - lambda) / (2 * A)
  tail : 2 * A ^ 2 * delta ^ 2 + tailError < nu * A * delta
  first : 2 * mu * delta * A ^ 2 +
    2 * mu * delta * A ^ 2 / (1 - 4 * delta ^ 2 * A ^ 2) +
    1 / (8 * A ^ 2 - 2) + mu + splitError / 2 < nu * mu * A
  firstRounded : 2 * mu * delta * A + freshCost +
    roundingAllowance / minCapacity ≤ nu * mu

/-- Rounded-proof working parameters. The published local depth budgets are
unchanged, but `mu < 1/50` and `nu = 18/25` leave explicit rounding slack.
The fresh-error budget also retains the residual low/high strangers after
fringe filtering instead of treating all such strangers as exactly removed. -/
def roundedParams : Params where
  A := 19 / 4
  mu := 199 / 10000
  delta := 1 / 57
  nu := 18 / 25
  lambda := 584 / 8925
  support := patersonMu
  tailError := patersonTailError
  splitError := patersonDelta0
  freshCost := (1 - patersonAlpha0 + patersonDelta0) / (2 * (19 / 4)) +
    patersonTailError * (199 / 10000) / (19 / 4)
  minCapacity := 10 ^ 6
  roundingAllowance := 100
  A_gt_one := by norm_num
  mu_pos := by norm_num
  delta_pos := by norm_num
  delta_lt_one := by norm_num
  nu_pos := by norm_num
  nu_lt_one := by norm_num
  lambda_pos := by norm_num
  lambda_lt_one := by norm_num
  mu_lt_support := by norm_num [patersonMu]
  tailError_nonneg := by norm_num [patersonTailError, patersonDelta1,
    patersonDelta2, patersonDelta3, patersonDelta4, patersonDelta5]
  splitError_nonneg := by norm_num [patersonDelta0]
  freshCost_nonneg := by norm_num [patersonAlpha0_eq, patersonDelta0,
    patersonTailError, patersonDelta1, patersonDelta2, patersonDelta3,
    patersonDelta4, patersonDelta5]
  minCapacity_pos := by norm_num
  roundingAllowance_nonneg := by norm_num
  geometric := by norm_num
  capacity := by norm_num
  tail := by norm_num [patersonTailError, patersonDelta1,
    patersonDelta2, patersonDelta3, patersonDelta4, patersonDelta5]
  first := by norm_num [patersonDelta0]
  firstRounded := by norm_num [patersonAlpha0_eq, patersonDelta0,
    patersonTailError, patersonDelta1, patersonDelta2, patersonDelta3,
    patersonDelta4, patersonDelta5]

/-- Capacity at level `l` after `t` ideal stages. -/
def capacity (p : Params) (root : ℚ) (t l : ℕ) : ℚ :=
  root * p.nu ^ t * p.A ^ l

theorem capacity_nonneg (p : Params) {root : ℚ} (hr : 0 ≤ root) (t l : ℕ) :
    0 ≤ capacity p root t l := by
  exact mul_nonneg (mul_nonneg hr (pow_nonneg p.nu_pos.le _))
    (pow_nonneg (by linarith [p.A_gt_one]) _)

theorem capacity_stage_succ (p : Params) (root : ℚ) (t l : ℕ) :
    capacity p root (t + 1) l = p.nu * capacity p root t l := by
  simp only [capacity, pow_succ]
  ring

theorem capacity_level_succ (p : Params) (root : ℚ) (t l : ℕ) :
    capacity p root t (l + 1) = p.A * capacity p root t l := by
  simp only [capacity, pow_succ]
  ring

/-- A safe integer stage coefficient for the first rounded-proof instance.
This is not a depth theorem: it certifies only the ideal shrink recurrence. -/
theorem roundedParams_shrink_seven :
    2 * roundedParams.A * roundedParams.nu ^ 7 < 1 := by
  norm_num [roundedParams]

/-- The fresh-source estimates produced by the separator fit the rounded
instance's budget. `r` represents the selected supported prefix/final cohort;
floor rounding loses at most one, and whole-bag rounding adds at most one
to its half size. The residual old-stranger term remains explicit. -/
theorem roundedParams_fresh_source {b half cohort old : ℚ}
    (hhalf : half ≤ b / (2 * roundedParams.A) + 1)
    (hcohort : patersonAlpha0 * half - 1 ≤ cohort)
    (hcohortMax : cohort ≤ half)
    (hold : old ≤ roundedParams.mu * b / roundedParams.A) :
    patersonTailError * old + half - cohort + patersonDelta0 * cohort ≤
      roundedParams.freshCost * b + roundedParams.roundingAllowance := by
  norm_num [roundedParams, patersonAlpha0_eq, patersonDelta0,
    patersonTailError, patersonDelta1, patersonDelta2, patersonDelta3,
    patersonDelta4, patersonDelta5] at *
  linarith

end Paterson.Bags
