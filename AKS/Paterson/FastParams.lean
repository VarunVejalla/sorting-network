module

public import AKS.Paterson.BagParams

/-! # Rounded parameters with room for the 7000 target

The older working instance used shrink factor 0.72. A tighter constant
rounding allowance permits 0.707 at minimum capacity 300000. The rational
power certificate gives an ideal stage coefficient of 13/2, leaving a
separate budget for root sorts.
These are arithmetic certificates, not a completed global sorting theorem.
-/

@[expose] public section

namespace Paterson.Bags

def fastParams : Params where
  A := 19 / 4
  mu := 199 / 10000
  delta := 1 / 57
  nu := 707 / 1000
  lambda := 3811 / 59500
  support := patersonMu
  tailError := patersonTailError
  splitError := patersonDelta0
  freshCost := (1 - patersonAlpha0 + patersonDelta0) / (2 * (19 / 4)) +
    patersonTailError * (199 / 10000) / (19 / 4)
  minCapacity := 300000
  roundingAllowance := 10
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

/-- Two batches of logarithmic growth are dominated by 13 shrink steps. -/
theorem fastParams_shrink_certificate :
    (2 * fastParams.A) ^ 2 * fastParams.nu ^ 13 < 1 := by
  norm_num [fastParams]

/-- Scalar depth accounting if the scheduler supplies the advertised stage
and root-sort counts. The constant term must still be accounted for. -/
theorem fastParams_depth_budget :
    (989 : ℚ) * (13 / 2) + 561 < 7000 := by norm_num

end Paterson.Bags
