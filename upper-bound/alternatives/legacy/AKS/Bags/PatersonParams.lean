module
/-
  # Paterson Parameters: Exact Shrink-Factor Arithmetic

  This file records a small kernel-checked part of Paterson's Section 8
  parameter calculation. It does not establish the halver, separator, or
  sorting-network bounds.
-/

public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

@[expose] public section

/-- Paterson's reported bag growth parameter `A = 4.75`. -/
def patersonA : ℚ := 19 / 4

/-- The five-level outer fringe parameter `λ = 2^(1-5)`. -/
def patersonLambda : ℚ := 1 / 16

/-- Stranger-tail parameter `μ` in Paterson's reported choice. -/
def patersonMu : ℚ := 1 / 50

/-- Geometric stranger-decay parameter `δ` in Paterson's reported choice. -/
def patersonDelta : ℚ := 1 / 57

/-- Error tolerances for the six restricted-halver levels, in order. -/
def patersonDelta0 : ℚ := 1 / 62
def patersonDelta1 : ℚ := 1 / 199
def patersonDelta2 : ℚ := 1 / 110
def patersonDelta3 : ℚ := 1 / 109
def patersonDelta4 : ℚ := 1 / 106
def patersonDelta5 : ℚ := 1 / 90

/-- Capacity multiplier per stage from Paterson's bag-capacity recurrence. -/
def patersonNu : ℚ :=
  2 * patersonLambda * patersonA + (1 - patersonLambda) / (2 * patersonA)

theorem patersonNu_eq : patersonNu = 421 / 608 := by
  norm_num [patersonNu, patersonLambda, patersonA]

theorem patersonNu_pos : 0 < patersonNu := by
  rw [patersonNu_eq]
  norm_num

theorem patersonNu_lt_one : patersonNu < 1 := by
  rw [patersonNu_eq]
  norm_num

/-- Under the natural identification of Seiferas's per-fringe `γ` with half
    Paterson's total outer-fringe fraction `λ`, Paterson's published capacity
    multiplier does not satisfy the current `Params.hC3` hypothesis. This
    records why the current bag theorem cannot simply be instantiated with the
    reported Paterson parameters. -/
theorem patersonNu_fails_current_hC3 :
    patersonNu < 4 * (1 / 32 : ℚ) * patersonA + 5 / (2 * patersonA) := by
  norm_num [patersonNu, patersonLambda, patersonA]

/-- The paper's bound on the surplus of correctly placed values in the parent bag. -/
def patersonEta : ℚ :=
  4 * patersonMu * patersonDelta * patersonA ^ 2 /
      (1 - 4 * patersonDelta ^ 2 * patersonA ^ 2) +
    1 / (4 * patersonA ^ 2 - 1)

theorem patersonEta_eq : patersonEta = 3907 / 89250 := by
  norm_num [patersonEta, patersonMu, patersonDelta, patersonA]

/-- The large supported fraction required by the first Paterson separator level. -/
def patersonAlpha0 : ℚ := 1 - patersonEta - 2 * patersonMu

theorem patersonAlpha0_eq : patersonAlpha0 = 81773 / 89250 := by
  norm_num [patersonAlpha0, patersonEta_eq, patersonMu]

theorem patersonAlpha0_pos : 0 < patersonAlpha0 := by
  rw [patersonAlpha0_eq]
  norm_num

theorem patersonAlpha0_lt_one : patersonAlpha0 < 1 := by
  rw [patersonAlpha0_eq]
  norm_num

/-- Paterson's entropy function, using natural logarithms. -/
noncomputable def patersonEntropy (x : ℝ) : ℝ :=
  -x * Real.log x - (1 - x) * Real.log (1 - x)

theorem patersonEntropy_eq_binEntropy (x : ℝ) : patersonEntropy x = Real.binEntropy x := by
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  simp only [Real.negMulLog_def, patersonEntropy]
  ring

/-- The real expression whose ceiling bounds the depth of an `(ε, α)`-halver.
    The source theorem applies for `0 < ε < 1/2` and `0 < α ≤ 1`. -/
noncomputable def patersonHalverDepthBound (α ε : ℚ) : ℝ :=
  1 + (patersonEntropy ((ε : ℝ) * α) +
      patersonEntropy ((1 - (ε : ℝ)) * α)) /
    (-((ε : ℝ) * α) * Real.log ((1 - (ε : ℝ)) * α))

/-- The real separator-depth expression before taking ceilings of the local
    restricted-halver depths. -/
noncomputable def patersonSeparatorRawDepth : ℝ :=
  max (patersonHalverDepthBound (2 * patersonMu) patersonDelta1)
      (patersonHalverDepthBound patersonAlpha0 patersonDelta0) +
    patersonHalverDepthBound (4 * patersonMu) patersonDelta2 +
    patersonHalverDepthBound (8 * patersonMu) patersonDelta3 +
    patersonHalverDepthBound (16 * patersonMu) patersonDelta4 +
    patersonHalverDepthBound (32 * patersonMu) patersonDelta5

/-- The real-valued asymptotic number of stages per `log₂ N`. -/
noncomputable def patersonStageRatio : ℝ :=
  Real.log (19 / 2 : ℝ) / -Real.log (421 / 608 : ℝ)

/-- A rational upper bound on Paterson's stage ratio. The proof reduces the
    logarithmic comparison to one exact rational power inequality. -/
theorem patersonStageRatio_lt : patersonStageRatio < 123 / 20 := by
  have hypos : (0 : ℝ) < 421 / 608 := by norm_num
  have hylt : (421 : ℝ) / 608 < 1 := by norm_num
  have hden : 0 < -Real.log (421 / 608 : ℝ) :=
    neg_pos.mpr (Real.log_neg hypos hylt)
  have hzpos : (0 : ℝ) < (19 / 2 : ℝ) ^ 20 * (421 / 608 : ℝ) ^ 123 := by
    positivity
  have hzlt : (19 / 2 : ℝ) ^ 20 * (421 / 608 : ℝ) ^ 123 < 1 := by
    norm_num
  have hzlog := Real.log_neg hzpos hzlt
  have hlog_eq :
      Real.log ((19 / 2 : ℝ) ^ 20 * (421 / 608 : ℝ) ^ 123) =
        20 * Real.log (19 / 2 : ℝ) + 123 * Real.log (421 / 608 : ℝ) := by
    rw [Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
    norm_num
  unfold patersonStageRatio
  rw [div_lt_iff₀ hden]
  nlinarith [hzlog, hlog_eq]

/-- With a separator depth of at most 989, the rationalized product of the
    separator depth and stage-ratio bounds is strictly below 6100. This is
    only the asymptotic product; additive boundary costs remain to be proved. -/
theorem patersonProduct989_lt_6100 :
    (989 : ℝ) * (123 / 20 : ℝ) < 6100 := by
  norm_num

/-! **Slack required by the interior stranger inequalities**

The paper reports approximate parameters. Substituting the displayed
reciprocals and the unadjusted fringe fraction literally fails both interior
inequalities. A slightly larger capacity multiplier repairs them; this is
also the direction required to accommodate integer rounding.
-/

/-- Total tail error across the five restricted-halver levels. -/
def patersonTailError : ℚ := patersonDelta1 + patersonDelta2 +
  patersonDelta3 + patersonDelta4 + patersonDelta5

/-- Left-hand side of Paterson's first-stranger inequality (5). -/
def patersonFirstStrangerCost : ℚ :=
  2 * patersonMu * patersonDelta * patersonA ^ 2 +
  2 * patersonMu * patersonDelta * patersonA ^ 2 /
    (1 - 4 * patersonDelta ^ 2 * patersonA ^ 2) +
  1 / (8 * patersonA ^ 2 - 2) + patersonMu + patersonDelta0 / 2

theorem patersonUnadjusted_tail_fails :
    patersonNu * patersonA * patersonDelta <
      2 * patersonA ^ 2 * patersonDelta ^ 2 + patersonTailError := by
  norm_num [patersonNu_eq, patersonA, patersonDelta, patersonTailError,
    patersonDelta1, patersonDelta2, patersonDelta3, patersonDelta4, patersonDelta5]

theorem patersonUnadjusted_first_fails :
    patersonNu * patersonMu * patersonA < patersonFirstStrangerCost := by
  norm_num [patersonNu_eq, patersonA, patersonMu, patersonDelta,
    patersonFirstStrangerCost, patersonDelta0]

/-- A rational capacity multiplier with strict slack in both interior bounds. -/
def patersonAdjustedNu : ℚ := 693 / 1000

/-- Fringe fraction corresponding to the adjusted capacity multiplier. -/
def patersonAdjustedLambda : ℚ := 11167 / 178500

theorem patersonAdjusted_capacity :
    patersonAdjustedNu = 2 * patersonAdjustedLambda * patersonA +
      (1 - patersonAdjustedLambda) / (2 * patersonA) := by
  norm_num [patersonAdjustedNu, patersonAdjustedLambda, patersonA]

theorem patersonAdjusted_tail :
    2 * patersonA ^ 2 * patersonDelta ^ 2 + patersonTailError <
      patersonAdjustedNu * patersonA * patersonDelta := by
  norm_num [patersonAdjustedNu, patersonA, patersonDelta, patersonTailError,
    patersonDelta1, patersonDelta2, patersonDelta3, patersonDelta4, patersonDelta5]

theorem patersonAdjusted_first :
    patersonFirstStrangerCost < patersonAdjustedNu * patersonMu * patersonA := by
  norm_num [patersonAdjustedNu, patersonA, patersonMu, patersonDelta,
    patersonFirstStrangerCost, patersonDelta0]

/-- The corrected multiplier still permits fewer than 6.15 stages per log₂ N
in the ideal capacity recurrence. -/
theorem patersonAdjustedStageRatio_lt :
    Real.log (19 / 2 : ℝ) / -Real.log (693 / 1000 : ℝ) < 123 / 20 := by
  have hden : 0 < -Real.log (693 / 1000 : ℝ) :=
    neg_pos.mpr (Real.log_neg (by norm_num) (by norm_num))
  have hzpos : (0 : ℝ) < (19 / 2 : ℝ) ^ 20 * (693 / 1000 : ℝ) ^ 123 := by
    positivity
  have hzlt : (19 / 2 : ℝ) ^ 20 * (693 / 1000 : ℝ) ^ 123 < 1 := by norm_num
  have hzlog := Real.log_neg hzpos hzlt
  have hlog_eq :
      Real.log ((19 / 2 : ℝ) ^ 20 * (693 / 1000 : ℝ) ^ 123) =
        20 * Real.log (19 / 2 : ℝ) + 123 * Real.log (693 / 1000 : ℝ) := by
    rw [Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
    norm_num
  rw [div_lt_iff₀ hden]
  nlinarith [hzlog, hlog_eq]

end
