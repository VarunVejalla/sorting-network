import AKS.Chvatal.StageKernel

/-! Exact rational checks for the candidate weighted-profile parameters.
This scratch file is deliberately outside the promoted package. -/

namespace Chvatal

def profileLevelWeight : Rat := 1 / 2
def profileRankWeight : Rat := 608000000
def profileProduct : Rat := profileLevelWeight * profileRankWeight

def profileRankOneGain : Rat :=
  profileLevelWeight / 64 + 4096 ^ 2 / profileProduct

def profileHigherRankGain : Rat :=
  invEpsF * profileProduct / 64 + 4096 ^ 2 / profileProduct

def profileLocalErrorRatio : Rat :=
  (((64 : Rat) - 1) * invMu * siblingFactor + invEpsB + slackCoeff) /
    (64 * invMu)

def profileCycleProduct : Rat := invEpsF * 4096 ^ 2 / 64

theorem profileRankOneGain_lt : profileRankOneGain < 64 / 1000 := by
  norm_num [profileRankOneGain, profileProduct, profileLevelWeight,
    profileRankWeight]

theorem profileHigherRankGain_lt : profileHigherRankGain < 111 / 1000 := by
  norm_num [profileHigherRankGain, profileProduct, profileLevelWeight,
    profileRankWeight, invEpsF]

theorem profileRankWeight_delta_lt_one :
    profileRankWeight * invDelta < 1 := by
  norm_num [profileRankWeight, invDelta]

theorem profileLocalErrorRatio_lt : profileLocalErrorRatio < 97 / 100 := by
  norm_num [profileLocalErrorRatio, siblingFactor, slackCoeff,
    invMu, invDelta, invEpsB]

theorem profileHigherRankPlusError_gt :
    1 < profileHigherRankGain + profileLocalErrorRatio := by
  norm_num [profileHigherRankGain, profileProduct, profileLevelWeight,
    profileRankWeight, profileLocalErrorRatio, siblingFactor, slackCoeff,
    invMu, invDelta, invEpsB, invEpsF]

theorem profileCycleProduct_gt_square :
    (11 / 200 : Rat) ^ 2 < profileCycleProduct := by
  norm_num [profileCycleProduct, invEpsF]

theorem profileCycle_weighted_max_barrier (x y : Rat)
    (hx : 0 <= x) (hy : 0 <= y)
    (hxy : profileCycleProduct <= x * y) :
    11 / 200 < max x y := by
  by_contra h
  have hx' : x <= 11 / 200 := le_trans (le_max_left x y) (le_of_not_gt h)
  have hy' : y <= 11 / 200 := le_trans (le_max_right x y) (le_of_not_gt h)
  have hxy' : x * y <= (11 / 200 : Rat) * (11 / 200 : Rat) :=
    mul_le_mul hx' hy' hy (by norm_num)
  have := profileCycleProduct_gt_square
  linarith

theorem profileError_leaves_less_than_cycle :
    1 < profileLocalErrorRatio + 11 / 200 := by
  norm_num [profileLocalErrorRatio, siblingFactor, slackCoeff,
    invMu, invDelta, invEpsB]

/-! The following candidate is a rank-profile replacement for the scalar
`mu * delta^r` envelope.  It is still a strict sub-envelope, but its
rank-zero local row has enough margin to absorb the current fixed error. -/

def profileGamma : Rat := 483 / 500
def profileScale : Rat := 122 / 125
def profileEffectiveDelta : Rat := invDelta * profileGamma

/-- Higher-rank transfer coefficient for `B_r = scale * mu * theta^r`. -/
def profileRankTransfer : Rat :=
  invEpsF / (64 * profileEffectiveDelta) + 4096 ^ 2 * profileEffectiveDelta

/-- Rank-zero variable coefficient, including the profile-sensitive sibling sum. -/
def profileRankZeroTransfer : Rat :=
  1 / 64 + 4096 ^ 2 * profileEffectiveDelta +
    (63 / 64) * 4096 *
      ((64 * 4096 * profileEffectiveDelta) /
        (1 - (64 * 4096 * profileEffectiveDelta) ^ 2))

/-- Fresh rank-zero error, normalized by `mu * capacity`. -/
def profileRankZeroError : Rat := (invEpsB + slackCoeff) / (64 * invMu)

theorem profileRankTransfer_lt_one : profileRankTransfer < 1 := by
  norm_num [profileRankTransfer, profileEffectiveDelta, profileGamma,
    invEpsF, invDelta]

theorem profileRankZero_closes :
    profileRankZeroTransfer * profileScale + profileRankZeroError <= profileScale := by
  norm_num [profileRankZeroTransfer, profileRankZeroError,
    profileEffectiveDelta, profileGamma, profileScale, siblingFactor,
    slackCoeff, invMu, invDelta, invEpsB]

theorem profileScale_lt_one : profileScale < 1 := by
  norm_num [profileScale]

end Chvatal
