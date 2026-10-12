import UpperBoundContrib.Candidate
import UpperBoundContrib.Best

/-! # Improvement gate (informational for the baseline)

Compiles only if the claimed constant is *strictly* below the accepted `currentBest`. CI reports this
target separately: the baseline candidate (claimed = currentBest) intentionally does not satisfy it. -/

theorem claimed_lt_currentBest :
    UpperBoundContrib.claimed < UpperBoundContrib.currentBest := by
  unfold UpperBoundContrib.claimed UpperBoundContrib.currentBest
  norm_num
