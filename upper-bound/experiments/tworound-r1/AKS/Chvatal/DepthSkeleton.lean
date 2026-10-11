module

public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! # §7 depth arithmetic: total depth `6320 + (3d-21)·3540 + 903` (DCS-TR-294 §7). -/

@[expose] public section

namespace Chvatal

/-- §7: ordinary separator rounds for `N = 64^d` (`d ≥ 7`). -/
def ordinaryRounds (d : ℕ) : ℕ := 3 * d - 21

/-- §7 paper depth of the root separator stage. -/
def rootSeparatorPaperDepth : ℕ := 6320

/-- §7 paper depth of one ordinary separator round. -/
def ordinaryStagePaperDepth : ℕ := 3540

/-- §7 paper depth of the final sorter layer. -/
def finalSorterPaperDepth : ℕ := 903

/-- §7: root separator + ordinary rounds + final sorters. -/
def totalDepth (d : ℕ) : ℕ :=
  rootSeparatorPaperDepth + ordinaryRounds d * ordinaryStagePaperDepth + finalSorterPaperDepth

theorem totalDepth_real (d : ℕ) (hd : 7 ≤ d) :
    (totalDepth d : ℝ) = 1770 * (6 * (d : ℝ)) - 67117 := by
  have heq : totalDepth d = 10620 * d - 67117 := by
    unfold totalDepth ordinaryRounds rootSeparatorPaperDepth ordinaryStagePaperDepth
      finalSorterPaperDepth
    omega
  rw [heq, Nat.cast_sub (by omega)]
  push_cast
  ring

/-- Padding to the next power of 64 costs at most 6 binary logs, giving the `-56497` form. -/
theorem totalDepth_logb_le {n d : ℕ} (hd : 7 ≤ d) (hclog : Nat.clog 64 n = d)
    (hn : 1 < n) :
    (totalDepth d : ℝ) ≤ 1770 * Real.logb 2 (n : ℝ) - 56497 := by
  have hltN : 64 ^ (d - 1) < n := by
    have h := Nat.pow_pred_clog_lt_self (show 1 < 64 by norm_num) hn
    rwa [hclog] at h
  have hlt : (2 : ℝ) ^ (6 * (d - 1)) < (n : ℝ) := by
    rw [pow_mul]
    exact_mod_cast hltN
  have hlog := Real.logb_lt_logb (show (1 : ℝ) < 2 by norm_num) (by positivity) hlt
  rw [Real.logb_pow, Real.logb_self_eq_one (show (1 : ℝ) < 2 by norm_num), mul_one] at hlog
  have htot := totalDepth_real d hd
  have hd1 : ((d - 1 : ℕ) : ℝ) = d - 1 := by rw [Nat.cast_sub (by omega)]; simp
  push_cast [hd1] at hlog
  linarith

end Chvatal
