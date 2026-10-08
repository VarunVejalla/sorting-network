module

public import AKS.Bags.PatersonNumerics
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! # Chvátal Phase 0: §7 depth arithmetic and parameter checks

Source: V. Chvátal, *Lecture Notes on the New AKS Sorting Network*,
Rutgers DCS-TR-294 (1992), checked in as `docs/dcs-tr-294.pdf`.

Status: arithmetic skeleton ONLY. The network construction (§3), the outsider
invariant (§4), and the scramble-separator existence (§5-6) are NOT formalized
here. The depth budget below is therefore a bound on the paper's *accounting*,
not a sorting theorem. Separator quality appears only as the concrete §7
numerical claims (4.1), (4.3), (4.4), (4.5), (7.1), (7.2), transcribed from the
printed formulas; assembling (4.2) from (7.1) belongs to the scheduler phase.
-/

@[expose] public section

namespace Chvatal

/-! ## §7 depth accounting: 6320 + (3d-21)·3660 + 903 -/

/-- §7: ordinary separator rounds for `N = 64^d`. Meaningful for `d ≥ 7`. -/
def ordinaryRounds (d : ℕ) : ℕ := 3 * d - 21

/-- §7 paper depth for the root separator stage. -/
def rootSeparatorPaperDepth : ℕ := 6320

/-- §7 paper depth for one ordinary separator round. -/
def ordinaryStagePaperDepth : ℕ := 3660

/-- §7 paper depth for the final sorter layer. -/
def finalSorterPaperDepth : ℕ := 903

/-- §7: root separator (6320) + ordinary rounds (3660 each) + final sorters (903). -/
def totalDepth (d : ℕ) : ℕ :=
  rootSeparatorPaperDepth + ordinaryRounds d * ordinaryStagePaperDepth + finalSorterPaperDepth

/-- Largest `d` with `bitonicDepthBudget (6·d) ≤ totalDepth d`.
    Full-wire Batcher on `64^d` meets the §7 total budget exactly on `7 ≤ d ≤ 603`;
    past this range Batcher is too deep for the padded 1830 form. -/
def batcherFitsTotalDepthMax : ℕ := 603

/-- Per-stage depth budgets matching §7 paper accounting. -/
structure StageDepthBudget (d : ℕ) where
  rootSepDepth : ℕ
  ordinaryStageDepth : ℕ
  finalSorterDepth : ℕ
  hroot : rootSepDepth ≤ rootSeparatorPaperDepth
  hord : ordinaryStageDepth ≤ ordinaryStagePaperDepth
  hfinal : finalSorterDepth ≤ finalSorterPaperDepth

/-- §7 paper budgets at equality (6320, 3660, 903). -/
def StageDepthBudget.ofPaper (d : ℕ) : StageDepthBudget d where
  rootSepDepth := rootSeparatorPaperDepth
  ordinaryStageDepth := ordinaryStagePaperDepth
  finalSorterDepth := finalSorterPaperDepth
  hroot := le_rfl
  hord := le_rfl
  hfinal := le_rfl

theorem StageDepthBudget.depth_sum_le (d : ℕ) (B : StageDepthBudget d) :
    B.rootSepDepth + ordinaryRounds d * B.ordinaryStageDepth + B.finalSorterDepth ≤
      totalDepth d := by
  unfold totalDepth rootSeparatorPaperDepth ordinaryStagePaperDepth finalSorterPaperDepth
  have hmid :
      ordinaryRounds d * B.ordinaryStageDepth ≤
        ordinaryRounds d * ordinaryStagePaperDepth :=
    Nat.mul_le_mul_left _ B.hord
  exact add_le_add (add_le_add B.hroot hmid) B.hfinal

/-- §7 closed form. At `d = 7` there are zero ordinary rounds. -/
theorem totalDepth_eq (d : ℕ) (hd : 7 ≤ d) :
    totalDepth d = 10980 * d - 69637 := by
  unfold totalDepth ordinaryRounds rootSeparatorPaperDepth ordinaryStagePaperDepth
    finalSorterPaperDepth
  omega

theorem totalDepth_real (d : ℕ) (hd : 7 ≤ d) :
    (totalDepth d : ℝ) = 1830 * (6 * (d : ℝ)) - 69637 := by
  have heq := totalDepth_eq d hd
  have hge : 69637 ≤ 10980 * d := by omega
  rw [heq, Nat.cast_sub hge]
  push_cast
  ring

theorem clog64_pow_cast (e : ℕ) : ((64 ^ e : ℕ) : ℝ) = (2 : ℝ) ^ (6 * e) := by
  have h64 : (64 : ℝ) = 2 ^ 6 := by norm_num
  have h1 : ((64 ^ e : ℕ) : ℝ) = (64 : ℝ) ^ e := by norm_cast
  rw [h1, h64]
  exact (pow_mul 2 6 e).symm

theorem logb64pow (e : ℕ) : Real.logb 2 ((64 ^ e : ℕ) : ℝ) = 6 * e := by
  rw [clog64_pow_cast, Real.logb_pow,
    Real.logb_self_eq_one (show (1 : ℝ) < 2 by norm_num)]
  push_cast
  ring

/-- Sharp per-power form: `1830·lg(64^d) - 69637`. -/
theorem totalDepth_pow_eq (d : ℕ) (hd : 7 ≤ d) :
    (totalDepth d : ℝ) = 1830 * Real.logb 2 ((64 ^ d : ℕ) : ℝ) - 69637 := by
  rw [logb64pow, totalDepth_real d hd]

/-- Padding to the next power of 64 costs at most 6 binary logs, giving the
`-58657` form. Pure arithmetic; no network is constructed. -/
theorem totalDepth_logb_le {n d : ℕ} (hd : 7 ≤ d) (hclog : Nat.clog 64 n = d)
    (hn : 1 < n) :
    (totalDepth d : ℝ) ≤ 1830 * Real.logb 2 (n : ℝ) - 58657 := by
  have hltN : 64 ^ (d - 1) < n := by
    have h := Nat.pow_pred_clog_lt_self (show 1 < 64 by norm_num) hn
    rwa [hclog] at h
  have hlt : (2 : ℝ) ^ (6 * (d - 1)) < (n : ℝ) := by
    rw [← clog64_pow_cast]
    exact_mod_cast hltN
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ (6 * (d - 1)) := by positivity
  have hlog := Real.logb_lt_logb (show (1 : ℝ) < 2 by norm_num) h2pos hlt
  rw [Real.logb_pow, Real.logb_self_eq_one (show (1 : ℝ) < 2 by norm_num),
    mul_one] at hlog
  have htot := totalDepth_real d hd
  have hsplit : ((6 * d : ℕ) : ℝ) = ((6 * (d - 1) : ℕ) : ℝ) + 6 := by
    have h : 6 * d = 6 * (d - 1) + 6 := by omega
    rw [h]
    push_cast
    ring
  have ed : (6 : ℝ) * (d : ℝ) = ((6 * d : ℕ) : ℝ) := by push_cast; ring
  linarith

end Chvatal
