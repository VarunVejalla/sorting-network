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

/-- §7: root separator (6320) + ordinary rounds (3660 each) + final sorters (903). -/
def totalDepth (d : ℕ) : ℕ := 6320 + ordinaryRounds d * 3660 + 903

/-- §7 closed form. At `d = 7` there are zero ordinary rounds. -/
theorem totalDepth_eq (d : ℕ) (hd : 7 ≤ d) :
    totalDepth d = 10980 * d - 69637 := by
  unfold totalDepth ordinaryRounds
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

/-! ## §7 instantiations at k = 64, A = 4096, ν = 1/64 -/

/-- One sharp logarithm bound drives both irrational checks below:
`ln 2 < 0.7`, from the checked-in dyadic enclosure. -/
theorem chvatal_log2_lt : Real.log 2 < (0.7 : ℝ) := by
  have h := (Paterson.log_dyadic_bounds (show (0 : ℝ) < 2 by norm_num) 0).2
  have hu : Paterson.logUpper (2 : ℝ) 0 < 0.7 := by
    norm_num [Paterson.logUpper, Paterson.logApprox, Paterson.logError,
      Finset.sum_range_succ]
  linarith

/-- §7 (4.3): `μ ≤ ν/(A·k²)`, in fact an equality. -/
theorem chvatal43 : (1 / 1073741824 : ℚ) ≤ (1 / 64) / (4096 * 64 ^ 2) := by
  norm_num

/-- §7 (4.4): fringe-count consequence for the first-level contract. -/
theorem chvatal44 : (1 / 1073741824 : ℚ) ≤
    1 / (2 * (128 / 4095)) * (4096 * (1 / 64) * 64 - 1) / (4096 ^ 2 * 64 ^ 2) := by
  norm_num

/-- §7 (4.5): first-stranger decay through one stage. -/
theorem chvatal45 : (1 / 80000000 : ℚ) / (4096 * (1 / 64)) +
    (1 / 4294967296) ^ 2 * 4096 * 64 / (1 / 64) ≤ 1 / 4294967296 := by
  norm_num

/-- §7 (7.2): the `εF` budget. -/
theorem chvatal72 : (1 / 80000000 : ℚ) ≤
    1 / 4 * (1 / 64 ^ 4) * (4 * 64 - 1) / (4 * 64) := by
  norm_num

/-- §5/§7: `δF = 128/4095` satisfies the `δF ≤ 1/25` requirement. -/
theorem chvatal_deltaF : (128 / 4095 : ℚ) ≤ 1 / 25 := by
  norm_num

/-- §7 right-hand side of (7.1) at `k = 64`. -/
noncomputable def rhs71 : ℝ :=
  1 / 4 * (1 / 64 ^ 4) *
    ((16 * 64 ^ 6 - 32 * 64 ^ 4 - 2 * 64 ^ 2 + 64 + 2) / (16 * 64 ^ 6 - 64 ^ 2))

/-- §7 (4.1): the exceptional root separator quality `ε* ≤ μ/k`.
Suffices: `√(1 + 79·ln2) ≤ 8`, i.e. `ln 2 ≤ 63/79`. -/
theorem chvatal41 :
    Real.sqrt (1 + 79 * Real.log 2) / 2 ^ 39 < (1 / 1073741824) / 64 := by
  have hlog := chvatal_log2_lt
  have hnn : (0 : ℝ) ≤ 1 + 79 * Real.log 2 := by
    have hpos := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
    linarith
  have h64 : (1 : ℝ) + 79 * Real.log 2 < 64 := by linarith
  have h8 : Real.sqrt (1 + 79 * Real.log 2) < 8 := by
    have h := Real.sqrt_lt_sqrt hnn h64
    rwa [show Real.sqrt (64 : ℝ) = 8 from by
      rw [show (64 : ℝ) = 8 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at h
  have hCinv : (0 : ℝ) < ((2 ^ 39)⁻¹) := by positivity
  calc Real.sqrt (1 + 79 * Real.log 2) / 2 ^ 39
      < 8 / 2 ^ 39 := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_lt_mul_of_pos_right h8 hCinv
    _ = (1 / 1073741824) / 64 := by norm_num

/-- §7 (7.1): the `εB` budget. Suffices: `1 + 59·ln2 ≤ 2^58·R²`
via `ln 2 < 0.7`, since `2^58·R² = 64·Q² > 63.9`. -/
theorem chvatal71 :
    Real.sqrt (1 + 59 * Real.log 2) / 2 ^ 29 ≤ rhs71 := by
  have hlog := chvatal_log2_lt
  have hR : (42.3 : ℝ) ≤ (2 ^ 29) ^ 2 * rhs71 ^ 2 := by
    unfold rhs71
    norm_num
  have h59 : (1 : ℝ) + 59 * Real.log 2 ≤ (2 ^ 29) ^ 2 * rhs71 ^ 2 := by linarith
  have hRnn : (0 : ℝ) ≤ (2 ^ 29) * rhs71 := by
    unfold rhs71
    norm_num
  have hsq : Real.sqrt (1 + 59 * Real.log 2) ≤ (2 ^ 29) * rhs71 := by
    have e : ((2 ^ 29) * rhs71) ^ 2 = (2 ^ 29) ^ 2 * rhs71 ^ 2 := by ring
    have hle : (1 : ℝ) + 59 * Real.log 2 ≤ ((2 ^ 29) * rhs71) ^ 2 := by
      rw [e]; exact h59
    have h := Real.sqrt_le_sqrt hle
    rw [Real.sqrt_sq hRnn] at h
    exact h
  have hCinv : (0 : ℝ) < ((2 ^ 29)⁻¹) := by positivity
  calc Real.sqrt (1 + 59 * Real.log 2) / 2 ^ 29
      ≤ ((2 ^ 29) * rhs71) / 2 ^ 29 := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right hsq hCinv.le
    _ = rhs71 := by
        have h29 : ((2 : ℝ) ^ 29) ≠ 0 := by positivity
        field_simp

end Chvatal
