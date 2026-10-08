module
/-
  # Module A — §7 numeric side conditions at `m = 100`, `n = 16`

  Kernel-checked fringe geometry and `jMax ≤ 48` for `params7Geometry` shapes.
  Chernoff floors for Lemmas 6.1–6.2 at `(100,16,f=16)` and the mismatch with
  `invariant7` (sized for §4 outsider / large-`f` separators via `chvatal71`).
-/

public import AKS.Chvatal.Lemma61
public import AKS.Chvatal.Lemma62
public import AKS.Chvatal.Params
public import AKS.Chvatal.Theorem51Core
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith

set_option maxHeartbeats 800000

@[expose] public section

namespace Chvatal

/-! **Log bounds for `(100,16)` Chernoff floors** -/

private theorem exp5_gt_100 : (100 : ℝ) < Real.exp (5 : ℝ) := by
  have hlow : (100 : ℝ) < (2718 / 1000 : ℝ) ^ 5 := by norm_num
  have h2728 : (2718 / 1000 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hmid : (2718 / 1000 : ℝ) ^ 5 < Real.exp 1 ^ 5 := by gcongr
  have hpow : Real.exp 1 ^ 5 = Real.exp (5 : ℝ) := by
    rw [← Real.exp_nat_mul, mul_one, Nat.cast_ofNat]
  linarith

private theorem log100_lt_five : Real.log (100 : ℝ) < 5 := by
  have hlog := Real.log_lt_log (by norm_num) exp5_gt_100
  rwa [Real.log_exp] at hlog

private theorem chernoff_hepsB_m100_lt_half :
    Real.sqrt (2 * (1 + Real.log (100 : ℝ)) / 100) < (1 / 2 : ℝ) := by
  have hlog := log100_lt_five
  have hinside : 2 * (1 + Real.log (100 : ℝ)) / 100 < (12 / 100 : ℝ) := by
    linarith
  have h12 : Real.sqrt (12 / 100 : ℝ) < (1 / 2 : ℝ) := by
    have h := Real.sqrt_lt_sqrt (by norm_num) (by norm_num : (12 / 100 : ℝ) < (1 / 4 : ℝ))
    rwa [show Real.sqrt (1 / 4 : ℝ) = (1 / 2 : ℝ) from by
      rw [show (1 / 4 : ℝ) = (1 / 2 : ℝ) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at h
  have hmono := Real.sqrt_lt_sqrt (by positivity) hinside
  exact hmono.trans h12

theorem moduleA_chernoff_hepsB_m100_le_half :
    Real.sqrt (2 * (1 + Real.log (100 : ℝ)) / 100) ≤ (1 / 2 : ℝ) :=
  le_of_lt chernoff_hepsB_m100_lt_half

theorem invariant7_epsB_lt_chernoff_hepsB_m100 :
    (invariant7.epsB : ℝ) < Real.sqrt (2 * (1 + Real.log (100 : ℝ)) / 100) := by
  have hlo : (1 / 10 : ℝ) < Real.sqrt (2 * (1 + Real.log (100 : ℝ)) / 100) := by
    rw [Real.lt_sqrt (by norm_num)]
    linarith [Real.log_pos (by norm_num : (1 : ℝ) < 100)]
  have heps : (invariant7.epsB : ℝ) < (1 / 10 : ℝ) := by
    unfold invariant7
    norm_num
  linarith

theorem not_invariant7_hepsB_m100 :
    ¬ Real.sqrt (2 * (1 + Real.log (100 : ℝ)) / 100) ≤ (invariant7.epsB : ℝ) := by
  intro h
  exact not_le_of_gt invariant7_epsB_lt_chernoff_hepsB_m100 h

/-! **Chernoff floor vs `invariant7.epsB` (log-scale `m`, not paper `m = 100`)** -/

/-- Necessary scale: if `√(2/m) ≤ ε` then `m ≥ 2/ε²` (for `ε = invariant7.epsB` this is `≈ 2·10^30`). -/
theorem chernoff_loose_floor_le_eps {m : Nat} {eps : ℝ} (hm : 1 ≤ m) (heps : 0 < eps)
    (h : Real.sqrt (2 / m) ≤ eps) : (2 / eps ^ 2 : ℝ) ≤ m := by
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le (Nat.zero_lt_one) hm)
  have hsq : (2 : ℝ) / m ≤ eps ^ 2 := by
    have hp : 0 ≤ (2 : ℝ) / m := by positivity
    calc (2 : ℝ) / m = (Real.sqrt (2 / m)) ^ 2 := (Real.sq_sqrt hp).symm
      _ ≤ eps ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
  have hmul : (2 : ℝ) ≤ (m : ℝ) * eps ^ 2 := by
    simpa [mul_comm] using (div_le_iff₀ hmpos).1 hsq
  have heps2pos : 0 < eps ^ 2 := sq_pos_of_pos heps
  have hle : (2 / eps ^ 2 : ℝ) ≤ (m : ℝ) := (div_le_iff₀ heps2pos).2 hmul
  exact_mod_cast hle

theorem not_chernoff_hepsB_le_invariant7_at_m100 :
    ¬ Real.sqrt (2 * (1 + Real.log (100 : ℝ)) / 100) ≤ (invariant7.epsB : ℝ) :=
  not_invariant7_hepsB_m100

/-- Chernoff-scale `m` for `invariant7.epsB` is astronomically above paper `m = 100`
    (`chernoff_loose_floor_le_eps`: `√(2/m) ≤ epsB` ⇒ `m ≥ 2/epsB²`). -/
theorem invariant7_chernoff_loose_m_gt_100 :
    (100 : ℝ) < 2 / (invariant7.epsB : ℝ) ^ 2 := by
  unfold invariant7
  norm_num

private theorem hepsWorst_f16_lt_300 :
    Real.sqrt
        ((1 + Real.log (100 : ℝ)) * 16 * fringeRowCount 100 16 (by decide : Even 16) * 16 / 2) <
      (300 : ℝ) := by
  rw [fringeRowCount_m100_f16]
  have h1 : (1 + Real.log (100 : ℝ)) < (6 : ℝ) := by linarith [log100_lt_five]
  have hmul' :
      (1 + Real.log (100 : ℝ)) * 16 * 92 * 16 < (6 : ℝ) * 16 * 92 * 16 := by
    simpa using mul_lt_mul_of_pos_right h1 (by norm_num : 0 < (16 * 92 * 16 : ℝ))
  have hinside :
      (1 + Real.log (100 : ℝ)) * 16 * 92 * 16 / 2 < (6 : ℝ) * 16 * 92 * 16 / 2 :=
    div_lt_div_of_pos_right hmul' (by norm_num : 0 < (2 : ℝ))
  have hnum : (6 : ℝ) * 16 * 92 * 16 / 2 = (70656 : ℝ) := by norm_num
  have h70656 : Real.sqrt (70656 : ℝ) < (300 : ℝ) := by
    have h300 : Real.sqrt (90000 : ℝ) = (300 : ℝ) := by
      rw [show (90000 : ℝ) = (300 : ℝ) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [← h300]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num : (70656 : ℝ) < (90000 : ℝ))
  calc
    Real.sqrt ((1 + Real.log (100 : ℝ)) * 16 * 92 * 16 / 2)
        < Real.sqrt ((6 : ℝ) * 16 * 92 * 16 / 2) :=
          Real.sqrt_lt_sqrt (by positivity) hinside
    _ = Real.sqrt (70656 : ℝ) := by rw [hnum]
    _ < 300 := h70656

theorem moduleA_hepsWorst_f16_le_300 :
    Real.sqrt
        ((1 + Real.log (100 : ℝ)) * 16 * fringeRowCount 100 16 (by decide : Even 16) * 16 / 2) ≤
      (300 : ℝ) :=
  le_of_lt hepsWorst_f16_lt_300

theorem invariant7_epsF_lt_hepsWorst_f16 :
    (invariant7.epsF : ℝ) <
      Real.sqrt
        ((1 + Real.log (100 : ℝ)) * 16 * fringeRowCount 100 16 (by decide : Even 16) * 16 / 2) := by
  rw [fringeRowCount_m100_f16]
  have hinside : (1 : ℝ) < (1 + Real.log (100 : ℝ)) * 16 * 92 * 16 / 2 := by
    have hlog : (0 : ℝ) < Real.log 100 := Real.log_pos (by norm_num)
    linarith
  have hsqrt : (1 : ℝ) < Real.sqrt ((1 + Real.log (100 : ℝ)) * 16 * 92 * 16 / 2) := by
    rw [Real.lt_sqrt (by linarith)]
    linarith
  have hinv : (invariant7.epsF : ℝ) < (1 : ℝ) := by
    unfold invariant7
    norm_num
  linarith

theorem not_invariant7_hepsWorst_f16 :
    ¬ Real.sqrt
          ((1 + Real.log (100 : ℝ)) * 16 * fringeRowCount 100 16 (by decide : Even 16) * 16 / 2) ≤
        (invariant7.epsF : ℝ) := by
  intro h
  exact not_le_of_gt invariant7_epsF_lt_hepsWorst_f16 h

theorem moduleA_hepsF_ge_4e_f16 : (4 * Real.exp 1) / 16 ≤ (300 : ℝ) := by
  have h4e : (4 * Real.exp 1) / 16 < (11 / 10 : ℝ) := by
    have he : Real.exp 1 < (28 / 10 : ℝ) := by
      linarith [Real.exp_one_lt_d9]
    have : (4 * Real.exp 1) / 16 < (4 * (28 / 10 : ℝ)) / 16 := by
      gcongr
    linarith
  linarith

theorem not_invariant7_hepsF_ge_4e_f16 :
    ¬ (4 * Real.exp 1) / 16 ≤ (invariant7.epsF : ℝ) := by
  intro h
  have h4e : (1 / 10 : ℝ) < (4 * Real.exp 1) / 16 := by linarith [Real.exp_one_gt_d9]
  have heps : (invariant7.epsF : ℝ) < (1 / 10 : ℝ) := by
    unfold invariant7
    norm_num
  linarith

private theorem moduleA_deltaF_eq : (invariant7.deltaF : ℝ) = (128 / 4095 : ℝ) := by
  unfold invariant7
  norm_num

private theorem moduleA_logDenom_pos :
    (0 : ℝ) < Real.log (0.12 / (Real.exp 1 * (128 / 4095 : ℝ))) := by
  apply Real.log_pos
  have he : Real.exp 1 < (28 / 10 : ℝ) := by linarith [Real.exp_one_lt_d9]
  have hden : Real.exp 1 * (128 / 4095 : ℝ) < (28 / 10 : ℝ) * (128 / 4095 : ℝ) := by gcongr
  have hden' : (28 / 10 : ℝ) * (128 / 4095 : ℝ) < (12 / 100 : ℝ) := by norm_num
  have hlt : Real.exp 1 * (128 / 4095 : ℝ) < (12 / 100 : ℝ) := lt_trans hden hden'
  have hpos : (0 : ℝ) < Real.exp 1 * (128 / 4095 : ℝ) := by positivity
  have hfrac : (1 : ℝ) < (12 / 100 : ℝ) / (Real.exp 1 * (128 / 4095 : ℝ)) := by
    rw [one_lt_div hpos]
    exact hlt
  simpa [show (0.12 : ℝ) = (12 / 100 : ℝ) from by norm_num] using hfrac

private theorem moduleA_log_one_pt_two_gt_tenth : (1 / 10 : ℝ) < Real.log (12 / 10 : ℝ) := by
  have h := Real.lt_log_one_add_of_pos (by norm_num : (0 : ℝ) < (2 / 10 : ℝ))
  rw [show (1 : ℝ) + 2 / 10 = (12 / 10 : ℝ) from by ring] at h
  exact lt_trans (by norm_num : (1 / 10 : ℝ) < 2 * (2 / 10) / (2 / 10 + 2)) h

private theorem moduleA_logDenom_gt :
    (1 / 10 : ℝ) < Real.log (0.12 / (Real.exp 1 * (128 / 4095 : ℝ))) := by
  rw [show (0.12 : ℝ) = (12 / 100 : ℝ) from by norm_num]
  set frac : ℝ := (12 / 100 : ℝ) / (Real.exp 1 * (128 / 4095 : ℝ))
  have h12 : (12 / 10 : ℝ) < frac := by
    have hden : (12 / 10 : ℝ) * (Real.exp 1 * (128 / 4095 : ℝ)) < (12 / 100 : ℝ) := by
      have he : Real.exp 1 < (28 / 10 : ℝ) := by linarith [Real.exp_one_lt_d9]
      have := mul_lt_mul_of_pos_right he (by norm_num : (0 : ℝ) < (128 / 4095 : ℝ))
      norm_num at this ⊢
      linarith
    rw [lt_div_iff₀ (by positivity)]
    exact hden
  have hlog12 : Real.log (12 / 10 : ℝ) < Real.log frac :=
    Real.log_lt_log (by norm_num) h12
  exact moduleA_log_one_pt_two_gt_tenth.trans hlog12

private theorem moduleA_logNumer_f16_lt :
    Real.log (3 * Real.exp 5 * (16 : ℝ)) < (11 : ℝ) := by
  have hsplit :
      Real.log (3 * Real.exp 5 * (16 : ℝ)) = Real.log 3 + 5 + Real.log 16 := by
    calc
      Real.log (3 * Real.exp 5 * (16 : ℝ)) =
          Real.log (3 * Real.exp 5) + Real.log 16 :=
        Real.log_mul (by positivity) (by norm_num)
      _ = Real.log 3 + Real.log (Real.exp 5) + Real.log 16 := by
        rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne']
      _ = Real.log 3 + 5 + Real.log 16 := by rw [Real.log_exp]
  have hln3 : Real.log (3 : ℝ) < (2 : ℝ) := by
    have h3 : (3 : ℝ) < Real.exp 2 := by
      have := Real.add_one_lt_exp (by norm_num : (2 : ℝ) ≠ 0)
      linarith [Real.exp_pos 2]
    have hlog : Real.log 3 < Real.log (Real.exp 2) :=
      (Real.log_lt_log_iff (by norm_num) (Real.exp_pos 2)).2 h3
    rw [Real.log_exp] at hlog
    exact hlog
  have hln16 : Real.log (16 : ℝ) < (4 : ℝ) := by
    have hpow : Real.log (16 : ℝ) = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = (2 : ℝ) ^ 4 from by norm_num]
      simpa using Real.log_pow (by norm_num : (0 : ℝ) < 2) 4
    rw [hpow]
    nlinarith [Real.log_two_lt_d9]
  linarith [hsplit, hln3, hln16]

private theorem moduleA_epsF_lemma62_bracket_f16_lt :
    (1 : ℝ) + Real.log (3 * Real.exp 5 * (16 : ℝ)) /
        Real.log (0.12 / (Real.exp 1 * (invariant7.deltaF : ℝ))) < (120 : ℝ) := by
  rw [moduleA_deltaF_eq]
  have hL := moduleA_logDenom_gt
  have hLpos : (0 : ℝ) < Real.log (0.12 / (Real.exp 1 * (128 / 4095 : ℝ))) :=
    moduleA_logDenom_pos
  have hratio :
      Real.log (3 * Real.exp 5 * (16 : ℝ)) /
          Real.log (0.12 / (Real.exp 1 * (128 / 4095 : ℝ))) <
        (110 : ℝ) := by
    have hmul :
        Real.log (3 * Real.exp 5 * (16 : ℝ)) <
          (110 : ℝ) * Real.log (0.12 / (Real.exp 1 * (128 / 4095 : ℝ))) := by
      have h110' : (11 : ℝ) < (110 : ℝ) * Real.log (0.12 / (Real.exp 1 * (128 / 4095 : ℝ))) := by
        have h110pos : (110 : ℝ) * (1 / 10 : ℝ) < (110 : ℝ) * Real.log (0.12 / (Real.exp 1 * (128 / 4095 : ℝ))) :=
          mul_lt_mul_of_pos_left hL (by norm_num : (0 : ℝ) < 110)
        linarith
      linarith [moduleA_logNumer_f16_lt, h110']
    exact (div_lt_iff₀ hLpos).2 hmul
  have h111 : (1 : ℝ) + Real.log (3 * Real.exp 5 * (16 : ℝ)) /
        Real.log (0.12 / (Real.exp 1 * (128 / 4095 : ℝ))) < (111 : ℝ) := by linarith [hratio]
  exact lt_trans h111 (by norm_num : (111 : ℝ) < 120)

theorem moduleA_epsF_lemma62_lb_le_300 :
    epsF_lemma62_lb 16 (invariant7.deltaF : ℝ) ≤ (300 : ℝ) := by
  have hbr := le_of_lt moduleA_epsF_lemma62_bracket_f16_lt
  have hcore :
      epsF_lemma62_lb 16 (invariant7.deltaF : ℝ) ≤ (120 / 7 : ℝ) := by
    unfold epsF_lemma62_lb
    have hcoef : (2 : ℝ) / ((16 - 2 : ℕ) : ℝ) = (1 / 7 : ℝ) := by norm_num
    calc
      (2 : ℝ) / ((16 : ℝ) - 2) *
          (1 + Real.log (3 * Real.exp 5 * (16 : ℝ)) /
            Real.log (0.12 / (Real.exp 1 * (invariant7.deltaF : ℝ)))) =
          (1 / 7 : ℝ) *
            (1 + Real.log (3 * Real.exp 5 * (16 : ℝ)) /
              Real.log (0.12 / (Real.exp 1 * (invariant7.deltaF : ℝ)))) := by
        have hcast : (2 : ℝ) / ((16 : ℝ) - 2) = (2 : ℝ) / ((16 - 2 : ℕ) : ℝ) := by
          congr 1
          norm_num
        rw [hcast, hcoef]
      _ ≤ (120 / 7 : ℝ) := by
        have hle := mul_le_mul_of_nonneg_left hbr (by norm_num : (0 : ℝ) ≤ 1 / 7)
        rw [show (1 / 7 : ℝ) * (120 : ℝ) = (120 / 7 : ℝ) from by ring] at hle
        exact hle
  exact hcore.trans (by norm_num : (120 / 7 : ℝ) ≤ (300 : ℝ))

/-- Kernel-checked: `epsF_lemma62_lb` ≈ 3.81 at `(δ_F,f) = (128/4095,16)` (well below `300`). -/
structure ModuleA_epsF_lemma62_Certificate where
  bound : epsF_lemma62_lb 16 (invariant7.deltaF : ℝ) ≤ (300 : ℝ)

theorem moduleA_epsF_lemma62_Certificate : ModuleA_epsF_lemma62_Certificate :=
  ⟨moduleA_epsF_lemma62_lb_le_300⟩

/-- §4 outsider induction scalars matching `theorem51Params_moduleA_f16` (not `invariant7`). -/
noncomputable def moduleA_invariantF16 (_C : ModuleA_epsF_lemma62_Certificate) : InvariantParams :=
  { mu := invariant7.mu
    delta := invariant7.delta
    epsB := 1 / 2
    epsF := 300
    deltaF := invariant7.deltaF
    epsStar := invariant7.epsStar
    hmu_pos := invariant7.hmu_pos
    hdelta_pos := invariant7.hdelta_pos
    hdelta_lt := invariant7.hdelta_lt
    hepsB_nonneg := by norm_num
    hepsF_nonneg := by norm_num
    hdeltaF_pos := invariant7.hdeltaF_pos
    hdeltaF_lt := invariant7.hdeltaF_lt
    hepsStar_nonneg := invariant7.hepsStar_nonneg }

theorem not_moduleA_invariantF16_eq_invariant7_epsB
    (C : ModuleA_epsF_lemma62_Certificate) :
    (moduleA_invariantF16 C).epsB ≠ invariant7.epsB := by
  simp [moduleA_invariantF16, invariant7]

/-! **§4 budget incompatibility (Chernoff-scale `ε` vs `invariant7`)** -/

theorem not_cond42_epsB_half_at_params7 :
    ¬ Cond42 params7 { invariant7 with
      epsB := (1 / 2 : Rat)
      hepsB_nonneg := by norm_num } := by
  unfold Cond42 siblingFactor slackCoeff params7 invariant7
  norm_num

theorem not_cond45_epsF_three_hundred_at_params7 :
    ¬ Cond45 params7 { invariant7 with
      epsF := (300 : Rat)
      hepsF_nonneg := by norm_num } := by
  unfold Cond45 params7 invariant7
  norm_num

theorem not_separatorConds_params7_moduleA_invariantF16 (C : ModuleA_epsF_lemma62_Certificate) :
    ¬ SeparatorConds params7 (moduleA_invariantF16 C) := by
  intro h
  exact not_cond42_epsB_half_at_params7 h.2.1

/-! **Shape consequences for `params7Geometry`** -/

theorem params7Geometry_f_le_50 {f k b : Nat} (hshape : 100 = 2 * f + k * b) : f ≤ 50 := by
  omega

theorem params7Geometry_f_le_97 {f k b : Nat} (hshape : 100 = 2 * f + k * b) :
    f ≤ 97 :=
  (params7Geometry_f_le_50 hshape).trans (by norm_num : (50 : Nat) ≤ 97)

theorem params7Geometry_hf2 {f : Nat} (hf10 : 10 ≤ f) : 2 ≤ f :=
  le_trans (by norm_num : (2 : Nat) ≤ 10) hf10

theorem params7Geometry_hfm {f k b : Nat} (hshape : 100 = 2 * f + k * b) : f ≤ 100 := by
  omega

theorem params7Geometry_hfpos {f : Nat} (hf10 : 10 ≤ f) : 0 < f :=
  Nat.lt_of_lt_of_le (by norm_num : (0 : Nat) < 10) hf10

theorem params7Geometry_hmF {f k b : Nat} (hf : Even f) (_hf10 : 10 ≤ f)
    (hshape : 100 = 2 * f + k * b) :
    1 ≤ fringeRowCount 100 f hf := by
  have hm : f / 2 < 100 := by
    have hf50 : f ≤ 50 := params7Geometry_f_le_50 hshape
    have : f / 2 ≤ 25 := by omega
    exact lt_of_le_of_lt this (by norm_num : (25 : Nat) < 100)
  exact one_le_fringeRowCount hf hm

theorem params7Geometry_f16_hmF :
    1 ≤ fringeRowCount 100 16 (by decide : Even 16) := by
  rw [fringeRowCount_m100_f16]
  norm_num

theorem params7Geometry_f16_hjMax48 :
    lemma62_jMax (invariant7.deltaF : ℝ) 16 16 ≤ 48 :=
  lemma62_jMax_params7_f16_le_48 (by norm_num)

theorem params7Geometry_hjMax48 {f k b : Nat} (hf : Even f) {deltaF : ℝ}
    (hshape : 100 = 2 * f + k * b) (hdeltaF : deltaF = invariant7.deltaF) :
    lemma62_jMax deltaF f 16 ≤ 48 := by
  rw [hdeltaF]
  exact lemma62_jMax_params7_f16_le_48 (params7Geometry_f_le_97 hshape)

/-! **Viable `Theorem51Params` for Module A at `f = 16`** -/

/-- Chernoff-scale §5–§6 budgets at `(100,16,f=16)`; not usable as `invariant7` for §4. -/
noncomputable def theorem51Params_moduleA_f16 (C : ModuleA_epsF_lemma62_Certificate) :
    Theorem51Params params7Geometry_f16 where
  epsB := (1 / 2 : ℝ)
  deltaF := invariant7.deltaF
  epsF := (300 : ℝ)
  hepsB_pos := by norm_num
  hepsB_lb := moduleA_chernoff_hepsB_m100_le_half
  hdeltaF_pos := by norm_num [invariant7]
  hdeltaF := by unfold invariant7; norm_num
  hepsF_pos := by norm_num
  hepsF_ge_4e := moduleA_hepsF_ge_4e_f16
  hepsF_ge_lemma62 := C.bound

/-- Same with kernel-checked `epsF_lemma62_lb ≤ 300`. -/
noncomputable def theorem51Params_moduleA_f16_discharged :
    Theorem51Params params7Geometry_f16 :=
  theorem51Params_moduleA_f16 moduleA_epsF_lemma62_Certificate

/-- Legacy: global `TotalColumnOnesLeN` (false for all monotone `c` at `m = 100`). -/
structure ModuleAParams7_f16Chernoff where
  htotal : TotalColumnOnesLeN 100 16

/-- B-side: only fringe/`hepsWorst`/`hclose` residuals; B Chernoff uses `DecodeMatrixClassObligation`. -/
structure ModuleAParams7_f16DecodeResidual where
  hepsB : Real.sqrt (2 * (1 + Real.log (100 : ℝ)) / 100) ≤ (invariant7.epsB : ℝ)
  havg : AvgRowOnesLeOne 100 16
  hepsWorst :
    Real.sqrt
        ((1 + Real.log 100) * 16 * fringeRowCount 100 16 (by decide : Even 16) * 16 / 2) ≤
      (invariant7.epsF : ℝ)
  hepsF_ge_4e : (4 * Real.exp 1) / 16 ≤ (invariant7.epsF : ℝ)
  hepsF_ge_lemma62 :
    epsF_lemma62_lb 16 (invariant7.deltaF : ℝ) ≤ (invariant7.epsF : ℝ)

structure ModuleAParams7_f16Residual where
  htotal : TotalColumnOnesLeN 100 16
  hepsB : Real.sqrt (2 * (1 + Real.log (100 : ℝ)) / 100) ≤ (invariant7.epsB : ℝ)
  hepsWorst :
    Real.sqrt
        ((1 + Real.log 100) * 16 * fringeRowCount 100 16 (by decide : Even 16) * 16 / 2) ≤
      (invariant7.epsF : ℝ)
  hepsF_ge_4e : (4 * Real.exp 1) / 16 ≤ (invariant7.epsF : ℝ)
  hepsF_ge_lemma62 :
    epsF_lemma62_lb 16 (invariant7.deltaF : ℝ) ≤ (invariant7.epsF : ℝ)

/-- Residual for `theorem51Params_moduleA_f16`: F-side certificate only; B-side is
    `DecodeMatrixClassObligation.standard` (pipeline class — see `SortedColumnDecode`). -/
structure ModuleAParams7_f16ModuleA where
  havg : AvgRowOnesLeOne 100 16
  epsF_lemma62 : ModuleA_epsF_lemma62_Certificate

/-- Legacy bundle (equivalent to `ModuleAParams7_f16ModuleA` via `TotalColumnOnesLeN_iff`). -/
structure ModuleAParams7_f16ModuleALegacy where
  havg : AvgRowOnesLeOne 100 16
  epsF_lemma62 : ModuleA_epsF_lemma62_Certificate

def ModuleAParams7_f16ModuleA.of_legacy (L : ModuleAParams7_f16ModuleALegacy) :
    ModuleAParams7_f16ModuleA where
  havg := L.havg
  epsF_lemma62 := L.epsF_lemma62

/-! **Fail-fraction accounting (Lemma 6.1 / 6.2 union factors)** -/

theorem lemma62_failFactor_thirty_lt_fortyFour_hundredths :
    lemma62_failFactor Lemma62InnerBound.thirty.x < 44 / 100 := by
  rw [lemma62_failFactor_thirty_eq]
  norm_num

theorem moduleA_global_failFraction_add_lt_one {m n : Nat} (hm : 100 ≤ m) (hn : 16 ≤ n) :
    lemma61_failFactor m n + lemma62_failFactor Lemma62InnerBound.thirty.x < 1 := by
  have hα := lemma61_failFactor_lt_one_hundredth m n hm hn
  have hβ := lemma62_failFactor_lt_fortyNine_hundredth Lemma62InnerBound.thirty
  linarith

theorem moduleA_global_failFraction_add_lt_one_m100 :
    lemma61_failFactor 100 16 + lemma62_failFactor (3 / 10 : ℝ) < 1 :=
  moduleA_global_failFraction_add_lt_one (by norm_num) (by norm_num)

private theorem exp1_lt_2728281829 : Real.exp 1 < (2728281829 / 1000000000 : ℝ) := by
  linarith [Real.exp_one_lt_d9]

/-- Crude pipeline B factor at `m = 100`: `100 · lemma61_failFactor` is not tiny (≈ 0.9). -/
theorem lemma61_failFactor_pipeline_100_16_gt_four_fifths :
    (4 / 5 : ℝ) < lemma61_failFactor_pipeline 100 16 := by
  unfold lemma61_failFactor_pipeline
  set rat := (2 * (101 : ℝ) / ((2728281829 / 1000000000 : ℝ) * 100))
  set actual := (2 * (101 : ℝ) / (Real.exp 1 * 100))
  have hm : (0 : ℝ) < (100 : ℝ) := by norm_num
  have hratio : (4 / 5 : ℝ) < (100 : ℝ) * rat ^ 16 := by
    dsimp [rat]
    norm_num
  have hden : Real.exp 1 * 100 < (2728281829 / 1000000000 : ℝ) * 100 :=
    mul_lt_mul_of_pos_right exp1_lt_2728281829 hm
  have hpos : (0 : ℝ) < 2 * (101 : ℝ) := by norm_num
  have hbase : rat ^ 16 ≤ actual ^ 16 := by
    dsimp [rat, actual]
    have hfrac : rat ≤ actual := le_of_lt (div_lt_div_of_pos_left hpos (by positivity) hden)
    have hrfr0 : (0 : ℝ) ≤ rat := by dsimp [rat]; positivity
    exact pow_le_pow_left₀ hrfr0 hfrac 16
  have hprod : (100 : ℝ) * rat ^ 16 ≤ (100 : ℝ) * actual ^ 16 :=
    mul_le_mul_of_nonneg_left hbase (by norm_num)
  have hfac : lemma61_failFactor 100 16 = actual ^ 16 := by
    unfold lemma61_failFactor
    norm_num [actual]
  exact lt_of_lt_of_le hratio (by simpa [hfac] using hprod)

end Chvatal
