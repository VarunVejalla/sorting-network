module

/- Shared Thm 5.1 geometry (`m = 2f + kb`), `ε`-parameters and the Lemma 6.1 closing numeric. -/

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp

@[expose] public section

namespace Chvatal

structure ScrambleGeometry where
  m : Nat
  n : Nat
  b : Nat
  f : Nat
  k : Nat
  hm : 100 ≤ m
  hn : 16 ≤ n
  hf : 10 ≤ f
  hfeven : Even f
  hshape : m = 2 * f + k * b

def ScrambleGeometry.ofShape (m n b f k : Nat) (hm : 100 ≤ m) (hn : 16 ≤ n) (hf : 10 ≤ f)
    (hfeven : Even f) (hshape : m = 2 * f + k * b) : ScrambleGeometry :=
  ⟨m, n, b, f, k, hm, hn, hf, hfeven, hshape⟩

def Scramble (m n : Nat) : Type := Fin m → Equiv.Perm (Fin n)

structure Theorem51Params (g : ScrambleGeometry) where
  epsB : ℝ
  deltaF : ℝ
  epsF : ℝ
  hepsB_pos : 0 < epsB
  hepsB_lb : Real.sqrt (2 * (1 + Real.log g.m) / g.m) ≤ epsB

theorem scrambleGeometry_hn (g : ScrambleGeometry) : 0 < g.n := by have := g.hn; omega

/-- §7 ordinary separator quality `ε_B` (DCS-TR-294 §7). -/
noncomputable def paperOrdinaryEpsB : ℝ := Real.sqrt (2 * (1 + 58 * Real.log 2) / (2 ^ 58 : ℝ))

/-- §7 root separator quality `ε_B` at `m = 2^79`. -/
noncomputable def paperRootEpsB : ℝ := Real.sqrt (1 + 79 * Real.log 2) / (2 ^ 39 : ℝ)

noncomputable def lemma61_failFactor (m n : Nat) : ℝ :=
  (2 * (m + 1) / (Real.exp 1 * m)) ^ n

theorem lemma61_failFactor_lt_one_hundredth
    (m n : Nat) (hm : 100 ≤ m) (hn : 16 ≤ n) :
    lemma61_failFactor m n < 1 / 100 := by
  have hm' : (100 : ℝ) ≤ m := by exact_mod_cast hm
  have he : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have hb : 2 * ((m : ℝ) + 1) / (Real.exp 1 * m) ≤ 149 / 200 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg (sub_nonneg.2 he.le) (by linarith : (0 : ℝ) ≤ m)]
  calc lemma61_failFactor m n ≤ (149 / 200 : ℝ) ^ n := pow_le_pow_left₀ (by positivity) hb n
    _ ≤ (149 / 200 : ℝ) ^ 16 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
    _ < 1 / 100 := by norm_num

end Chvatal
