module
/-
  Shared Thm 5.1 geometry, matrix Properties B/F, and Lemma 6.1 closing numeric.
  Split from `Theorem51.lean` so `Lemma61` / `MatrixBridge` can import without a
  cycle when the full witness uses `SortScrambleSortPack`.
-/

public import AKS.Chvatal.DepthSkeleton
public import AKS.Chvatal.Params
public import AKS.Sort.Defs
public import AKS.Sort.Depth
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

/-! **Scramble geometry** -/

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

def ScrambleGeometry.wires (g : ScrambleGeometry) : Nat := g.m * g.n

/-- Generic Thm 5.1 / §7 scramble shape `m = 2f + kb` with paper minima `100 ≤ m`, `16 ≤ n`. -/
def ScrambleGeometry.ofShape (m n b f k : Nat) (hm : 100 ≤ m) (hn : 16 ≤ n) (hf : 10 ≤ f)
    (hfeven : Even f) (hshape : m = 2 * f + k * b) : ScrambleGeometry where
  m := m
  n := n
  b := b
  f := f
  k := k
  hm := hm
  hn := hn
  hf := hf
  hfeven := hfeven
  hshape := hshape

def Scramble (m n : Nat) : Type := Fin m → Equiv.Perm (Fin n)




noncomputable def epsF_lemma62_lb (f : Nat) (deltaF : ℝ) : ℝ :=
  (2 : ℝ) / (f - 2) *
    (1 + Real.log (3 * Real.exp 5 * f) / Real.log (0.12 / (Real.exp 1 * deltaF)))

structure Theorem51Params (g : ScrambleGeometry) where
  epsB : ℝ
  deltaF : ℝ
  epsF : ℝ
  hepsB_pos : 0 < epsB
  hepsB_lb : Real.sqrt (2 * (1 + Real.log g.m) / g.m) ≤ epsB
  hdeltaF_pos : 0 < deltaF
  hdeltaF : deltaF ≤ 1 / 25
  hepsF_pos : 0 < epsF
  hepsF_ge_4e : (4 * Real.exp 1) / g.f ≤ epsF
  hepsF_ge_lemma62 : epsF_lemma62_lb g.f deltaF ≤ epsF

theorem scrambleGeometry_hn (g : ScrambleGeometry) : 0 < g.n :=
  Nat.lt_of_lt_of_le (by decide : 0 < 16) g.hn

/-! **§7 scramble geometry (`m = 100`, `n = 16`)** -/

/-- Paper minima `m×n = 100×16` with `m = 2f + kb` (Thm 5.1 / §7 ordinary separator template). -/
def params7Geometry (f k b : Nat) (hf : Even f) (hf10 : 10 ≤ f)
    (hshape : 100 = 2 * f + k * b) : ScrambleGeometry :=
  ScrambleGeometry.ofShape 100 16 b f k (by norm_num) (by norm_num) hf10 hf hshape



/-! **§7 paper-scale ordinary separator (`2^59 < m ≤ 2^60`, `n = 16`)** -/

/-- Upper end of the ordinary §7 scramble row range (`2^59 < m ≤ 2^60`). -/
def paperOrdinaryM : Nat := 2 ^ 60

/-- §7 ordinary separator quality `ε_B` from DCS-TR-294 §7 (not the Lemma 7.1 minimum `m = 100`). -/
noncomputable def paperOrdinaryEpsB : ℝ :=
  Real.sqrt (1 + 59 * Real.log 2) / (2 ^ 29 : ℝ)

/-- §7 root separator quality `ε_B` at `m = 2^79`. -/
noncomputable def paperRootEpsB : ℝ :=
  Real.sqrt (1 + 79 * Real.log 2) / (2 ^ 39 : ℝ)



def paperRootM : Nat := 2 ^ 79


/-- Convenient shape witness: `100 = 2·16 + 4·17`. -/
def params7Geometry_f16 : ScrambleGeometry :=
  params7Geometry 16 4 17 (by decide : Even 16) (by norm_num) (by norm_num)





noncomputable def lemma61_failFactor (m n : Nat) : ℝ :=
  (2 * (m + 1) / (Real.exp 1 * m)) ^ n

theorem lemma61_failFactor_lt_one_hundredth
    (m n : Nat) (hm : 100 ≤ m) (hn : 16 ≤ n) :
    lemma61_failFactor m n < 1 / 100 := by
  unfold lemma61_failFactor
  have hmpos : (0 : ℝ) < m := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : Nat) < 100) hm)
  have hratio : ((m : ℝ) + 1) / m ≤ (101 : ℝ) / 100 := by
    have hm' : (100 : ℝ) ≤ m := by exact_mod_cast hm
    field_simp [hmpos.ne']
    linarith
  have hform :
      2 * ((m : ℝ) + 1) / (Real.exp 1 * m) =
        (2 / Real.exp 1) * (((m : ℝ) + 1) / m) := by
    field_simp [hmpos.ne']
  have hform' :
      2 * (101 : ℝ) / (Real.exp 1 * 100) =
        (2 / Real.exp 1) * (101 / 100) := by
    field_simp
  have hbase :
      2 * ((m : ℝ) + 1) / (Real.exp 1 * m) ≤
        2 * 101 / (Real.exp 1 * 100) := by
    rw [hform, hform']
    exact mul_le_mul_of_nonneg_left hratio (by positivity)
  have he : (2712 / 1000 : ℝ) < Real.exp 1 :=
    LT.lt.trans (by norm_num : (2712 / 1000 : ℝ) < 2.7182818283) Real.exp_one_gt_d9
  have hnum : 2 * (101 : ℝ) / (Real.exp 1 * 100) < (149 / 200 : ℝ) := by
    have hlt :
        2 * (101 : ℝ) / (Real.exp 1 * 100) <
          2 * 101 / ((2712 / 1000) * 100) := by
      refine div_lt_div_of_pos_left (by positivity) (by positivity) ?_
      exact mul_lt_mul_of_pos_right he (by positivity)
    have hval : 2 * (101 : ℝ) / ((2712 / 1000) * 100) = (202000 : ℝ) / 271200 := by
      norm_num
    have h149 : (202000 : ℝ) / 271200 < 149 / 200 := by norm_num
    linarith
  have hbase_nn : (0 : ℝ) ≤ 2 * ((m : ℝ) + 1) / (Real.exp 1 * m) := by
    positivity
  have hnum_nn : (0 : ℝ) ≤ 2 * (101 : ℝ) / (Real.exp 1 * 100) := by
    positivity
  have hpow_base :
      (2 * ((m : ℝ) + 1) / (Real.exp 1 * m)) ^ n ≤
        (2 * 101 / (Real.exp 1 * 100)) ^ n :=
    pow_le_pow_left₀ hbase_nn hbase n
  have hpow_mid :
      (2 * 101 / (Real.exp 1 * 100) : ℝ) ^ n ≤ (149 / 200 : ℝ) ^ n :=
    pow_le_pow_left₀ hnum_nn hnum.le n
  have hpow_n : (149 / 200 : ℝ) ^ n ≤ (149 / 200 : ℝ) ^ 16 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
  have h16 : (149 / 200 : ℝ) ^ 16 < 1 / 100 := by norm_num
  calc (2 * ((m : ℝ) + 1) / (Real.exp 1 * m)) ^ n
      ≤ (2 * 101 / (Real.exp 1 * 100)) ^ n := hpow_base
    _ ≤ (149 / 200 : ℝ) ^ n := hpow_mid
    _ ≤ (149 / 200 : ℝ) ^ 16 := hpow_n
    _ < 1 / 100 := h16

end Chvatal
