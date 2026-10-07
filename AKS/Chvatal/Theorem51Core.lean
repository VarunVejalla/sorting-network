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

def aboveBottomRows (m n i : Nat) (_hi : i ≤ m) : Finset (Fin (m * n)) :=
  Finset.univ.filter fun w => w.val < (m - i) * n

def HasMatrixPropertyB {m n : Nat} (net : ComparatorNetwork (m * n))
    (epsB : ℝ) : Prop :=
  ∀ v : Equiv.Perm (Fin (m * n)),
    ∀ i : Nat, 1 ≤ i → i ≤ m →
      ((Finset.univ.filter fun pos : Fin (m * n) =>
          pos.val < (m - i) * n ∧
            m * n - i * n ≤ (net.exec (v : Fin (m * n) → Fin (m * n)) pos).val).card : ℝ) <
        (epsB / 2) * (m * n)

def HasMatrixPropertyF {m n : Nat} (net : ComparatorNetwork (m * n))
    (f : Nat) (_hf : f ≤ m) (deltaF epsF : ℝ) : Prop :=
  ∀ v : Equiv.Perm (Fin (m * n)),
    ∀ j : Nat, 0 < j → (j : ℝ) ≤ deltaF * (f * n) →
      ((Finset.univ.filter fun pos : Fin (m * n) =>
          pos.val < (m - f) * n ∧
            m * n - j ≤ (net.exec (v : Fin (m * n) → Fin (m * n)) pos).val).card : ℝ) <
        epsF * j

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

theorem params7Geometry_m_eq (f k b : Nat) (hf : Even f) (hf10 : 10 ≤ f)
    (hshape : 100 = 2 * f + k * b) :
    (params7Geometry f k b hf hf10 hshape).m = 100 := rfl

theorem params7Geometry_n_eq (f k b : Nat) (hf : Even f) (hf10 : 10 ≤ f)
    (hshape : 100 = 2 * f + k * b) :
    (params7Geometry f k b hf hf10 hshape).n = 16 := rfl

/-! **§7 paper-scale ordinary separator (`2^59 < m ≤ 2^60`, `n = 16`)** -/

/-- Upper end of the ordinary §7 scramble row range (`2^59 < m ≤ 2^60`). -/
def paperOrdinaryM : Nat := 2 ^ 60

/-- §7 ordinary separator quality `ε_B` from DCS-TR-294 §7 (not the Lemma 7.1 minimum `m = 100`). -/
noncomputable def paperOrdinaryEpsB : ℝ :=
  Real.sqrt (1 + 59 * Real.log 2) / (2 ^ 29 : ℝ)

/-- §7 root separator quality `ε_B` at `m = 2^79`. -/
noncomputable def paperRootEpsB : ℝ :=
  Real.sqrt (1 + 79 * Real.log 2) / (2 ^ 39 : ℝ)

/-- Paper ordinary scramble with `m = 2^60`, `f = 2^58`, `100 = 2·16 + 4·17`-style shape
    `2^60 = 2·2^58 + 1·2^59`. -/
def paperOrdinaryGeometry : ScrambleGeometry :=
  ScrambleGeometry.ofShape (2 ^ 60) 16 (2 ^ 59) (2 ^ 58) 1
    (by decide : 100 ≤ 2 ^ 60) (by norm_num) (by decide : 10 ≤ 2 ^ 58)
    (by decide : Even (2 ^ 58)) (by decide : 2 ^ 60 = 2 * 2 ^ 58 + 1 * 2 ^ 59)

/-- Representative `m = 2^59 + 1` inside `(2^59, 2^60]` with `f = 2^58`, `k = 1`, `b = 1`. -/
def paperOrdinaryGeometry_m2p59p1 : ScrambleGeometry :=
  ScrambleGeometry.ofShape (2 ^ 59 + 1) 16 1 (2 ^ 58) 1
    (by decide : 100 ≤ 2 ^ 59 + 1) (by norm_num) (by decide : 10 ≤ 2 ^ 58)
    (by decide : Even (2 ^ 58)) (by decide : 2 ^ 59 + 1 = 2 * 2 ^ 58 + 1 * 1)

def paperRootM : Nat := 2 ^ 79

/-- Root separator scramble at `m = 2^79` (shape witness `m = 2f` with `f = 2^78`, `k = 0`). -/
def paperRootGeometry : ScrambleGeometry :=
  ScrambleGeometry.ofShape (2 ^ 79) 16 0 (2 ^ 78) 0
    (by decide : 100 ≤ 2 ^ 79) (by norm_num) (by decide : 10 ≤ 2 ^ 78)
    (by decide : Even (2 ^ 78)) (by decide : 2 ^ 79 = 2 * 2 ^ 78 + 0 * 0)

/-- Convenient shape witness: `100 = 2·16 + 4·17`. -/
def params7Geometry_f16 : ScrambleGeometry :=
  params7Geometry 16 4 17 (by decide : Even 16) (by norm_num) (by norm_num)

/-- §7 Thm 5.1 budgets from `invariant7` (side conditions on `f` and `ε` inequalities remain external). -/
noncomputable def theorem51Params7 (g : ScrambleGeometry)
    (hepsB_lb : Real.sqrt (2 * (1 + Real.log g.m) / g.m) ≤ (invariant7.epsB : ℝ))
    (hepsF_ge_4e : (4 * Real.exp 1) / g.f ≤ (invariant7.epsF : ℝ))
    (hepsF_ge_lemma62 :
      epsF_lemma62_lb g.f (invariant7.deltaF : ℝ) ≤ (invariant7.epsF : ℝ)) :
    Theorem51Params g where
  epsB := invariant7.epsB
  deltaF := invariant7.deltaF
  epsF := invariant7.epsF
  hepsB_pos := by norm_num [invariant7]
  hepsB_lb := hepsB_lb
  hdeltaF_pos := by norm_num [invariant7]
  hdeltaF := by
    unfold invariant7
    norm_num
  hepsF_pos := by norm_num [invariant7]
  hepsF_ge_4e := hepsF_ge_4e
  hepsF_ge_lemma62 := hepsF_ge_lemma62

/-- §7 ordinary Thm 5.1 budgets: paper `ε_B`, `invariant7` `δ_F`/`ε_F` (matches DCS-TR-294 §7). -/
noncomputable def theorem51Params_paperOrdinary (g : ScrambleGeometry)
    (hepsB_lb : Real.sqrt (2 * (1 + Real.log g.m) / g.m) ≤ paperOrdinaryEpsB)
    (hepsF_ge_4e : (4 * Real.exp 1) / g.f ≤ (invariant7.epsF : ℝ))
    (hepsF_ge_lemma62 :
      epsF_lemma62_lb g.f (invariant7.deltaF : ℝ) ≤ (invariant7.epsF : ℝ)) :
    Theorem51Params g where
  epsB := paperOrdinaryEpsB
  deltaF := invariant7.deltaF
  epsF := invariant7.epsF
  hepsB_pos := by
    have h : (0 : ℝ) < Real.sqrt (1 + 59 * Real.log 2) / 2 ^ 29 := by positivity
    exact h
  hepsB_lb := hepsB_lb
  hdeltaF_pos := by norm_num [invariant7]
  hdeltaF := by unfold invariant7; norm_num
  hepsF_pos := by norm_num [invariant7]
  hepsF_ge_4e := hepsF_ge_4e
  hepsF_ge_lemma62 := hepsF_ge_lemma62

/-- §7 root Thm 5.1 budgets at `m = 2^79` with paper root `ε_B`. -/
noncomputable def theorem51Params_paperRoot (g : ScrambleGeometry)
    (hepsB_lb : Real.sqrt (2 * (1 + Real.log g.m) / g.m) ≤ paperRootEpsB)
    (hepsF_ge_4e : (4 * Real.exp 1) / g.f ≤ (invariant7.epsF : ℝ))
    (hepsF_ge_lemma62 :
      epsF_lemma62_lb g.f (invariant7.deltaF : ℝ) ≤ (invariant7.epsF : ℝ)) :
    Theorem51Params g where
  epsB := paperRootEpsB
  deltaF := invariant7.deltaF
  epsF := invariant7.epsF
  hepsB_pos := by
    have h : (0 : ℝ) < Real.sqrt (1 + 79 * Real.log 2) / 2 ^ 39 := by positivity
    exact h
  hepsB_lb := hepsB_lb
  hdeltaF_pos := by norm_num [invariant7]
  hdeltaF := by unfold invariant7; norm_num
  hepsF_pos := by norm_num [invariant7]
  hepsF_ge_4e := hepsF_ge_4e
  hepsF_ge_lemma62 := hepsF_ge_lemma62

noncomputable def chernoff_hepsB (m : Nat) : ℝ :=
  Real.sqrt (2 * (1 + Real.log m) / m)

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
