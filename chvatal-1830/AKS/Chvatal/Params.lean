module
/-
  # Chvatal §7 parameter instantiation

  Source: V. Chvatal, *Lecture Notes on the New AKS Sorting Network*,
  Rutgers DCS-TR-294 (1992), §7.

  Status: concrete `ScheduleParams` / `InvariantParams` at `k = 64`,
  `A = 4096`, `ν = 1/64`, with kernel-checked (4.1)–(4.5) after correcting
  `slackCoeff` to `(Aνk - 2Aν + 1)/(2A²k²)`. Depth accounting lives in
  `DepthSkeleton.lean`.
-/

public import AKS.Chvatal.OutsiderInvariant
public import AKS.Chvatal.DepthSkeleton
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity

@[expose] public section

namespace Chvatal

/-! **§7 schedule parameters** -/

/-- Paper §7: `k = 64`, `A = k² = 4096`, `ν = 1/k = 1/64`. -/
def params7 : ScheduleParams where
  br := 64
  A := 4096
  nu := 1 / 64
  hbr := by norm_num
  hA := by norm_num
  hnu_pos := by norm_num
  hnu_lt := by norm_num
  hAnu := by norm_num

/-! **§7 invariant parameters** -/

/-- Paper §7 scalars used by the outsider induction.
    `epsB` is a rational placeholder small enough for (4.3)–(4.5)-style budgets;
    the sharp (7.1) real bound is `chvatal71` in `DepthSkeleton`. -/
def invariant7 : InvariantParams where
  mu := 1 / 1073741824
  delta := 1 / 4294967296
  epsB := 1 / 1000000000000000
  epsF := 1 / 80000000
  deltaF := 128 / 4095
  epsStar := (1 / 1073741824) / 64
  hmu_pos := by norm_num
  hdelta_pos := by norm_num
  hdelta_lt := by norm_num
  hepsB_nonneg := by norm_num
  hepsF_nonneg := by norm_num
  hdeltaF_pos := by norm_num
  hdeltaF_lt := by norm_num
  hepsStar_nonneg := by norm_num

theorem cond41_params7 : Cond41 params7 invariant7 := by
  unfold Cond41 params7 invariant7
  norm_num

theorem cond43_params7 : Cond43 params7 invariant7 := by
  unfold Cond43 params7 invariant7
  norm_num

theorem cond44_params7 : Cond44 params7 invariant7 := by
  unfold Cond44 params7 invariant7
  norm_num

theorem cond45_params7 : Cond45 params7 invariant7 := by
  unfold Cond45 params7 invariant7
  norm_num

theorem cond42_params7 : Cond42 params7 invariant7 := by
  unfold Cond42 siblingFactor slackCoeff params7 invariant7
  norm_num

theorem siblingFactor_nonneg_params7 : (0 : Rat) ≤ siblingFactor params7 invariant7 := by
  unfold siblingFactor params7 invariant7
  positivity

theorem slackCoeff_nonneg_params7 : (0 : Rat) ≤ slackCoeff params7 := by
  unfold slackCoeff params7
  positivity

/-- Full (4.1)–(4.5) at the §7 parameters. -/
theorem separatorConds_params7 : SeparatorConds params7 invariant7 :=
  ⟨cond41_params7, cond42_params7, cond43_params7, cond44_params7,
    cond45_params7⟩

/-- §7 ordinary-separator budgets: paper `ε_B < 1.25·10⁻⁸` (rational upper bound), else `invariant7`.
    Suitable for PreferNon / outsider induction with paper-ordinary Thm 5.1 separators. -/
def invariant7_paperOrdinary : InvariantParams where
  mu := invariant7.mu
  delta := invariant7.delta
  epsB := 1 / 80000000
  epsF := invariant7.epsF
  deltaF := invariant7.deltaF
  epsStar := invariant7.epsStar
  hmu_pos := invariant7.hmu_pos
  hdelta_pos := invariant7.hdelta_pos
  hdelta_lt := invariant7.hdelta_lt
  hepsB_nonneg := by norm_num
  hepsF_nonneg := invariant7.hepsF_nonneg
  hdeltaF_pos := invariant7.hdeltaF_pos
  hdeltaF_lt := invariant7.hdeltaF_lt
  hepsStar_nonneg := invariant7.hepsStar_nonneg

theorem cond41_params7_paperOrdinary : Cond41 params7 invariant7_paperOrdinary := by
  unfold Cond41 params7 invariant7_paperOrdinary invariant7
  norm_num

theorem cond43_params7_paperOrdinary : Cond43 params7 invariant7_paperOrdinary := by
  unfold Cond43 params7 invariant7_paperOrdinary invariant7
  norm_num

theorem cond44_params7_paperOrdinary : Cond44 params7 invariant7_paperOrdinary := by
  unfold Cond44 params7 invariant7_paperOrdinary invariant7
  norm_num

theorem cond45_params7_paperOrdinary : Cond45 params7 invariant7_paperOrdinary := by
  unfold Cond45 params7 invariant7_paperOrdinary invariant7
  norm_num

theorem cond42_params7_paperOrdinary : Cond42 params7 invariant7_paperOrdinary := by
  unfold Cond42 siblingFactor slackCoeff params7 invariant7_paperOrdinary invariant7
  norm_num

theorem separatorConds_params7_paperOrdinary :
    SeparatorConds params7 invariant7_paperOrdinary :=
  ⟨cond41_params7_paperOrdinary, cond42_params7_paperOrdinary, cond43_params7_paperOrdinary,
    cond44_params7_paperOrdinary, cond45_params7_paperOrdinary⟩

/-- (4.1), (4.3), (4.4), (4.5) at the §7 parameters. -/
theorem conds_partial_params7 :
    Cond41 params7 invariant7 ∧ Cond43 params7 invariant7 ∧
      Cond44 params7 invariant7 ∧ Cond45 params7 invariant7 :=
  ⟨cond41_params7, cond43_params7, cond44_params7, cond45_params7⟩

end Chvatal
