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

end Chvatal
