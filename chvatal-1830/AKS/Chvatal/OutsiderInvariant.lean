module
/-
  # Chvatal §4 outsider invariant parameters and conditions (4.1)-(4.5)

  Source: V. Chvatal, DCS-TR-294 (1992), §4. Paper "outsider of order `r`" is `KBag.Strange (r+1)`.
-/

public import AKS.Chvatal.Scheduler
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Field.GeomSum
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

namespace Chvatal

open Finset

/-- Scalar parameters of the §4 outsider bound (paper §7: `mu = 2^{-30}`, `delta = 2^{-16}`, ...). -/
structure InvariantParams where
  mu : Rat
  delta : Rat
  epsB : Rat
  epsF : Rat
  deltaF : Rat
  epsStar : Rat
  hmu_pos : 0 < mu
  hdelta_pos : 0 < delta
  hdelta_lt : delta < 1
  hepsB_nonneg : 0 ≤ epsB
  hepsF_nonneg : 0 ≤ epsF
  hdeltaF_pos : 0 < deltaF
  hdeltaF_lt : deltaF < 1
  hepsStar_nonneg : 0 ≤ epsStar

namespace InvariantParams

variable (ip : InvariantParams)

theorem mu_nonneg : (0 : Rat) ≤ ip.mu := ip.hmu_pos.le

theorem delta_nonneg : (0 : Rat) ≤ ip.delta := ip.hdelta_pos.le

end InvariantParams

/-- Geometric factor of Lemmas 4.1-4.3: `δ k A² / (1 - δ² k² A²)`. -/
def siblingFactor (p : ScheduleParams) (ip : InvariantParams) : Rat :=
  ip.delta * (p.br : Rat) * p.A ^ 2 /
    (1 - ip.delta ^ 2 * (p.br : Rat) ^ 2 * p.A ^ 2)

/-- Lemma 4.2 residual `(k-1)Δ₂ - π/2` as a coefficient of `c`: `(A ν k - 2 A ν + 1) / (2 A² k²)`. -/
def slackCoeff (p : ScheduleParams) : Rat :=
  (p.A * p.nu * (p.br : Rat) - 2 * p.A * p.nu + 1) /
    (2 * p.A ^ 2 * (p.br : Rat) ^ 2)

/-- §4 (4.1): exceptional root separator quality `ε* ≤ μ/k`. -/
def Cond41 (p : ScheduleParams) (ip : InvariantParams) : Prop :=
  ip.epsStar ≤ ip.mu / (p.br : Rat)

/-- §4 (4.2): first-outsider budget through one stage. The last term `μ δ A k / ν` counts
    order-1 outsiders arriving from the `k` children (worst case, no fair density). -/
def Cond42 (p : ScheduleParams) (ip : InvariantParams) : Prop :=
  (ip.mu + (p.br - 1 : Rat) * ip.mu * siblingFactor p ip +
      slackCoeff p + ip.epsB) /
      (p.A * p.nu) +
    ip.mu * ip.delta * p.A * (p.br : Rat) / p.nu ≤ ip.mu

/-- §4 (4.3): `μ ≤ ν/(A k²)`. -/
def Cond43 (p : ScheduleParams) (ip : InvariantParams) : Prop :=
  ip.mu ≤ p.nu / (p.A * (p.br : Rat) ^ 2)

/-- §4 (4.4): fringe-count consequence involving `δF`. -/
def Cond44 (p : ScheduleParams) (ip : InvariantParams) : Prop :=
  ip.mu ≤ (1 / (2 * ip.deltaF)) *
    (p.A * p.nu * (p.br : Rat) - 1) / (p.A ^ 2 * (p.br : Rat) ^ 2)

/-- §4 (4.5): higher-order decay through one stage. -/
def Cond45 (p : ScheduleParams) (ip : InvariantParams) : Prop :=
  ip.epsF / (p.A * p.nu) + ip.delta ^ 2 * p.A * (p.br : Rat) / p.nu ≤
    ip.delta

/-- All five separator-quality / envelope inequalities of §4. -/
def SeparatorConds (p : ScheduleParams) (ip : InvariantParams) : Prop :=
  Cond41 p ip ∧ Cond42 p ip ∧ Cond43 p ip ∧ Cond44 p ip ∧ Cond45 p ip

theorem br_ge_one (p : ScheduleParams) : 1 ≤ p.br :=
  le_trans (by omega : 1 ≤ 2) p.hbr

end Chvatal
