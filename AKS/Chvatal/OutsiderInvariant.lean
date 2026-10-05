module
/-
  # Chvatal §4 outsider invariant (abstract separator quality)

  Source: V. Chvatal, *Lecture Notes on the New AKS Sorting Network*,
  Rutgers DCS-TR-294 (1992), §4. Checked in as `docs/dcs-tr-294.pdf`.

  Status: states the invariant `P`, the separator-quality hypotheses (4.1)-(4.5),
  and the purity conclusion (Lemma 4.5). Algebraic cores of Lemmas 4.1-4.4 live
  in `OutsiderLemmas.lean` under abstract stage-count / separator hypotheses;
  Phase 2 supplies concrete `εB`/`εF`/`δF`/`ε*` and stage dynamics.

  Indexing note. Paper "outsider of order `r`" means: not native to the bag's
  ancestor `r` levels up (order `0` = not native to the bag itself). Our
  `KBag.Strange` uses Seiferas-style indexing: `Strange (r+1)` is the paper's
  order-`r` outsider (`Strange 1` = order 0).
-/

public import AKS.Chvatal.Scheduler
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Field.GeomSum
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

namespace Chvatal

open Finset

/-! **Invariant parameters** -/

/-- Scalar parameters controlling the §4 outsider bound and separator budgets.
    Paper §7 defaults: `mu = 2^{-30}`, `delta = 2^{-16}`, etc. -/
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

/-! **Conditions (4.1)-(4.5)** -/

/-- Geometric factor appearing in Lemmas 4.1-4.3:
    `δ k A² / (1 - δ² k² A²)`. -/
def siblingFactor (p : ScheduleParams) (ip : InvariantParams) : Rat :=
  ip.delta * (p.br : Rat) * p.A ^ 2 /
    (1 - ip.delta ^ 2 * (p.br : Rat) ^ 2 * p.A ^ 2)

/-- Lemma 4.2 residual from `(k-1)Δ₂ - π/2`, as a coefficient of `c`:
    `(A ν k - 2 A ν + 1) / (2 A² k²)`.

    (The paper's displayed form places this whole fraction after `(k-1)Δ₁`;
    OCR of the notes can look like an unscaled `Aνk - 2Aν` sum.) -/
def slackCoeff (p : ScheduleParams) : Rat :=
  (p.A * p.nu * (p.br : Rat) - 2 * p.A * p.nu + 1) /
    (2 * p.A ^ 2 * (p.br : Rat) ^ 2)

/-- §4 (4.1): exceptional root separator quality `ε* ≤ μ/k`. -/
def Cond41 (p : ScheduleParams) (ip : InvariantParams) : Prop :=
  ip.epsStar ≤ ip.mu / (p.br : Rat)

/-- §4 (4.2): first-outsider budget through one stage (paper displayed form). -/
def Cond42 (p : ScheduleParams) (ip : InvariantParams) : Prop :=
  (ip.mu + (p.br - 1 : Rat) * ip.mu * siblingFactor p ip +
      slackCoeff p + ip.epsB) /
      (p.A * p.nu) +
    ip.mu * ip.delta / (p.A * (p.br : Rat) * p.nu) ≤ ip.mu

/-- §4 (4.3): `μ ≤ ν/(A k²)`. -/
def Cond43 (p : ScheduleParams) (ip : InvariantParams) : Prop :=
  ip.mu ≤ p.nu / (p.A * (p.br : Rat) ^ 2)

/-- §4 (4.4): fringe-count consequence involving `δF`. -/
def Cond44 (p : ScheduleParams) (ip : InvariantParams) : Prop :=
  ip.mu ≤ (1 / (2 * ip.deltaF)) *
    (p.A * p.nu * (p.br : Rat) - 1) / (p.A ^ 2 * (p.br : Rat) ^ 2)

/-- §4 (4.5): first-stranger / higher-order decay through one stage. -/
def Cond45 (p : ScheduleParams) (ip : InvariantParams) : Prop :=
  ip.epsF / (p.A * p.nu) + ip.delta ^ 2 * p.A * (p.br : Rat) / p.nu ≤
    ip.delta

/-- All five separator-quality / envelope inequalities of §4. -/
def SeparatorConds (p : ScheduleParams) (ip : InvariantParams) : Prop :=
  Cond41 p ip ∧ Cond42 p ip ∧ Cond43 p ip ∧ Cond44 p ip ∧ Cond45 p ip

/-! **Invariant P** -/

/-- Paper proposition `P` at stage `t`, for a single bag placement and rank
    permutation. Uses paper order `r` via `Strange (r+1)`. -/
theorem br_ge_one (p : ScheduleParams) : 1 ≤ p.br :=
  le_trans (by omega : 1 ≤ 2) p.hbr

def OutsiderBound (p : ScheduleParams) (ip : InvariantParams) (d : Nat)
    (_sched : LevelSchedule p d) (t : Nat)
    (pl : Placement p.br d)
    (perm : Fin (p.br ^ d) → Fin (p.br ^ d)) : Prop :=
  ∀ (b : KBag p.br d) (r : Nat), r ≤ d →
    ((b.strangers (r + 1) perm (pl.regs b) (br_ge_one p) : Rat)) <
      ip.mu * ip.delta ^ r * capacity p d b.l t

/-- Convenience: `P` restricted to occupied levels `[α(t), ω(t)]`. -/
def OutsiderBound.active (p : ScheduleParams) (ip : InvariantParams) (d : Nat)
    (sched : LevelSchedule p d) (t : Nat) (_ht : t ≤ sched.tf)
    (pl : Placement p.br d)
    (perm : Fin (p.br ^ d) → Fin (p.br ^ d)) : Prop :=
  ∀ (b : KBag p.br d) (r : Nat), r ≤ d →
    sched.alpha t ≤ b.l → b.l ≤ sched.omega t →
    ((b.strangers (r + 1) perm (pl.regs b) (br_ge_one p) : Rat)) <
      ip.mu * ip.delta ^ r * capacity p d b.l t

/-! **Lemma 4.5 purity** -/

/-- §4 Lemma 4.5 (purity form): if the order-`r` bound at the top level is
    strictly less than 1, then there are no order-`r` outsiders there.

    Status: this is the cardinality step only; discharging
    `μ δ^r c(α(tf), tf) ≤ 1` from the §7 envelope is separate. -/
theorem lemma45_purity (p : ScheduleParams) (ip : InvariantParams) (d : Nat)
    (sched : LevelSchedule p d) (pl : Placement p.br d)
    (perm : Fin (p.br ^ d) → Fin (p.br ^ d))
    (r : Nat) (hr : r ≤ d)
    (b : KBag p.br d) (hb : b.l = sched.alpha sched.tf)
    (hP : OutsiderBound p ip d sched sched.tf pl perm)
    (hcap : ip.mu * ip.delta ^ r * capacity p d (sched.alpha sched.tf) sched.tf ≤ 1) :
    b.strangers (r + 1) perm (pl.regs b) (br_ge_one p) = 0 := by
  have hbr := br_ge_one p
  have hlt := hP b r hr
  have hbound :
      (b.strangers (r + 1) perm (pl.regs b) hbr : Rat) < 1 := by
    calc (b.strangers (r + 1) perm (pl.regs b) hbr : Rat)
        < ip.mu * ip.delta ^ r * capacity p d b.l sched.tf := hlt
      _ = ip.mu * ip.delta ^ r * capacity p d (sched.alpha sched.tf) sched.tf := by
          rw [hb]
      _ ≤ 1 := hcap
  have hnat : b.strangers (r + 1) perm (pl.regs b) hbr < 1 := by
    exact_mod_cast hbound
  omega

/-- Finite geometric sum used in the Lemma 4.1 envelope:
    `sum_{j=0}^{J-1} q^j = (q^J - 1) / (q - 1)`. -/
theorem lemma41_geom_partial (q : Rat) (hq : q ≠ 1) (J : Nat) :
    ∑ j ∈ Finset.range J, q ^ j = (q ^ J - 1) / (q - 1) :=
  geom_sum_eq hq J

end Chvatal
