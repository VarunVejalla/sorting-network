module
/-
  # Chvatal §4 abstract separator contract

  Source: V. Chvatal, *Lecture Notes on the New AKS Sorting Network*,
  Rutgers DCS-TR-294 (1992), §4–§5.

  Status: abstract interface for separator quality, `StageCounts`, and
  `StageModel`. `StageDynamics` discharges `StageModel`; concrete scramble
  separators (Thm 5.1 / Phase 2) and placement/routing fill `StageDynamics`.
  No network construction lives here.
-/

public import AKS.Chvatal.OutsiderInvariant

@[expose] public section

namespace Chvatal

/-! **Local separator quality** -/

/-- Quality of the separator used between stages `t` and `t+1` on a bag of
    size `a`. Encodes paper Properties B/F for Lemmas 4.2–4.4. -/
structure LocalSeparatorQuality (ip : InvariantParams) where
  a : Rat
  ha_pos : 0 < a
  /-- `a ≤ c` at stages with `t ≥ 1` (paper: bag size ≤ capacity). -/
  ha_le : Rat → Prop
  /-- Intrusion into one child block: ≤ `epsB * a` non-addressed keys. -/
  intrusion : Rat
  hIntrusion : intrusion ≤ ip.epsB * a
  /-- Fringe filter: among ≤ `deltaF*(π/2)` order-`(r-1)` outsiders, at most
      `epsF` fraction enter one child block. -/
  fringeSent : Rat → Rat
  hFringe : ∀ src, fringeSent src ≤ ip.epsF * src

/-- Root-at-time-0 exceptional separator (`epsB` replaced by `epsStar`). -/
structure RootSeparatorQuality (ip : InvariantParams) where
  N : Rat
  hN_pos : 0 < N
  childOutsiders : Rat
  hStar : childOutsiders < ip.epsStar * N

/-! **Stage-count interface for Lemma 4.1** -/

/-- Combinatorial counts a stage model must provide for one parent level `i`
    and one distinguished child. -/
structure StageCounts (p : ScheduleParams) (d i t : Nat) where
  addressedBelowChild : Rat
  wiresBelowChild : Rat
  badBelowChild : Rat
  parentAddressedBelowChild : Rat
  addressed_eq :
    addressedBelowChild = (p.br : Rat) ^ d / (p.br : Rat) ^ (i + 1)
  parent_balance :
    parentAddressedBelowChild =
      addressedBelowChild - wiresBelowChild + badBelowChild

/-- Wire-mass form from Lemma 3.1 when `i < ω(t)`. -/
def StageCounts.WiresMassForm (p : ScheduleParams) (d i t : Nat)
    (sc : StageCounts p d i t) : Prop :=
  sc.wiresBelowChild =
    ((p.br : Rat) ^ d / (p.br : Rat) ^ i - capacity p d i t) / (p.br : Rat)

/-- Bad-key bound from descendant outsiders under `P`. -/
def StageCounts.BadBound (p : ScheduleParams) (ip : InvariantParams)
    (d i t : Nat) (sc : StageCounts p d i t) : Prop :=
  sc.badBelowChild ≤ ip.mu * siblingFactor p ip * capacity p d i t

/-! **Lemma 4.2–4.4 source interface** -/

/-- Paper Lemma 4.2 coefficient of `c(i,t)`. -/
def lemma42_coeff (p : ScheduleParams) (ip : InvariantParams) : Rat :=
  ip.mu + ((p.br : Rat) - 1) * ip.mu * siblingFactor p ip +
    slackCoeff p + ip.epsB

/-- Sources of order-0 outsiders at a child after one stage. -/
structure Lemma43Sources where
  fromParent : Rat
  fromChildren : Rat
  total : Rat
  hsplit : total ≤ fromParent + fromChildren

/-- Sources of order-`r` outsiders at a child after one stage (`r ≥ 1`). -/
structure Lemma44Sources where
  fromParent : Rat
  fromChildren : Rat
  total : Rat
  hsplit : total ≤ fromParent + fromChildren

/-! **Stage model for the §4 inductive step** -/

/-- Combinatorial hypotheses for one stage transition `t → t+1`.
    Fields package facts discharged later by the stage scheduler and
    separator routing (Phase 1 remainder / Phase 2). -/
structure StageModel (p : ScheduleParams) (ip : InvariantParams) (d : Nat)
    (sched : LevelSchedule p d) (t : Nat)
    (pl : Placement p.br d)
    (perm : Fin (p.br ^ d) → Fin (p.br ^ d))
    (pl' : Placement p.br d)
    (perm' : Fin (p.br ^ d) → Fin (p.br ^ d)) where
  ht : t + 1 ≤ sched.tf
  /-- Capacity at the parent level is positive. -/
  hcap_pos : ∀ (b : KBag p.br d), 1 ≤ b.l →
    0 < capacity p d (b.l - 1) t
  /-- Optional Lemma 4.1 count bundle at each occupied parent level. -/
  counts : ∀ i, sched.alpha t ≤ i → i < sched.omega t → StageCounts p d i t
  counts_wires : ∀ i (ha : sched.alpha t ≤ i) (ho : i < sched.omega t),
    (counts i ha ho).WiresMassForm p d i t
  counts_bad : ∀ i (ha : sched.alpha t ≤ i) (ho : i < sched.omega t),
    (counts i ha ho).BadBound p ip d i t
  /-- Order-0 source split at each non-root bag after the stage. -/
  order0 : ∀ (b : KBag p.br d), 1 ≤ b.l → Lemma43Sources
  order0_total : ∀ (b : KBag p.br d) (hb : 1 ≤ b.l),
    ((b.strangers 1 perm' (pl'.regs b) (br_ge_one p) : Rat)) ≤
      (order0 b hb).total
  order0_parent : ∀ (b : KBag p.br d) (hb : 1 ≤ b.l),
    (order0 b hb).fromParent ≤
      lemma42_coeff p ip * capacity p d (b.l - 1) t
  order0_child : ∀ (b : KBag p.br d) (hb : 1 ≤ b.l),
    (order0 b hb).fromChildren ≤
      ip.mu * ip.delta / (p.br : Rat) * capacity p d (b.l - 1) t
  /-- Order-`r` (`r ≥ 1`) source split. -/
  orderR : ∀ (b : KBag p.br d) (r : Nat), 1 ≤ r → r ≤ d → 1 ≤ b.l →
    Lemma44Sources
  orderR_total : ∀ (b : KBag p.br d) (r : Nat)
      (hr1 : 1 ≤ r) (hrd : r ≤ d) (hb : 1 ≤ b.l),
    ((b.strangers (r + 1) perm' (pl'.regs b) (br_ge_one p) : Rat)) ≤
      (orderR b r hr1 hrd hb).total
  orderR_parent : ∀ (b : KBag p.br d) (r : Nat)
      (hr1 : 1 ≤ r) (hrd : r ≤ d) (hb : 1 ≤ b.l),
    (orderR b r hr1 hrd hb).fromParent ≤
      ip.epsF * (ip.mu * ip.delta ^ (r - 1) * capacity p d (b.l - 1) t)
  orderR_child : ∀ (b : KBag p.br d) (r : Nat)
      (hr1 : 1 ≤ r) (hrd : r ≤ d) (hb : 1 ≤ b.l),
    (orderR b r hr1 hrd hb).fromChildren ≤
      ip.delta ^ 2 * p.A * (p.br : Rat) / p.nu *
        (ip.mu * ip.delta ^ (r - 1) *
          (p.A * p.nu * capacity p d (b.l - 1) t))
  /-- Level-0 bags: outsider counts after the stage (root / exceptional case). -/
  level0 : ∀ (b : KBag p.br d) (r : Nat), b.l = 0 → r ≤ d →
    ((b.strangers (r + 1) perm' (pl'.regs b) (br_ge_one p) : Rat)) ≤
      ip.mu * ip.delta ^ r * capacity p d 0 (t + 1)

end Chvatal
