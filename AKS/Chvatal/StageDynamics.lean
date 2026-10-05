module
/-
  # Chvatal §4 stage dynamics → StageModel

  Source: V. Chvatal, *Lecture Notes on the New AKS Sorting Network*,
  Rutgers DCS-TR-294 (1992), §4.

  Status: discharges `StageModel` from a thinner combinatorial `StageDynamics`
  contract (Lemma 4.2 parts, source splits, fringe routing, child send-ups).
  `PlacementStep` / `StageRouting` fill the Finset source-split; remaining
  numeric routing bounds and scramble separators (Thm 5.1) stay deferred.
-/

public import AKS.Chvatal.OutsiderInduction
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace Chvatal

/-! **Stage dynamics contract** -/

/-- Combinatorial accounting for one stage transition `t → t+1`.
    Packages the paper's Lemmas 4.2–4.4 source ingredients without building
    comparator networks. -/
structure StageDynamics (p : ScheduleParams) (ip : InvariantParams) (d : Nat)
    (sched : LevelSchedule p d) (t : Nat)
    (pl : Placement p.br d)
    (perm : Fin (p.br ^ d) → Fin (p.br ^ d))
    (pl' : Placement p.br d)
    (perm' : Fin (p.br ^ d) → Fin (p.br ^ d)) where
  ht : t + 1 ≤ sched.tf
  /-- Lemma 4.1 count bundle at each occupied parent level. -/
  counts : ∀ i, sched.alpha t ≤ i → i < sched.omega t → StageCounts p d i t
  counts_wires : ∀ i (ha : sched.alpha t ≤ i) (ho : i < sched.omega t),
    (counts i ha ho).WiresMassForm p d i t
  counts_bad : ∀ i (ha : sched.alpha t ≤ i) (ho : i < sched.omega t),
    (counts i ha ho).BadBound p ip d i t
  /-- Order-0 Lemma 4.2 parts and routing at each non-root child. -/
  parentOut0 : ∀ (b : KBag p.br d), 1 ≤ b.l → Rat
  sibMass0 : ∀ (b : KBag p.br d), 1 ≤ b.l → Rat
  intrusion0 : ∀ (b : KBag p.br d), 1 ≤ b.l → Rat
  slack0 : ∀ (b : KBag p.br d), 1 ≤ b.l → Rat
  fromParent0 : ∀ (b : KBag p.br d), 1 ≤ b.l → Rat
  fromChildren0 : ∀ (b : KBag p.br d), 1 ≤ b.l → Rat
  hParentOut0 : ∀ (b : KBag p.br d) (hb : 1 ≤ b.l),
    parentOut0 b hb ≤ ip.mu * capacity p d (b.l - 1) t
  hSibMass0 : ∀ (b : KBag p.br d) (hb : 1 ≤ b.l),
    sibMass0 b hb ≤
      ((p.br : Rat) - 1) * ip.mu * siblingFactor p ip * capacity p d (b.l - 1) t
  hIntrusion0 : ∀ (b : KBag p.br d) (hb : 1 ≤ b.l),
    intrusion0 b hb ≤ ip.epsB * capacity p d (b.l - 1) t
  hSlack0 : ∀ (b : KBag p.br d) (hb : 1 ≤ b.l),
    slack0 b hb ≤ slackCoeff p * capacity p d (b.l - 1) t
  hFromParent0 : ∀ (b : KBag p.br d) (hb : 1 ≤ b.l),
    fromParent0 b hb ≤
      parentOut0 b hb + sibMass0 b hb + intrusion0 b hb + slack0 b hb
  hFromChildren0 : ∀ (b : KBag p.br d) (hb : 1 ≤ b.l),
    fromChildren0 b hb ≤
      ip.mu * ip.delta / (p.br : Rat) * capacity p d (b.l - 1) t
  hStrangers0 : ∀ (b : KBag p.br d) (hb : 1 ≤ b.l),
    ((b.strangers 1 perm' (pl'.regs b) (br_ge_one p) : Rat)) ≤
      fromParent0 b hb + fromChildren0 b hb
  /-- Order-`r` (`r ≥ 1`) fringe / child routing. -/
  fromParentR : ∀ (b : KBag p.br d) (r : Nat), 1 ≤ r → r ≤ d → 1 ≤ b.l → Rat
  fromChildrenR : ∀ (b : KBag p.br d) (r : Nat), 1 ≤ r → r ≤ d → 1 ≤ b.l → Rat
  hFromParentR : ∀ (b : KBag p.br d) (r : Nat)
      (hr1 : 1 ≤ r) (hrd : r ≤ d) (hb : 1 ≤ b.l),
    fromParentR b r hr1 hrd hb ≤
      ip.epsF * (ip.mu * ip.delta ^ (r - 1) * capacity p d (b.l - 1) t)
  hFromChildrenR : ∀ (b : KBag p.br d) (r : Nat)
      (hr1 : 1 ≤ r) (hrd : r ≤ d) (hb : 1 ≤ b.l),
    fromChildrenR b r hr1 hrd hb ≤
      ip.delta ^ 2 * p.A * (p.br : Rat) / p.nu *
        (ip.mu * ip.delta ^ (r - 1) *
          (p.A * p.nu * capacity p d (b.l - 1) t))
  hStrangersR : ∀ (b : KBag p.br d) (r : Nat)
      (hr1 : 1 ≤ r) (hrd : r ≤ d) (hb : 1 ≤ b.l),
    ((b.strangers (r + 1) perm' (pl'.regs b) (br_ge_one p) : Rat)) ≤
      fromParentR b r hr1 hrd hb + fromChildrenR b r hr1 hrd hb
  /-- Level-0 bags after the stage (root / exceptional routing). -/
  level0 : ∀ (b : KBag p.br d) (r : Nat), b.l = 0 → r ≤ d →
    ((b.strangers (r + 1) perm' (pl'.regs b) (br_ge_one p) : Rat)) ≤
      ip.mu * ip.delta ^ r * capacity p d 0 (t + 1)

/-! **Lemma 4.2 assembly** -/

/-- Order-0 parent send bound from Lemma 4.2 parts. -/
theorem order0_parent_of_parts (p : ScheduleParams) (ip : InvariantParams)
    (d : Nat) (sched : LevelSchedule p d) (t : Nat)
    (pl pl' : Placement p.br d)
    (perm perm' : Fin (p.br ^ d) → Fin (p.br ^ d))
    (D : StageDynamics p ip d sched t pl perm pl' perm')
    (b : KBag p.br d) (hb : 1 ≤ b.l) :
    D.fromParent0 b hb ≤ lemma42_coeff p ip * capacity p d (b.l - 1) t := by
  have hparts := lemma42_of_parts p ip (capacity p d (b.l - 1) t)
    (D.parentOut0 b hb) (D.sibMass0 b hb) (D.intrusion0 b hb) (D.slack0 b hb)
    (D.hParentOut0 b hb) (D.hSibMass0 b hb) (D.hIntrusion0 b hb) (D.hSlack0 b hb)
  linarith [D.hFromParent0 b hb, hparts]

/-! **StageModel discharge** -/

/-- Build the order-0 source bundle from dynamics. -/
def order0SourcesOf (p : ScheduleParams) (ip : InvariantParams)
    (d : Nat) (sched : LevelSchedule p d) (t : Nat)
    (pl pl' : Placement p.br d)
    (perm perm' : Fin (p.br ^ d) → Fin (p.br ^ d))
    (D : StageDynamics p ip d sched t pl perm pl' perm')
    (b : KBag p.br d) (hb : 1 ≤ b.l) : Lemma43Sources where
  fromParent := D.fromParent0 b hb
  fromChildren := D.fromChildren0 b hb
  total := (b.strangers 1 perm' (pl'.regs b) (br_ge_one p) : Rat)
  hsplit := D.hStrangers0 b hb

/-- Build the order-`r` source bundle from dynamics. -/
def orderRSourcesOf (p : ScheduleParams) (ip : InvariantParams)
    (d : Nat) (sched : LevelSchedule p d) (t : Nat)
    (pl pl' : Placement p.br d)
    (perm perm' : Fin (p.br ^ d) → Fin (p.br ^ d))
    (D : StageDynamics p ip d sched t pl perm pl' perm')
    (b : KBag p.br d) (r : Nat) (hr1 : 1 ≤ r) (hrd : r ≤ d)
    (hb : 1 ≤ b.l) : Lemma44Sources where
  fromParent := D.fromParentR b r hr1 hrd hb
  fromChildren := D.fromChildrenR b r hr1 hrd hb
  total := (b.strangers (r + 1) perm' (pl'.regs b) (br_ge_one p) : Rat)
  hsplit := D.hStrangersR b r hr1 hrd hb

/-- `StageDynamics` discharges every field of `StageModel`. -/
def stageModel_of_dynamics (p : ScheduleParams) (ip : InvariantParams)
    (d : Nat) (sched : LevelSchedule p d) (t : Nat)
    (pl pl' : Placement p.br d)
    (perm perm' : Fin (p.br ^ d) → Fin (p.br ^ d))
    (D : StageDynamics p ip d sched t pl perm pl' perm') :
    StageModel p ip d sched t pl perm pl' perm' where
  ht := D.ht
  hcap_pos := fun b _hb => capacity_pos p d (b.l - 1) t
  counts := D.counts
  counts_wires := D.counts_wires
  counts_bad := D.counts_bad
  order0 := fun b hb =>
    order0SourcesOf p ip d sched t pl pl' perm perm' D b hb
  order0_total := fun b hb => le_rfl
  order0_parent := fun b hb => by
    simpa [order0SourcesOf] using
      order0_parent_of_parts p ip d sched t pl pl' perm perm' D b hb
  order0_child := fun b hb => by
    simpa [order0SourcesOf] using D.hFromChildren0 b hb
  orderR := fun b r hr1 hrd hb =>
    orderRSourcesOf p ip d sched t pl pl' perm perm' D b r hr1 hrd hb
  orderR_total := fun b r hr1 hrd hb => le_rfl
  orderR_parent := fun b r hr1 hrd hb => by
    simpa [orderRSourcesOf] using D.hFromParentR b r hr1 hrd hb
  orderR_child := fun b r hr1 hrd hb => by
    simpa [orderRSourcesOf] using D.hFromChildrenR b r hr1 hrd hb
  level0 := D.level0

/-- One-step preservation under dynamics: `P(t)` + conds + dynamics ⇒ `P(t+1)`. -/
theorem outsiderBound_step_of_dynamics (p : ScheduleParams) (ip : InvariantParams)
    (d : Nat) (sched : LevelSchedule p d) (t : Nat)
    (pl pl' : Placement p.br d)
    (perm perm' : Fin (p.br ^ d) → Fin (p.br ^ d))
    (hconds : SeparatorConds p ip)
    (D : StageDynamics p ip d sched t pl perm pl' perm')
    (hP : OutsiderBoundLe p ip d sched t pl perm) :
    OutsiderBoundLe p ip d sched (t + 1) pl' perm' :=
  outsiderBound_step p ip d sched t pl pl' perm perm' hconds
    (stageModel_of_dynamics p ip d sched t pl pl' perm perm' D) hP

end Chvatal
