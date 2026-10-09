module
-- Chvátal §4 separator quality and Lemma 4.1 count interface

public import AKS.Chvatal.OutsiderInvariant

@[expose] public section

namespace Chvatal

/-- Quality of the separator used between stages `t` and `t+1` on a bag of size `a`
    (paper Properties B/F). -/
structure LocalSeparatorQuality (ip : InvariantParams) where
  a : Rat
  ha_pos : 0 < a
  ha_le : Rat → Prop
  /-- Intrusion into one child block: ≤ `epsB * a` non-addressed keys. -/
  intrusion : Rat
  hIntrusion : intrusion ≤ ip.epsB * a
  /-- Fringe filter: at most an `epsF` fraction of the order-`(r-1)` outsiders enter one child. -/
  fringeSent : Rat → Rat
  hFringe : ∀ src, fringeSent src ≤ ip.epsF * src

/-- Lemma 4.1 counts at parent level `i` for one distinguished child. -/
structure StageCounts (p : ScheduleParams) (d i t : Nat) where
  wiresBelowChild : Rat
  badBelowChild : Rat

/-- Wire-mass form from Lemma 3.1. -/
def StageCounts.WiresMassForm (p : ScheduleParams) (d i t : Nat)
    (sc : StageCounts p d i t) : Prop :=
  sc.wiresBelowChild =
    ((p.br : Rat) ^ d / (p.br : Rat) ^ i - capacity p d i t) / (p.br : Rat)

/-- Bad-key bound from descendant outsiders under `P`. -/
def StageCounts.BadBound (p : ScheduleParams) (ip : InvariantParams)
    (d i t : Nat) (sc : StageCounts p d i t) : Prop :=
  sc.badBelowChild ≤ ip.mu * siblingFactor p ip * capacity p d i t

end Chvatal
