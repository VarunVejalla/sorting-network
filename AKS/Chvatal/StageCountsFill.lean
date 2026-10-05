module
/-
  # Chvatal Lemma 4.1 count bundle (algebraic fill)

  Source: V. Chvatal, *Lecture Notes on the New AKS Sorting Network*,
  Rutgers DCS-TR-294 (1992), §4 Lemma 4.1.

  Status: fills `StageCounts` / `WiresMassForm` / `BadBound` with the paper's
  scalar formulas. Linking these scalars to concrete wire Finsets below a child
  remains a placement-network obligation.
-/

public import AKS.Chvatal.OutsiderLemmas

@[expose] public section

namespace Chvatal

/-- Algebraic Lemma 4.1 count bundle at level `i`. -/
def stageCounts_algebraic (p : ScheduleParams) (d i t : Nat)
    (ip : InvariantParams) : StageCounts p d i t where
  addressedBelowChild := (p.br : Rat) ^ d / (p.br : Rat) ^ (i + 1)
  wiresBelowChild :=
    ((p.br : Rat) ^ d / (p.br : Rat) ^ i - capacity p d i t) / (p.br : Rat)
  badBelowChild := ip.mu * siblingFactor p ip * capacity p d i t
  parentAddressedBelowChild :=
    (p.br : Rat) ^ d / (p.br : Rat) ^ (i + 1) -
      (((p.br : Rat) ^ d / (p.br : Rat) ^ i - capacity p d i t) / (p.br : Rat)) +
        ip.mu * siblingFactor p ip * capacity p d i t
  addressed_eq := rfl
  parent_balance := by ring

theorem stageCounts_algebraic_wires (p : ScheduleParams) (d i t : Nat)
    (ip : InvariantParams) :
    (stageCounts_algebraic p d i t ip).WiresMassForm p d i t := rfl

theorem stageCounts_algebraic_bad (p : ScheduleParams) (d i t : Nat)
    (ip : InvariantParams) :
    (stageCounts_algebraic p d i t ip).BadBound p ip d i t := le_rfl

/-- Bundle of algebraic counts on the occupied ladder `(α(t), ω(t))`. -/
def stageCounts_on_schedule (p : ScheduleParams) (ip : InvariantParams)
    (d : Nat) (sched : LevelSchedule p d) (t : Nat) :
    ∀ i, sched.alpha t ≤ i → i < sched.omega t → StageCounts p d i t :=
  fun i _ _ => stageCounts_algebraic p d i t ip

theorem stageCounts_on_schedule_wires (p : ScheduleParams) (ip : InvariantParams)
    (d : Nat) (sched : LevelSchedule p d) (t : Nat) :
    ∀ i (ha : sched.alpha t ≤ i) (ho : i < sched.omega t),
      ((stageCounts_on_schedule p ip d sched t) i ha ho).WiresMassForm p d i t :=
  fun i _ _ => stageCounts_algebraic_wires p d i t ip

theorem stageCounts_on_schedule_bad (p : ScheduleParams) (ip : InvariantParams)
    (d : Nat) (sched : LevelSchedule p d) (t : Nat) :
    ∀ i (ha : sched.alpha t ≤ i) (ho : i < sched.omega t),
      ((stageCounts_on_schedule p ip d sched t) i ha ho).BadBound p ip d i t :=
  fun i _ _ => stageCounts_algebraic_bad p d i t ip

end Chvatal
