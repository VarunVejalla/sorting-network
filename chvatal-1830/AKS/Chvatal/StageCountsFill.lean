module
-- Chvátal Lemma 4.1 count bundle (algebraic fill)

public import AKS.Chvatal.OutsiderLemmas

@[expose] public section

namespace Chvatal

/-- Algebraic Lemma 4.1 counts on the occupied ladder `(α(t), ω(t))`. -/
def stageCounts_on_schedule (p : ScheduleParams) (ip : InvariantParams)
    (d : Nat) (sched : LevelSchedule p d) (t : Nat) :
    ∀ i, sched.alpha t ≤ i → i < sched.omega t → StageCounts p d i t :=
  fun i _ _ =>
    ⟨((p.br : Rat) ^ d / (p.br : Rat) ^ i - capacity p d i t) / (p.br : Rat),
      ip.mu * siblingFactor p ip * capacity p d i t⟩

theorem stageCounts_on_schedule_wires (p : ScheduleParams) (ip : InvariantParams)
    (d : Nat) (sched : LevelSchedule p d) (t : Nat) :
    ∀ i (ha : sched.alpha t ≤ i) (ho : i < sched.omega t),
      ((stageCounts_on_schedule p ip d sched t) i ha ho).WiresMassForm p d i t :=
  fun _ _ _ => rfl

theorem stageCounts_on_schedule_bad (p : ScheduleParams) (ip : InvariantParams)
    (d : Nat) (sched : LevelSchedule p d) (t : Nat) :
    ∀ i (ha : sched.alpha t ≤ i) (ho : i < sched.omega t),
      ((stageCounts_on_schedule p ip d sched t) i ha ho).BadBound p ip d i t :=
  fun _ _ _ => le_rfl

end Chvatal
