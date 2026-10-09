module
/-
  # Chvatal §4 outsider bound `P` (non-strict inductive form)

  Source: V. Chvatal, DCS-TR-294 (1992), §4.
-/

public import AKS.Chvatal.OutsiderLemmas

@[expose] public section

namespace Chvatal

/-- Non-strict form of proposition `P` at stage `t`, for a placement and rank permutation. -/
def OutsiderBoundLe (p : ScheduleParams) (ip : InvariantParams) (d : Nat)
    (_sched : LevelSchedule p d) (t : Nat)
    (pl : Placement p.br d)
    (perm : Fin (p.br ^ d) → Fin (p.br ^ d)) : Prop :=
  ∀ (b : KBag p.br d) (r : Nat), r ≤ d →
    ((b.strangers (r + 1) perm (pl.regs b) (br_ge_one p) : Rat)) ≤
      ip.mu * ip.delta ^ r * capacity p d b.l t

end Chvatal
