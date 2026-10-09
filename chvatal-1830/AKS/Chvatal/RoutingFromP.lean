module
-- Chvátal §4 placement step

public import AKS.Chvatal.OutsiderInduction

@[expose] public section

namespace Chvatal

/-- One stage's register routing: each non-root child bag is covered by keys sent from its parent
    and keys sent up from its children. -/
structure PlacementStep (p : ScheduleParams) (d : Nat)
    (pl pl' : Placement p.br d) where
  fromParent : ∀ (b : KBag p.br d), 1 ≤ b.l → Finset (Fin (p.br ^ d))
  fromChildren : ∀ (b : KBag p.br d), 1 ≤ b.l → Finset (Fin (p.br ^ d))
  hregs : ∀ (b : KBag p.br d) (hb : 1 ≤ b.l),
    pl'.regs b ⊆ fromParent b hb ∪ fromChildren b hb

/-- Outsider count on a covered bag splits across the two send Finsets. -/
theorem PlacementStep.strangers_split_le {p : ScheduleParams} {d : Nat}
    {pl pl' : Placement p.br d} (S : PlacementStep p d pl pl')
    (perm' : Fin (p.br ^ d) → Fin (p.br ^ d))
    (b : KBag p.br d) (hb : 1 ≤ b.l) (j : Nat) :
    (b.strangers j perm' (pl'.regs b) (br_ge_one p) : Rat) ≤
      (b.strangers j perm' (S.fromParent b hb) (br_ge_one p) : Rat) +
        (b.strangers j perm' (S.fromChildren b hb) (br_ge_one p) : Rat) := by
  exact_mod_cast (b.strangers_mono j perm' (S.hregs b hb) (br_ge_one p)).trans
    (b.strangers_union_le j perm' _ _ (br_ge_one p))

/-- Parent order-0 outsider mass at time `t`. -/
def parentOutMass (p : ScheduleParams) (d : Nat) (pl : Placement p.br d)
    (perm : Fin (p.br ^ d) → Fin (p.br ^ d)) (b : KBag p.br d) (_hb : 1 ≤ b.l) : Rat :=
  ((b.parent (br_ge_one p)).strangers 1 perm
    (pl.regs (b.parent (br_ge_one p))) (br_ge_one p) : Rat)

end Chvatal
