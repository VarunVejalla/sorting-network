module

/-
  # Natural-number flow sizes of the Chvátal tree network

  `a l t` is the number of wires held by each node on level `l` at time `t`; between times
  `t` and `t+1` each such node sends `up l t` wires to its parent (the fringe blocks
  `F₁ ∪ F₂`) and `down l t` wires to each of its `64` children (a middle block `B_j`).
  This is the schedule-independent interface between the integer flow table
  (`FlowTable`, `FlowTable7`) and the construction of the wire sets (`WireFlow`).
-/

public import AKS.Chvatal.Tree

@[expose] public section

namespace Chvatal

/-- Natural-number flow sizes for `br = 64`, depth `d`, final time `tf`. -/
structure FlowSizes (d tf : Nat) where
  a : Nat → Nat → Nat
  up : Nat → Nat → Nat
  down : Nat → Nat → Nat
  ha_root : a 0 0 = 64 ^ d
  ha_init : ∀ l, 1 ≤ l → a l 0 = 0
  hup_even : ∀ l t, t < tf → 2 ∣ up l t
  hup_root : ∀ t, t < tf → up 0 t = 0
  hdown_leaf : ∀ t, t < tf → down d t = 0
  /-- A node sends out exactly its wires. -/
  hsplit : ∀ l t, l ≤ d → t < tf → a l t = up l t + 64 * down l t
  /-- Wires arriving at a node at time `t+1`: from its parent (if any) and its children. -/
  hcons : ∀ l t, l ≤ d → t < tf →
    a l (t + 1) = (if 1 ≤ l then down (l - 1) t else 0) + (if l < d then 64 * up (l + 1) t else 0)

end Chvatal
