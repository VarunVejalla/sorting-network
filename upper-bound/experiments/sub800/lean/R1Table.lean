import R1Subtree

/-! # The design-P flow table (W1, step 15): definitions and the conservation step

Roles at `(i, t)`: descending top (`topD`), rising bottom (`botR`); otherwise rising top
(`i = α(t)`), interior or descending bottom. Up-flow (Chvátal): `0` (`topD`), `c/2^12` (rising top),
`63 c/2^18` (interior, descending bottom), `a` (`botR`). Design P (R1-PROOF §1): with
`s = 0` if `G = 0` else `r* c = 15 c/2^19`, the end children get `θ = π/2 + G − s`, the 14 interior
children share `I = 2s − G` (`⌊I/14⌋` or `⌈I/14⌉`); child `j` receives `G_j − θ_j` wires.

The primitive state is the wire count `aT t b`; deficits are `Gof (aT t) b`. -/

namespace R1T

open Finset
open Chvatal (KBag subtreeBags)

variable {d : ℕ}

/-- Descending top. -/
def topD (d i t : ℕ) : Prop := i = alpha d t ∧ alpha d t < alpha d (t + 1)

/-- Rising bottom. -/
def botR (d i t : ℕ) : Prop := i = omega t ∧ i ≠ alpha d t ∧ ¬ omega t < omega (t + 1)

instance (d i t : ℕ) : Decidable (topD d i t) := by unfold topD; infer_instance
instance (d i t : ℕ) : Decidable (botR d i t) := by unfold botR; infer_instance

/-- Exponent of the capacity as a natural number (valid on active nodes). -/
def eN (d i t : ℕ) : ℕ := 4 * d + 5 * i - 3 * t - 6

/-- Chvátal's up-flow for the roles other than the rising bottom. -/
def piC (d i t : ℕ) : ℕ :=
  if topD d i t then 0 else if i = alpha d t then 2 ^ (eN d i t - 12) else 63 * 2 ^ (eN d i t - 18)

/-- `r* · c = 15 · 2^(e − 19)`. -/
def sres (d i t : ℕ) : ℕ := 15 * 2 ^ (eN d i t - 19)

/-- Node `i` sends at stage `t`. -/
def Sends (d i t : ℕ) : Prop := Active d i t ∧ t < tf d

instance (d i t : ℕ) : Decidable (Sends d i t) := by unfold Sends Active; infer_instance

section Defs

variable (A : KBag 16 d → ℕ) (t : ℕ)

/-- Up-flow. -/
def upOf (b : KBag 16 d) : ℕ :=
  if Sends d b.l t then (if botR d b.l t then A b else piC d b.l t) else 0

/-- The reserve `s` of a sender. -/
def sOf (q : KBag 16 d) : ℤ := if Gof A q = 0 then 0 else (sres d q.l t : ℤ)

/-- Design P: the `θ` of child `j`. -/
def thetaOf (q : KBag 16 d) (hq : q.l < d) (j : Fin 16) : ℤ :=
  if topD d q.l t then 0
  else if botR d q.l t then Gof A (q.child j.val j.isLt hq)
  else if j.val = 0 ∨ j.val = 15 then (upOf A t q : ℤ) / 2 + Gof A q - sOf A t q
  else (2 * sOf A t q - Gof A q) / 14 +
    (if ((j.val : ℤ) - 1) < (2 * sOf A t q - Gof A q) % 14 then 1 else 0)

/-- Down-flow to child `j`. -/
def downOf (q : KBag 16 d) (j : Fin 16) : ℕ :=
  if h : Sends d q.l t ∧ q.l < d then
    (Gof A (q.child j.val j.isLt h.2) - thetaOf A t q h.2 j).toNat
  else 0

/-- Wires after the stage. -/
def nextA (b : KBag 16 d) : ℕ :=
  (if 1 ≤ b.l then downOf A t b.parent ⟨b.x % 16, Nat.mod_lt _ (by norm_num)⟩ else 0) +
    (if h : b.l < d then ∑ j : Fin 16, upOf A t (b.child j.val j.isLt h) else 0)

end Defs

/-- The wire counts of design P. -/
def aT (d : ℕ) : ℕ → KBag 16 d → ℕ
  | 0 => fun b => if b = KBag.root 16 d then 16 ^ d else 0
  | t + 1 => nextA (aT d t) t

/-- Conservation at a node: it sends out exactly its wires. -/
def Conserves (A : KBag 16 d → ℕ) (t : ℕ) (b : KBag 16 d) : Prop :=
  A b = upOf A t b + ∑ j : Fin 16, downOf A t b j

/-- Down-flow into `b` from its parent. -/
def downIn (A : KBag 16 d → ℕ) (t : ℕ) (b : KBag 16 d) : ℕ :=
  if 1 ≤ b.l then downOf A t b.parent ⟨b.x % 16, Nat.mod_lt _ (by norm_num)⟩ else 0

theorem downIn_child (A : KBag 16 d → ℕ) (t : ℕ) (w : KBag 16 d) (hw : w.l < d) (j : Fin 16) :
    downIn A t (w.child j.val j.isLt hw) = downOf A t w j := by
  unfold downIn
  rw [if_pos (by show 1 ≤ w.l + 1; omega)]
  have hp : (w.child j.val j.isLt hw).parent = w := Chvatal.KBag.child_parent w j.val j.isLt hw (by norm_num)
  have hx : (⟨(w.child j.val j.isLt hw).x % 16, Nat.mod_lt _ (by norm_num)⟩ : Fin 16) = j := by
    apply Fin.ext; show (16 * w.x + j.val) % 16 = j.val; omega
  rw [hp, hx]

/-- **Subtree conservation.** If every node conserves wires at stage `t`, the wires in a subtree
change by the inflow from the parent minus the outflow to it. -/
theorem subtree_step (A : KBag 16 d → ℕ) (t : ℕ) (hcons : ∀ z, Conserves A t z) :
    ∀ n (b : KBag 16 d), d - b.l = n →
      (∑ z ∈ subtreeBags 16 d (by norm_num) b, (nextA A t z : ℤ)) =
        ∑ z ∈ subtreeBags 16 d (by norm_num) b, (A z : ℤ) + downIn A t b - upOf A t b
  | 0, b, hn => by
    have hl : b.l = d := by have := b.hl; omega
    rw [subtreeBags_leaf b hl, Finset.sum_singleton, Finset.sum_singleton]
    have h1 : (nextA A t b : ℤ) = downIn A t b := by
      unfold nextA downIn; rw [dif_neg (by omega)]; push_cast; ring
    have h2 := hcons b
    unfold Conserves downOf at h2
    have h3 : ∑ j : Fin 16, (if h : Sends d b.l t ∧ b.l < d then
        (Gof A (b.child j.val j.isLt h.2) - thetaOf A t b h.2 j).toNat else 0) = 0 :=
      Finset.sum_eq_zero fun j _ => by rw [dif_neg (by omega)]
    rw [h3] at h2
    rw [h1, h2]; push_cast; ring
  | n + 1, b, hn => by
    have hl : b.l < d := by omega
    rw [sum_subtree_split b hl (fun z => (nextA A t z : ℤ)), sum_subtree_split b hl (fun z => (A z : ℤ))]
    have ih : ∀ j : Fin 16, (∑ z ∈ subtreeBags 16 d (by norm_num) (b.child j.val j.isLt hl), (nextA A t z : ℤ)) =
        ∑ z ∈ subtreeBags 16 d (by norm_num) (b.child j.val j.isLt hl), (A z : ℤ) +
          downIn A t (b.child j.val j.isLt hl) - upOf A t (b.child j.val j.isLt hl) :=
      fun j => subtree_step A t hcons n _ (by show d - (b.l + 1) = n; omega)
    rw [Finset.sum_congr rfl (fun j _ => ih j)]
    simp only [downIn_child A t b hl]
    have h1 : (nextA A t b : ℤ) = downIn A t b + ∑ j : Fin 16, (upOf A t (b.child j.val j.isLt hl) : ℤ) := by
      unfold nextA downIn; rw [dif_pos hl]; push_cast; ring
    have h2 := hcons b
    unfold Conserves at h2
    rw [h1, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    have h2' : (A b : ℤ) = upOf A t b + ∑ j : Fin 16, (downOf A t b j : ℤ) := by rw [h2]; push_cast; ring
    rw [h2']
    ring

/-- **Deficit update.** -/
theorem Gof_next (A : KBag 16 d → ℕ) (t : ℕ) (hcons : ∀ z, Conserves A t z) (b : KBag 16 d) :
    Gof (nextA A t) b = Gof A b + upOf A t b - downIn A t b := by
  unfold Gof
  rw [subtree_step A t hcons (d - b.l) b rfl]
  ring

end R1T
