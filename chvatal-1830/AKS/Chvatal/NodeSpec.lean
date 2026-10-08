module

/-
  # Node separator specification (interface between networks and the §4 counting)

  A node holding `a` wires runs a comparator network `net : ComparatorNetwork a` on its
  wires (cell `c` = the `c`-th smallest wire). Its output is cut into blocks by position:
  the first `π/2` cells (`F₁`) and last `π/2` cells (`F₂`) go up; the middle `64·τ` cells
  are split into 64 blocks of `τ` cells going to the children. Keys are normalized to their
  ranks `0..a-1` among the node's keys, so an input is a permutation `x` of `Fin a`, and the
  output `y := net.exec x` has `y c` = the rank of the key sitting at cell `c`.
  Smaller keys belong at smaller cell indices (ascending order).

  `NodeSpec` is the Chvátal Theorem 5.1 guarantee in two-sided position form:
  * `bHigh p`: at most `EB` of the largest `p` keys sit above the bottom `p` cells
    (cells `< a - p`), for every block boundary `p`;
  * `bLow p`: at most `EB` of the smallest `p` keys sit below the top `p` cells
    (cells `≥ p`), for every block boundary `p`;
  * `fHigh j`: for `0 < j ≤ Jmax`, fewer than `εF·j` of the largest `j` keys are outside `F₂`;
  * `fLow j`: symmetric for the smallest keys and `F₁`.
-/

public import AKS.Sort.Defs

@[expose] public section

namespace Chvatal

/-- Block boundaries (in cells) of a node that sends `π` wires up and `τ` wires to each of
    its 64 children: `π/2 + j·τ` for `j = 0, …, 64`. -/
def blockBounds (π τ : ℕ) : Finset ℕ := (Finset.range 65).image fun j => π / 2 + j * τ

/-- Two-sided position form of the Theorem 5.1 separator guarantee for one node. -/
structure NodeSpec (a π τ : ℕ) (net : ComparatorNetwork a) (EB : ℝ) (Jmax : ℕ) (εF : ℝ) :
    Prop where
  bHigh : ∀ (x : Equiv.Perm (Fin a)), ∀ p ∈ blockBounds π τ, p ≤ a →
    ((Finset.univ.filter fun c : Fin a =>
        a - p ≤ (net.exec (x : Fin a → Fin a) c).val ∧ c.val < a - p).card : ℝ) ≤ EB
  bLow : ∀ (x : Equiv.Perm (Fin a)), ∀ p ∈ blockBounds π τ, p ≤ a →
    ((Finset.univ.filter fun c : Fin a =>
        (net.exec (x : Fin a → Fin a) c).val < p ∧ p ≤ c.val).card : ℝ) ≤ EB
  fHigh : ∀ (x : Equiv.Perm (Fin a)) (j : ℕ), 0 < j → j ≤ Jmax → j ≤ a →
    ((Finset.univ.filter fun c : Fin a =>
        a - j ≤ (net.exec (x : Fin a → Fin a) c).val ∧ c.val < a - π / 2).card : ℝ) < εF * j
  fLow : ∀ (x : Equiv.Perm (Fin a)) (j : ℕ), 0 < j → j ≤ Jmax → j ≤ a →
    ((Finset.univ.filter fun c : Fin a =>
        (net.exec (x : Fin a → Fin a) c).val < j ∧ π / 2 ≤ c.val).card : ℝ) < εF * j

end Chvatal
