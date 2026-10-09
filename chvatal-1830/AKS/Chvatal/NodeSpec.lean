module

public import AKS.Sort.Defs

/-! # Node separator specification

A node on `a` wires runs `net`; its output `y = net.exec x` (`x` a permutation of `Fin a`, `y c` = rank of
the key at cell `c`) is cut into the first `π/2` cells (`F₁`), the last `π/2` cells (`F₂`) and 64 blocks
of `τ` middle cells. `NodeSpec` is the two-sided Theorem 5.1 guarantee: `bHigh`/`bLow` bound the
misplaced largest/smallest `p` keys at block boundaries by `EB`; `fHigh`/`fLow` bound those outside
`F₂`/`F₁` by `εF·j` for `0 < j ≤ Jmax`. -/

@[expose] public section

namespace Chvatal

/-- Block boundaries `π/2 + j·τ`, `j = 0, …, 64`. -/
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
