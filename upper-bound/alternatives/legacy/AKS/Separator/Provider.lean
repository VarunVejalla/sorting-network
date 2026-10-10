module

public import AKS.Separator.SepProof

/-! # Separator providers for the bag scheduler

The scheduler needs separators at a varying effective fringe fraction.
Correctness holds at every such fraction; depth is uniformly bounded once
that fraction exceeds the base fraction. This interface permits replacing
the MGG construction without changing the bag invariant.
-/

@[expose] public section

structure BagSeparators (γ ε : ℚ) where
  depth : ℕ
  net : (δ : ℚ) → 0 < δ → (m : ℕ) → ComparatorNetwork (2 * m)
  isSeparator : ∀ δ hδ, δ ≤ 1 / 2 → ∀ m, IsSeparator (net δ hδ m) δ ε
  isHalver : ∀ δ hδ m, IsEpsilonHalver (net δ hδ m) ε
  depth_le : ∀ δ hδ, γ ≤ δ → ∀ m, (net δ hδ m).depth ≤ depth

def mggBagSeparators (γ ε : ℚ) (hγ : 0 < γ) (hε : 0 < ε) : BagSeparators γ ε where
  depth := separatorDepth γ ε hγ hε
  net δ hδ m := separatorNet δ ε hδ hε m
  isSeparator δ hδ hd m := separatorNet_isSeparator δ ε hδ hε hd m
  isHalver δ hδ m := separatorNet_isHalver δ ε hδ hε m
  depth_le δ hδ hd m := (separatorNet_depth_le δ ε hδ hε m).trans
    (separatorDepth_antitone hγ hδ hd hε)
