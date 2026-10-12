import VariableSeparator
import Mathlib.Tactic

namespace Tapered945

open Chvatal

/-- A local ragged-flow profile for one parent bag.  `width j` is the number
of rows assigned to child `j`; `start` is the first parent row.  The prefix
bound lets every child boundary be used as a row-aligned cut in the two-round
separator theorem.  `conservation` says the child widths exactly fill the
parent interval. -/
structure RaggedFlowContract (m : Nat) where
  start : Nat
  rightFringe : Nat
  width : Nat → Nat
  widths_pos : ∀ j, j < 64 → 0 < width j
  conservation : start + (∑ j ∈ Finset.range 64, width j) + rightFringe = m
  cut_pos : ∀ j, 1 ≤ j → 1 ≤ start + raggedPrefixRows width j
  prefix_bound : ∀ j, j ≤ 64 →
    start + raggedPrefixRows width j ≤ m - rightFringe

/-- The two-sided separator contract at every internal cumulative child
boundary.  The profile can have unequal widths; only row alignment and the
two B2 guarantees are used. -/
theorem ragged_flow_boundary_bounds {m n : Nat} (hn : 0 < n)
    (σ₁ σ₂ : Scramble m n) {epsB : ℝ}
    (hBhigh : HasPackSemanticPropertyB2 hn σ₁ σ₂ epsB)
    (hBlow : HasPackSemanticPropertyB2 hn (flipScramble σ₁) (flipScramble σ₂) epsB)
    (x : Equiv.Perm (Fin (m * n))) (profile : RaggedFlowContract m)
    (j : Nat) (hj1 : 1 ≤ j) (hj64 : j ≤ 64) :
    ((Finset.univ.filter fun c : Fin (m * n) =>
      (profile.start + raggedPrefixRows profile.width j) * n ≤
          ((physicalPack2Net m n hn σ₁ σ₂).exec
            (x : Fin (m * n) → Fin (m * n)) c).val ∧
        c.val < (profile.start + raggedPrefixRows profile.width j) * n).card : ℝ) ≤
      (epsB / 2) * (m * n) ∧
    ((Finset.univ.filter fun c : Fin (m * n) =>
      ((physicalPack2Net m n hn σ₁ σ₂).exec
        (x : Fin (m * n) → Fin (m * n)) c).val <
          (profile.start + raggedPrefixRows profile.width j) * n ∧
        (profile.start + raggedPrefixRows profile.width j) * n ≤ c.val).card : ℝ) ≤
      (epsB / 2) * (m * n) := by
  have hlow : 1 ≤ profile.start + raggedPrefixRows profile.width j :=
    profile.cut_pos j hj1
  have hhigh : profile.start + raggedPrefixRows profile.width j ≤ m :=
    (profile.prefix_bound j hj64).trans (Nat.sub_le _ _)
  constructor
  · exact pack2_ragged_boundary_high hn σ₁ σ₂ hBhigh x profile.width j
      profile.start hlow hhigh
  · exact pack2_ragged_boundary_low hn σ₁ σ₂ hBlow x profile.width j
      profile.start hlow hhigh

/-- A child receives exactly its specified number of rows, by conservation;
this is the simple arithmetic form consumed by local scheduler proofs. -/
theorem ragged_flow_conservation_at_end {m : Nat}
    (profile : RaggedFlowContract m) :
    profile.start + raggedPrefixRows profile.width 64 + profile.rightFringe = m := by
  simpa [raggedPrefixRows] using profile.conservation

end Tapered945
