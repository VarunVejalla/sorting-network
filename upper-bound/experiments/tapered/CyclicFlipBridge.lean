import CyclicFlipScratch
import AKS.Chvatal.FlipSpec

namespace Tapered945
open Chvatal

/-- The scratch reversal is definitionally the repository flip operation. -/
theorem localFlipScramble16_eq_repository_flip {m : Nat} (σ : Scramble m 16) :
    localFlipScramble16 σ = flipScramble σ := rfl

/-- Kernel-checked 15-cap for the repository's flipped cyclic scramble. -/
theorem repositoryFlipCyclic16_firstRoundCap {m : Nat}
    (c : MonotoneColumnSums m 16) (i : Nat)
    (hmass : totalColumnOnes c = 16*i) (hi : i ≤ m) :
    ∀ j : Fin 16,
      scrambledColSum c (flipScramble cyclicScramble16) j ≤ i+15 := by
  change ∀ j : Fin 16,
      scrambledColSum c (localFlipScramble16 cyclicScramble16) j ≤ i+15
  exact localFlipCyclicScramble16_firstRoundCap c i hmass hi

end Tapered945
