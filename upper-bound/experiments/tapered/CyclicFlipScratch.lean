import CyclicCapBridge
import Mathlib.Data.Fin.Rev
import Mathlib.Tactic

namespace Tapered945
open Chvatal

set_option maxHeartbeats 500000

def localFlipScramble16 {m : Nat} (σ : Scramble m 16) : Scramble m 16 :=
  fun r => Fin.revPerm * σ (Fin.rev r) * Fin.revPerm

theorem localFlipCyclic16_value {m : Nat} (r : Fin m) (j : Fin 16) :
    (localFlipScramble16 cyclicScramble16 r j).val =
      (j.val+r.val+(17-m%16)%16)%16 := by
  simp [localFlipScramble16, cyclicScramble16, cyclicShift16, Fin.revPerm,
    Fin.rev, Fin.ext_iff]
  have hm : m % 16 < 16 := Nat.mod_lt _ (by norm_num)
  have hr : r.val < m := r.isLt
  have hj : j.val < 16 := j.isLt
  omega

/-- The same 15-cap holds for the defining row/column reversal of the cyclic
scramble, since it is an affine cyclic shift with offset `1-m` modulo 16. -/
theorem localFlipCyclicScramble16_firstRoundCap {m : Nat}
    (c : MonotoneColumnSums m 16) (i : Nat)
    (hmass : totalColumnOnes c = 16*i) (hi : i ≤ m) :
    ∀ j : Fin 16,
      scrambledColSum c (localFlipScramble16 cyclicScramble16) j ≤ i+15 := by
  have hformula : ∀ r : Fin m, ∀ k : Fin 16,
      (localFlipScramble16 cyclicScramble16 r k).val =
        (k.val+r.val+(17-m%16)%16)%16 := by
    exact localFlipCyclic16_value
  exact affineScramble16_firstRoundCap (localFlipScramble16 cyclicScramble16)
    ((17-m%16)%16) hformula c i hmass hi

end Tapered945
