import AKS.Chvatal.Lemma61
namespace Tapered945
open Chvatal

def cyclicShift16 {m : Nat} (r : Fin m) : Equiv.Perm (Fin 16) :=
  { toFun := fun k => ⟨(k.val+r.val)%16, Nat.mod_lt _ (by norm_num)⟩
    invFun := fun j => ⟨(j.val+16-r.val%16)%16, Nat.mod_lt _ (by norm_num)⟩
    left_inv := by
      intro k
      apply Fin.ext
      simp only [Nat.mod_eq_of_lt (show k.val < 16 by exact k.isLt)]
      omega
    right_inv := by
      intro j
      apply Fin.ext
      simp only [Nat.mod_eq_of_lt (show j.val < 16 by exact j.isLt)]
      omega }

def cyclicScramble16 {m : Nat} : Scramble m 16 := fun r => cyclicShift16 r

example {m : Nat} (r : Fin m) (k : Fin 16) :
    cyclicShift16 r k = ⟨(k.val+r.val)%16, Nat.mod_lt _ (by norm_num)⟩ := by
  rfl

end Tapered945
