module

public import AKS.Paterson.ChildSchedule

/-! # Bag labels after removing the leading half bit -/

@[expose] public section

namespace Paterson.Bags

def liftChildBag {k : ℕ} (hk : 1 ≤ k) (s : Fin 2) (b : Bag (k - 1)) : Bag k :=
  ⟨b.l + 1, s.val * 2 ^ b.l + b.x, by have := b.hl; omega, by
    have hs := s.isLt
    have hx := b.hx
    rw [pow_succ]
    nlinarith [pow_pos (by omega : 0 < (2 : ℕ)) b.l]⟩

def dropChildBag {k : ℕ} (b : Bag k) (hb : 1 ≤ b.l) : Bag (k - 1) :=
  ⟨b.l - 1, b.x % 2 ^ (b.l - 1), by have := b.hl; omega, Nat.mod_lt _ (by positivity)⟩

theorem drop_liftChildBag {k : ℕ} (hk : 1 ≤ k) (s : Fin 2) (b : Bag (k - 1)) :
    dropChildBag (liftChildBag hk s b) (by change 1 ≤ b.l + 1; omega) = b := by
  apply Bag.ext
  · change b.l + 1 - 1 = b.l; omega
  · change (s.val * 2 ^ b.l + b.x) % 2 ^ (b.l + 1 - 1) = b.x
    rw [Nat.add_sub_cancel, Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt b.hx]

theorem lift_dropChildBag {k : ℕ} (hk : 1 ≤ k) (s : Fin 2) (b : Bag k) (hb : 1 ≤ b.l)
    (hs : b.x / 2 ^ (b.l - 1) = s.val) :
    liftChildBag hk s (dropChildBag b hb) = b := by
  apply Bag.ext
  · change b.l - 1 + 1 = b.l; omega
  · change s.val * 2 ^ (b.l - 1) + b.x % 2 ^ (b.l - 1) = b.x
    rw [← hs]
    simpa only [mul_comm] using Nat.div_add_mod b.x (2 ^ (b.l - 1))

theorem liftChildBag_ancestor {k : ℕ} (hk : 1 ≤ k) (s : Fin 2) (b : Bag (k - 1))
    (j : ℕ) (hj : j ≤ b.l) :
    (liftChildBag hk s b).ancestor j = liftChildBag hk s (b.ancestor j) := by
  apply Bag.ext
  · change b.l + 1 - j = b.l - j + 1; omega
  · change (s.val * 2 ^ b.l + b.x) / 2 ^ j = s.val * 2 ^ (b.l - j) + b.x / 2 ^ j
    have hp : 2 ^ b.l = 2 ^ j * 2 ^ (b.l - j) := by
      rw [← pow_add, Nat.add_sub_of_le hj]
    calc (s.val * 2 ^ b.l + b.x) / 2 ^ j =
        (b.x + 2 ^ j * (s.val * 2 ^ (b.l - j))) / 2 ^ j := by
          congr 1
          rw [hp]
          ring
      _ = _ := by rw [Nat.add_mul_div_left _ _ (by positivity)]; omega

theorem liftChildBag_half {k : ℕ} (hk : 1 ≤ k) (s : Fin 2) (b : Bag (k - 1)) :
    (liftChildBag hk s b).x / 2 ^ ((liftChildBag hk s b).l - 1) = s.val := by
  change (s.val * 2 ^ b.l + b.x) / 2 ^ (b.l + 1 - 1) = s.val
  rw [Nat.add_sub_cancel, Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity),
    Nat.div_eq_of_lt b.hx, Nat.zero_add]

end Paterson.Bags
