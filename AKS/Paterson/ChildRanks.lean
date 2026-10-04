module

public import AKS.Paterson.ChildPlacement

/-! # Exact rank translation between a native half and its smaller tree -/

@[expose] public section

namespace Paterson.Bags

def dropChildRank {k : ℕ} (r : Fin (2 ^ k)) : Fin (2 ^ (k - 1)) :=
  ⟨r.val % 2 ^ (k - 1), Nat.mod_lt _ (by positivity)⟩

def liftChildRank {k : ℕ} (hk : 1 ≤ k) (s : Fin 2) :
    Fin (2 ^ (k - 1)) ↪o Fin (2 ^ k) where
  toFun r := ⟨s.val * 2 ^ (k - 1) + r.val, by
    have hpow : 2 ^ k = 2 * 2 ^ (k - 1) := by rw [← pow_succ', Nat.sub_add_cancel hk]
    have hs := s.isLt
    have hr := r.isLt
    rw [hpow]
    nlinarith [pow_pos (by omega : 0 < (2 : ℕ)) (k - 1)]⟩
  inj' := by intro a b h; apply Fin.ext; have := congrArg Fin.val h; dsimp only at this; omega
  map_rel_iff' := by intro a b; change s.val * 2 ^ (k - 1) + a.val ≤
      s.val * 2 ^ (k - 1) + b.val ↔ a.val ≤ b.val; omega

theorem drop_liftChildRank {k : ℕ} (hk : 1 ≤ k) (s : Fin 2) (r : Fin (2 ^ (k - 1))) :
    dropChildRank (liftChildRank hk s r) = r := by
  apply Fin.ext
  change (s.val * 2 ^ (k - 1) + r.val) % 2 ^ (k - 1) = r.val
  rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt r.isLt]

theorem lift_dropChildRank {k : ℕ} (hk : 1 ≤ k) (s : Fin 2) (r : Fin (2 ^ k))
    (hr : nativeBagIdx k 1 r.val = s.val) :
    liftChildRank hk s (dropChildRank r) = r := by
  have hs : r.val / 2 ^ (k - 1) = s.val := by
    simpa only [nativeBagIdx, bagSize, Nat.pow_div hk (by norm_num : 0 < (2 : ℕ))] using hr
  apply Fin.ext
  change s.val * 2 ^ (k - 1) + r.val % 2 ^ (k - 1) = r.val
  rw [← hs]
  simpa only [mul_comm] using Nat.div_add_mod r.val (2 ^ (k - 1))

theorem liftChildRank_nativeIdx {k : ℕ} (hk : 1 ≤ k) (s : Fin 2)
    (r : Fin (2 ^ (k - 1))) {L : ℕ} (hL : L ≤ k - 1) :
    nativeBagIdx k (L + 1) (liftChildRank hk s r).val =
      s.val * 2 ^ L + nativeBagIdx (k - 1) L r.val := by
  have hsize : bagSize k (L + 1) = bagSize (k - 1) L := by
    simp only [bagSize, Nat.pow_div (by omega : L + 1 ≤ k) (by norm_num : 0 < (2 : ℕ)),
      Nat.pow_div hL (by norm_num : 0 < (2 : ℕ))]
    congr 1
    omega
  have hp : 2 ^ (k - 1) = bagSize (k - 1) L * 2 ^ L := by
    unfold bagSize
    rw [Nat.pow_div hL (by norm_num : 0 < (2 : ℕ)), ← pow_add]
    congr 1
    omega
  change (s.val * 2 ^ (k - 1) + r.val) / bagSize k (L + 1) = _
  have heq : s.val * 2 ^ (k - 1) + r.val =
      r.val + bagSize (k - 1) L * (s.val * 2 ^ L) := by
    calc s.val * 2 ^ (k - 1) + r.val =
        s.val * (bagSize (k - 1) L * 2 ^ L) + r.val :=
          congrArg (fun z ↦ s.val * z + r.val) hp
      _ = _ := by ring
  rw [hsize, heq, Nat.add_mul_div_left _ _ (bagSize_pos hL)]
  unfold nativeBagIdx
  omega

theorem child_native_iff {k : ℕ} (hk : 1 ≤ k) (s : Fin 2) (b : Bag (k - 1))
    (r : Fin (2 ^ (k - 1))) :
    nativeBagIdx k (liftChildBag hk s b).l (liftChildRank hk s r).val =
      (liftChildBag hk s b).x ↔ nativeBagIdx (k - 1) b.l r.val = b.x := by
  change nativeBagIdx k (b.l + 1) (liftChildRank hk s r).val = s.val * 2 ^ b.l + b.x ↔ _
  rw [liftChildRank_nativeIdx hk s r b.hl]
  omega

theorem child_strange_iff {k : ℕ} (hk : 1 ≤ k) (s : Fin 2) (b : Bag (k - 1))
    {j : ℕ} (hj : 1 ≤ j) (hjb : j ≤ b.l + 1) (r : Fin (2 ^ (k - 1))) :
    (j = 0 ∨ nativeBagIdx k ((liftChildBag hk s b).ancestor (j - 1)).l
      (liftChildRank hk s r).val ≠ ((liftChildBag hk s b).ancestor (j - 1)).x) ↔
      (j = 0 ∨ nativeBagIdx (k - 1) (b.ancestor (j - 1)).l r.val ≠
        (b.ancestor (j - 1)).x) := by
  rw [liftChildBag_ancestor hk s b (j - 1) (by omega)]
  simp only [show j ≠ 0 by omega, false_or]
  exact not_congr (child_native_iff hk s (b.ancestor (j - 1)) r)

end Paterson.Bags
