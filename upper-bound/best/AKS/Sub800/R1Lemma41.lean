import AKS.Sub800.R1Kernel

/-! # Lemma 4.1′ in deficit form (W1, step 8)

`keys_below_child_le`: under `P` at stage `t`, a node `u` on an occupied level holds at most
`R_w − W_w + μ·sib·c(u.l, t)` keys addressed below its child `w`, where `R_w = 16^(d−u.l−1)` and
`W_w = Σ_{z ∈ subtree(w)} |regs z|` (so `R_w − W_w` is the deficit `G_w`). -/

namespace R1T

variable {sc : R1Scal}

open Finset
open Chvatal (KBag Placement subtreeBags subtreeKeys descendants mem_descendants
  descendants_card descendants_disjoint subtreeBags_l_ge native_card odd_geom_le)

variable (d t : ℕ)

/-- Strangers in a subtree under `P`, with per-bag sizes `a`. -/
theorem subtree_bad_le (pl : Placement 16 d) (a : KBag 16 d → ℕ)
    (hcard : ∀ b : KBag 16 d, (pl.regs b).card = a b)
    (hpar : ∀ b : KBag 16 d, b.l % 2 ≠ t % 2 → a b = 0)
    (hP : OutsiderBoundLe sc d t pl id) (w : KBag 16 d) :
    (((subtreeKeys 16 d pl (by norm_num) w).filter fun κ => ¬ w.Native κ id).card : ℚ) ≤
      ∑ h ∈ (range (d - w.l + 1)).filter (fun h => (w.l + h) % 2 = t % 2),
        (16 : ℚ) ^ h * (sc.mu * sc.delta ^ h * cap d (w.l + h) t) := by
  have hbr : 1 ≤ 16 := by norm_num
  unfold subtreeKeys subtreeBags
  rw [Finset.filter_biUnion, Finset.card_biUnion (fun z _ z' _ hne =>
    Finset.disjoint_filter_filter (pl.disjoint z z' hne)),
    Finset.sum_biUnion (fun h _ h' _ hne => descendants_disjoint hbr w hne)]
  push_cast
  rw [Finset.sum_filter]
  refine Finset.sum_le_sum fun h hh => ?_
  rw [Finset.mem_range] at hh
  have hc := descendants_card hbr w h (by have := w.hl; omega)
  split_ifs with hpt
  · rw [show (16 : ℚ) ^ h = ((descendants 16 d hbr w h).card : ℚ) by rw [hc]; push_cast; rfl,
      ← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun z hz => ?_
    have hzl := ((mem_descendants hbr w h z).mp hz).1
    have h1 : ((pl.regs z).filter fun κ => ¬ w.Native κ id).card ≤
        z.strangers (h + 1) id (pl.regs z) hbr := by
      unfold KBag.strangers
      refine Finset.card_le_card fun κ hκ => ?_
      rw [Finset.mem_filter] at hκ ⊢
      refine ⟨hκ.1, Or.inr ?_⟩
      simpa [((Finset.mem_filter.mp hz).2).2] using hκ.2
    have h2 := hP z h (by omega)
    rw [hzl] at h2
    exact le_trans (by exact_mod_cast h1) h2
  · refine le_of_eq (Finset.sum_eq_zero fun z hz => ?_)
    have hzl := ((mem_descendants hbr w h z).mp hz).1
    have := hpar z (by rw [hzl]; exact hpt)
    have h0 : ((pl.regs z).filter fun κ => ¬ w.Native κ id).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro κ hκ
      have hz0 : (pl.regs z).card = 0 := by rw [hcard]; exact this
      rw [Finset.card_eq_zero] at hz0
      rw [hz0] at hκ; simp at hκ
    rw [h0]; simp

theorem cap_add (m i : ℕ) : cap d (i + m) t = (32 : ℚ) ^ m * cap d i t := by
  induction m with
  | zero => simp
  | succ m ih => rw [← add_assoc, cap_succ_level, ih]; ring

/-- The odd-depth series below a child: at most `μ · sib · c(i, t)`. -/
theorem sibling_sum_le (i M : ℕ) :
    ∑ h ∈ (range M).filter (fun h => h % 2 = 1),
        (16 : ℚ) ^ h * (sc.mu * sc.delta ^ h * cap d (i + 1 + h) t) ≤ sc.mu * sc.sib * cap d i t := by
  set x : ℚ := sc.delta * 16 * 32 with hx
  have hc := cap_pos d i t
  have hx0 : 0 ≤ x := by have := sc.delta_pos; positivity
  have hx2 : x ^ 2 = sc.delta ^ 2 * (16 : ℚ) ^ 2 * (32 : ℚ) ^ 2 := by rw [hx]; ring
  have hterm : ∀ h : ℕ, (16 : ℚ) ^ h * (sc.mu * sc.delta ^ h * cap d (i + 1 + h) t) =
      (sc.mu * 32 * cap d i t) * x ^ h := by
    intro h
    rw [show i + 1 + h = i + (1 + h) by ring, cap_add, hx, mul_pow, mul_pow]; ring
  rw [Finset.sum_congr rfl (fun h _ => hterm h), ← Finset.mul_sum]
  calc (sc.mu * 32 * cap d i t) * ∑ h ∈ (range M).filter (fun h => h % 2 = 1), x ^ h
      ≤ (sc.mu * 32 * cap d i t) * (x / (1 - x ^ 2)) :=
        mul_le_mul_of_nonneg_left (odd_geom_le x hx0 (hx2 ▸ sc.cond_sib) M)
          (by have := sc.mu_pos; positivity)
    _ = sc.mu * sc.sib * cap d i t := by
        unfold R1Scal.sib
        rw [hx2, hx]; ring

/-- **Lemma 4.1′ (deficit form).** -/
theorem keys_below_child_le (pl : Placement 16 d) (a : KBag 16 d → ℕ)
    (hcard : ∀ b : KBag 16 d, (pl.regs b).card = a b)
    (hpar : ∀ b : KBag 16 d, b.l % 2 ≠ t % 2 → a b = 0)
    (hP : OutsiderBoundLe sc d t pl id)
    (u : KBag 16 d) (hul : u.l < d) (j : ℕ) (hj : j < 16) (hu : u.l % 2 = t % 2) :
    (((pl.regs u).filter fun κ => (u.child j hj hul).Native κ id).card : ℚ) ≤
      (16 : ℚ) ^ (d - u.l - 1) -
        ∑ z ∈ subtreeBags 16 d (by norm_num) (u.child j hj hul), (a z : ℚ) +
        sc.mu * sc.sib * cap d u.l t := by
  have hbr : 1 ≤ 16 := by norm_num
  set w : KBag 16 d := u.child j hj hul with hw
  have hwl : w.l = u.l + 1 := rfl
  set S := subtreeKeys 16 d pl hbr w with hS
  set X := (pl.regs u).filter fun κ => w.Native κ id with hX
  set Y := S.filter fun κ => w.Native κ id with hY
  set A := (Finset.univ : Finset (Fin (16 ^ d))).filter fun κ => w.Native κ id with hA
  have hAcard : A.card = 16 ^ (d - u.l - 1) := by
    have h1 := native_card hbr w
    rwa [hwl, show d - (u.l + 1) = d - u.l - 1 by omega] at h1
  have hdisjS : Disjoint (pl.regs u) S := by
    rw [hS, subtreeKeys, Finset.disjoint_biUnion_right]
    intro z hz
    refine pl.disjoint u z fun e => ?_
    have := subtreeBags_l_ge hbr w z hz
    rw [← e] at this
    omega
  have hcardXY : X.card + Y.card ≤ A.card := by
    rw [← Finset.card_union_of_disjoint
      (Finset.disjoint_of_subset_left (Finset.filter_subset _ _)
        (Finset.disjoint_of_subset_right (Finset.filter_subset _ _) hdisjS))]
    refine Finset.card_le_card (Finset.union_subset ?_ ?_) <;>
      exact fun κ hκ => mem_filter.2 ⟨mem_univ _, (mem_filter.1 hκ).2⟩
  have hsplit := Finset.card_filter_add_card_filter_not (s := S) (fun κ => w.Native κ id)
  have hScard : (S.card : ℚ) = ∑ z ∈ subtreeBags 16 d hbr w, (a z : ℚ) := by
    rw [hS, subtreeKeys, Finset.card_biUnion (fun z _ z' _ hne => pl.disjoint z z' hne)]
    push_cast
    exact Finset.sum_congr rfl fun z _ => by rw [hcard]
  have hbad : (((S.filter fun κ => ¬ w.Native κ id).card : ℕ) : ℚ) ≤ sc.mu * sc.sib * cap d u.l t := by
    refine (subtree_bad_le d t pl a hcard hpar hP w).trans ?_
    rw [Finset.filter_congr (fun h _ => by rw [hwl]; omega : ∀ h ∈ Finset.range (d - w.l + 1),
      (w.l + h) % 2 = t % 2 ↔ h % 2 = 1), hwl]
    exact sibling_sum_le d t u.l _
  have c1 : ((X.card + Y.card : ℕ) : ℚ) ≤ A.card := by exact_mod_cast hcardXY
  have c2 : ((Y.card + (S.filter fun κ => ¬ w.Native κ id).card : ℕ) : ℚ) = S.card := by
    exact_mod_cast hsplit
  have hAq : ((A.card : ℕ) : ℚ) = (16 : ℚ) ^ (d - u.l - 1) := by rw [hAcard]; push_cast; rfl
  push_cast at c1 c2 hbad hAq
  linarith

end R1T
