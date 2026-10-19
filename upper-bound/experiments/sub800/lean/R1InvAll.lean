import R1InvNext

/-! # Design P at every stage (W1, step 19)

The base case (`t = 0, 1`), `J(t)` for `1 ≤ t ≤ t_f`, conservation at every stage `t < t_f`, the
flow table `designP d : FlowTableB d (tf d)`, and its parity and final-occupancy facts. -/

namespace R1T

open Finset
open Chvatal (KBag subtreeBags descendants mem_descendants subtreeBags_l_ge)

variable {d : ℕ}

/-! ### Stage 0 -/

theorem root_mem_subtree (b : KBag 16 d) :
    KBag.root 16 d ∈ subtreeBags 16 d (by norm_num) b ↔ b = KBag.root 16 d := by
  constructor
  · intro h
    have := subtreeBags_l_ge (by norm_num) b _ h
    have hl : b.l = 0 := by simpa [KBag.root] using this
    apply KBag.ext
    · exact hl
    · have := b.hx; rw [hl] at this; simp [KBag.root]; omega
  · rintro rfl
    unfold subtreeBags
    simp only [Finset.mem_biUnion, Finset.mem_range]
    exact ⟨0, by omega, by rw [descendants_zero]; exact Finset.mem_singleton_self _⟩

theorem Gof_zero (b : KBag 16 d) :
    Gof (aT d 0) b = if b = KBag.root 16 d then 0 else (16 : ℤ) ^ (d - b.l) := by
  unfold Gof
  have hsum : ∑ z ∈ subtreeBags 16 d (by norm_num) b, ((aT d 0 z : ℕ) : ℤ) =
      if b = KBag.root 16 d then (16 : ℤ) ^ d else 0 := by
    have : ∀ z, ((aT d 0 z : ℕ) : ℤ) = if z = KBag.root 16 d then (16 : ℤ) ^ d else 0 := fun z => by
      show (((if z = KBag.root 16 d then 16 ^ d else 0 : ℕ)) : ℤ) = _
      split_ifs <;> simp
    rw [Finset.sum_congr rfl (fun z _ => this z), Finset.sum_ite_eq']
    by_cases hb : b = KBag.root 16 d
    · rw [if_pos ((root_mem_subtree b).2 hb), if_pos hb]
    · rw [if_neg (fun h => hb ((root_mem_subtree b).1 h)), if_neg hb]
  rw [hsum]
  split_ifs with hb
  · subst hb; simp [KBag.root]
  · simp

theorem sends_zero_iff (hd : 10 ≤ d) (i : ℕ) : Sends d i 0 ↔ i = 0 := by
  have htf : 0 < tf d := by unfold tf; omega
  constructor
  · rintro ⟨⟨_, _, hω, _⟩, _⟩; simp [omega] at hω; omega
  · rintro rfl; exact ⟨⟨by omega, by simp [alpha], by simp [omega], rfl⟩, htf⟩

theorem topD_root_zero (hd : 10 ≤ d) : topD d 0 0 := ⟨by simp [alpha], by simp [alpha]⟩

theorem conserves_zero (hd : 10 ≤ d) : ∀ b : KBag 16 d, Conserves (aT d 0) 0 b := by
  intro b
  by_cases hS : Sends d b.l 0
  · have hb0 : b.l = 0 := (sends_zero_iff hd b.l).1 hS
    have hbr : b = KBag.root 16 d := by
      apply KBag.ext
      · exact hb0
      · have := b.hx; rw [hb0] at this; simp [KBag.root]; omega
    have hbl : b.l < d := by omega
    have hT : topD d b.l 0 := by rw [hb0]; exact topD_root_zero hd
    unfold Conserves upOf downOf
    rw [if_pos hS, if_neg (fun h : botR d b.l 0 => h.2.1 hT.1), piC_topD d _ 0 hT, zero_add]
    have hθ : ∀ j : Fin 16, thetaOf (aT d 0) 0 b hbl j = 0 := fun j => by unfold thetaOf; rw [if_pos hT]
    have hch : ∀ j : Fin 16, Gof (aT d 0) (b.child j.val j.isLt hbl) = (16 : ℤ) ^ (d - 1) := by
      intro j
      rw [Gof_zero, if_neg (fun h => by have := congrArg KBag.l h; simp [KBag.child, KBag.root] at this)]
      rw [show (b.child j.val j.isLt hbl).l = 1 by show b.l + 1 = 1; omega]
    have : ∀ j : Fin 16, (if h : Sends d b.l 0 ∧ b.l < d then
        (Gof (aT d 0) (b.child j.val j.isLt h.2) - thetaOf (aT d 0) 0 b h.2 j).toNat else 0) =
        16 ^ (d - 1) := by
      intro j
      rw [dif_pos ⟨hS, hbl⟩, hθ j, hch j, sub_zero]
      exact_mod_cast Int.toNat_natCast (16 ^ (d - 1))
    rw [Finset.sum_congr rfl (fun j _ => this j), Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul]
    show (if b = KBag.root 16 d then 16 ^ d else 0) = _
    rw [if_pos hbr, show d = (d - 1) + 1 by omega, pow_succ]
    simp only [Nat.add_sub_cancel]; ring
  · unfold Conserves upOf downOf
    rw [if_neg hS]
    simp only [dif_neg (fun h : Sends d b.l 0 ∧ b.l < d => hS h.1), Finset.sum_const_zero, add_zero]
    show (if b = KBag.root 16 d then 16 ^ d else 0) = 0
    rw [if_neg]
    rintro rfl
    exact hS ((sends_zero_iff hd 0).2 rfl)

/-! ### Stage 1 -/

theorem J_one (hd : 10 ≤ d) : JInv d 1 := by
  have hG : ∀ b, Gof (aT d 1) b = Gof (aT d 0) b + upOf (aT d 0) 0 b - downIn (aT d 0) 0 b :=
    fun b => Gof_next (aT d 0) 0 (conserves_zero hd) b
  have hup0 : ∀ b : KBag 16 d, upOf (aT d 0) 0 b = 0 := by
    intro b
    by_cases hS : Sends d b.l 0
    · have hb0 := (sends_zero_iff hd b.l).1 hS
      have hT : topD d b.l 0 := by rw [hb0]; exact topD_root_zero hd
      rw [upOf_of_sends _ 0 b hS (fun h => h.2.1 hT.1), piC_topD d _ 0 hT]
    · exact upOf_of_not_sends _ 0 b hS
  have hα1 := alpha_one d
  have hω1 := omega_one
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro b hna
    show nextA (aT d 0) 0 b = 0
    unfold nextA
    have hin : (if 1 ≤ b.l then downOf (aT d 0) 0 b.parent ⟨b.x % 16, Nat.mod_lt _ (by norm_num)⟩
        else 0) = 0 := by
      show downIn (aT d 0) 0 b = 0
      by_cases h1 : 1 ≤ b.l
      · refine downIn_not_sends _ 0 b h1 (fun h => ?_)
        have := (sends_zero_iff hd _).1 h
        exact hna ⟨by unfold tf; omega, by omega, by omega, by omega⟩
      · exact downIn_root _ 0 b (by omega)
    rw [hin, zero_add]
    split_ifs
    · exact Finset.sum_eq_zero fun j _ => hup0 _
    · rfl
  · intro b hb
    rw [hG b, hup0 b, Nat.cast_zero, add_zero]
    rcases Nat.lt_or_ge b.l 1 with h0 | h1
    · have hbr : b = KBag.root 16 d := by
        apply KBag.ext
        · simp [KBag.root]; omega
        · have := b.hx; have hl : b.l = 0 := by omega
          rw [hl] at this; simp [KBag.root]; omega
      rw [Gof_zero, if_pos hbr, downIn_root _ 0 b (by omega)]; simp
    · have hbl1 : b.l = 1 := by omega
      have hS : Sends d (b.l - 1) 0 := (sends_zero_iff hd _).2 (by omega)
      have hT : topD d (b.l - 1) 0 := by rw [show b.l - 1 = 0 by omega]; exact topD_root_zero hd
      rw [downIn_topD _ 0 b h1 hS hT, Gof_zero, if_neg (fun h => by
        have := congrArg KBag.l h; simp [KBag.root] at this; omega)]
      have : (0 : ℤ) ≤ 16 ^ (d - b.l) := by positivity
      rw [Int.toNat_of_nonneg this]; ring
  · intro b hb
    rw [hG b, hup0 b, Nat.cast_zero, add_zero, Gof_zero, if_neg (fun h => by
        have := congrArg KBag.l h; simp [KBag.root] at this; omega)]
    rw [downIn_not_sends _ 0 b (by omega) (fun h => by have := (sends_zero_iff hd _).1 h; omega)]
    simp
  · intro b hA hlt; have := hA.2.2.1; omega
  · intro b _ hlt hlt'; omega

/-! ### All stages -/

theorem J_all (hd : 10 ≤ d) : ∀ t, 1 ≤ t → t ≤ tf d → JInv d t := by
  intro t ht1 htf
  induction t, ht1 using Nat.le_induction with
  | base => exact J_one hd
  | succ t ht1 ih => exact J_next hd t ht1 (by omega) (ih (by omega))

theorem conserves_all (hd : 10 ≤ d) : ∀ t, t < tf d → ∀ b : KBag 16 d, Conserves (aT d t) t b := by
  intro t ht
  rcases Nat.eq_zero_or_pos t with rfl | ht1
  · exact conserves_zero hd
  · exact conserves_of_J hd t ht1 ht (J_all hd t ht1 ht.le)

end R1T
