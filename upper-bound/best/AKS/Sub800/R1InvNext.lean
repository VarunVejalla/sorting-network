import AKS.Sub800.R1InvStep

/-! # Invariants of design P (W1, step 18): `J(t) → J(t+1)`, the base case, and all stages -/

namespace R1T

open Finset
open Chvatal (KBag subtreeBags)

variable {d : ℕ}

/-! ### Schedule values at `t = 1, 2` -/

theorem alpha_one (d : ℕ) : alpha d 1 = 1 := by simp [alpha]
theorem omega_one : omega 1 = 1 := by simp [omega]
theorem omega_two : omega 2 = 2 := by decide
theorem alpha_two (d : ℕ) (hd : 10 ≤ d) : alpha d 2 = 0 := by
  have : alphaLo d 2 = 0 := by unfold alphaLo; rw [if_pos (by omega)]
  simp [alpha, this, ceilParity]

/-! ### Evaluating the flows -/

theorem upOf_of_not_sends (A : KBag 16 d → ℕ) (t : ℕ) (b : KBag 16 d) (h : ¬ Sends d b.l t) :
    upOf A t b = 0 := by unfold upOf; rw [if_neg h]

theorem upOf_of_sends (A : KBag 16 d → ℕ) (t : ℕ) (b : KBag 16 d) (h : Sends d b.l t)
    (hB : ¬ botR d b.l t) : upOf A t b = piC d b.l t := by unfold upOf; rw [if_pos h, if_neg hB]

theorem upOf_botR (A : KBag 16 d → ℕ) (t : ℕ) (b : KBag 16 d) (h : Sends d b.l t)
    (hB : botR d b.l t) : upOf A t b = A b := by unfold upOf; rw [if_pos h, if_pos hB]

theorem downIn_root (A : KBag 16 d → ℕ) (t : ℕ) (b : KBag 16 d) (h : b.l = 0) : downIn A t b = 0 := by
  unfold downIn; rw [if_neg (by omega)]

theorem downIn_not_sends (A : KBag 16 d → ℕ) (t : ℕ) (b : KBag 16 d) (hb : 1 ≤ b.l)
    (h : ¬ Sends d (b.l - 1) t) : downIn A t b = 0 := by
  rw [downIn_eq A t b hb, dif_neg h]

theorem downIn_topD (A : KBag 16 d → ℕ) (t : ℕ) (b : KBag 16 d) (hb : 1 ≤ b.l)
    (h : Sends d (b.l - 1) t) (hT : topD d (b.l - 1) t) : downIn A t b = (Gof A b).toNat := by
  rw [downIn_eq A t b hb, dif_pos h]
  unfold thetaOf; rw [if_pos (show topD d b.parent.l t from hT), sub_zero]

theorem downIn_botR (A : KBag 16 d → ℕ) (t : ℕ) (b : KBag 16 d) (hb : 1 ≤ b.l)
    (h : Sends d (b.l - 1) t) (hB : botR d (b.l - 1) t) : downIn A t b = 0 := by
  rw [downIn_eq A t b hb, dif_pos h]
  have hT : ¬ topD d b.parent.l t := fun h' => hB.2.1 h'.1
  unfold thetaOf; rw [if_neg hT, if_pos (show botR d b.parent.l t from hB)]
  have hp : b.parent.l < d := by show b.l - 1 < d; have := b.hl; omega
  rw [show Gof A (b.parent.child (b.x % 16) (Nat.mod_lt _ (by norm_num)) hp) = Gof A b from
    congrArg (Gof A) (parent_child_self b hb hp), sub_self]; rfl

/-! ### The step -/

set_option maxHeartbeats 1000000

section Step

variable (hd : 10 ≤ d) (t : ℕ) (ht1 : 1 ≤ t) (htf : t < tf d) (hJ : JInv d t)
include hd ht1 htf hJ

/-- The deficit after the stage. -/
theorem G_next (b : KBag 16 d) :
    Gof (aT d (t + 1)) b = Gof (aT d t) b + upOf (aT d t) t b - downIn (aT d t) t b :=
  Gof_next (aT d t) t (conserves_of_J hd t ht1 htf hJ) b

/-- A middle sender's `θ` for a child, and the inflow it receives. -/
theorem downIn_mid (b : KBag 16 d) (hb : 1 ≤ b.l) (h : Sends d (b.l - 1) t)
    (hT : ¬ topD d (b.l - 1) t) (hB : ¬ botR d (b.l - 1) t) :
    ∃ θ : ℤ, 0 ≤ θ ∧ θ ≤ (2 : ℤ) ^ (eN d (b.l - 1) t - 13) ∧
      (downIn (aT d t) t b : ℤ) = Gof (aT d t) b - θ := by
  have hp : b.parent.l < d := by show b.l - 1 < d; have := b.hl; omega
  have hpS : Sends d b.parent.l t := h
  set j : Fin 16 := ⟨b.x % 16, Nat.mod_lt _ (by norm_num)⟩
  have hbd := sender_theta_bounds hd t ht1 htf hJ b.parent hpS hT hB hp j
  have hlb := sender_child_lb hd t ht1 htf hJ b.parent hpS hT hB hp j
  have hc : b.parent.child j.val j.isLt hp = b := parent_child_self b hb hp
  rw [hc] at hlb
  refine ⟨thetaOf (aT d t) t b.parent hp j, hbd.1, hbd.2, ?_⟩
  rw [downIn_eq _ t b hb, dif_pos h, Int.toNat_of_nonneg (by linarith [hbd.2])]

theorem J1_next : ∀ b : KBag 16 d, ¬ Active d b.l (t + 1) → aT d (t + 1) b = 0 := by
  intro b hna
  have hpa := alpha_parity d t
  have hpa1 := alpha_parity d (t + 1)
  have hpo := omega_parity t
  have hpo1 := omega_parity (t + 1)
  have hαs := alpha_step_exact d hd t
  have hωs := omega_step_exact t
  have hle := omega_le d t hd htf.le
  have hna' : ¬ (alpha d (t + 1) ≤ b.l ∧ b.l ≤ omega (t + 1) ∧ b.l % 2 = (t + 1) % 2) :=
    fun h => hna ⟨by omega, h.1, h.2.1, h.2.2⟩
  have hαω1 : t = 1 → alpha d t = 1 ∧ omega t = 1 ∧ alpha d (t + 1) = 0 ∧ omega (t + 1) = 2 := by
    rintro rfl
    exact ⟨alpha_one d, omega_one, alpha_two d hd, omega_two⟩
  have hαω : 2 ≤ t → alpha d t < omega t := fun h2 => alpha_lt_omega d t hd h2 htf
  show nextA (aT d t) t b = 0
  unfold nextA
  have hin : downIn (aT d t) t b = 0 := by
    by_cases hb : 1 ≤ b.l
    · by_cases hS : Sends d (b.l - 1) t
      · obtain ⟨⟨_, hα, hω, hpar⟩, _⟩ := hS
        have hB : botR d (b.l - 1) t := by
          rcases Nat.lt_or_ge t 2 with h1 | h2
          · have := hαω1 (by omega); exfalso; apply hna'; omega
          · have := hαω h2
            refine ⟨?_, ?_, ?_⟩
            · by_contra hne; apply hna'; omega
            · intro h; apply hna'; omega
            · intro h; apply hna'; omega
        exact downIn_botR _ t b hb ⟨⟨by omega, hα, hω, hpar⟩, htf⟩ hB
      · exact downIn_not_sends _ t b hb hS
    · exact downIn_root _ t b (by omega)
  have hin' : (if 1 ≤ b.l then downOf (aT d t) t b.parent ⟨b.x % 16, Nat.mod_lt _ (by norm_num)⟩
      else 0) = 0 := hin
  rw [hin', zero_add]
  split_ifs with hbl
  · refine Finset.sum_eq_zero fun j _ => ?_
    have hcl : (b.child j.val j.isLt hbl).l = b.l + 1 := rfl
    by_cases hS : Sends d (b.l + 1) t
    · obtain ⟨⟨_, hα, hω, hpar⟩, _⟩ := hS
      have hT : topD d (b.l + 1) t := by
        rcases Nat.lt_or_ge t 2 with h1 | h2
        · have := hαω1 (by omega); exfalso; apply hna'; omega
        · have := hαω h2
          refine ⟨?_, ?_⟩
          · by_contra hne; apply hna'; omega
          · by_contra hne; apply hna'; omega
      rw [upOf_of_sends _ t _ (by rw [hcl]; exact ⟨⟨by omega, hα, hω, hpar⟩, htf⟩)
        (by rw [hcl]; exact fun h => h.2.1 hT.1), hcl, piC_topD d _ t hT]
    · exact upOf_of_not_sends _ t _ (by rw [hcl]; exact hS)
  · rfl

/-- Wrong-parity nodes below the top have nonnegative deficits. -/
theorem G_nonneg_wrong (b : KBag 16 d) (hpar : b.l % 2 ≠ t % 2) (hα : alpha d t < b.l) :
    0 ≤ Gof (aT d t) b := by
  obtain ⟨-, -, hJ3, -, hJ5⟩ := hJ
  have hpo := omega_parity t
  rcases Nat.lt_or_ge b.l (omega t) with h | h
  · exact le_trans (by positivity) (hJ5 b hpar hα h).1
  · rw [hJ3 b (by omega)]; positivity

theorem J2_next : ∀ b : KBag 16 d, b.l ≤ alpha d (t + 1) → Gof (aT d (t + 1)) b = 0 := by
  intro b hb
  have hpa := alpha_parity d t
  have hpa1 := alpha_parity d (t + 1)
  have hαs := alpha_step_exact d hd t
  rw [G_next hd t ht1 htf hJ b]
  have hJ2 := hJ.2.1
  rcases Nat.lt_or_ge b.l (alpha d (t + 1)) with hlt | hge
  · -- strictly above the new top
    have hG : Gof (aT d t) b = 0 := hJ2 b (by omega)
    have hup : upOf (aT d t) t b = 0 := by
      by_cases hS : Sends d b.l t
      · have hT : topD d b.l t := by
          obtain ⟨⟨_, hα, _, _⟩, _⟩ := hS
          exact ⟨by omega, by omega⟩
        rw [upOf_of_sends _ t b hS (fun h => h.2.1 hT.1), piC_topD d _ t hT]
      · exact upOf_of_not_sends _ t b hS
    have hdn : downIn (aT d t) t b = 0 := by
      by_cases h1 : 1 ≤ b.l
      · exact downIn_not_sends _ t b h1 (fun h => by obtain ⟨⟨_, hα, _, _⟩, _⟩ := h; omega)
      · exact downIn_root _ t b (by omega)
    rw [hG, hup, hdn]; simp
  · have heq : b.l = alpha d (t + 1) := by omega
    rcases hαs with hdesc | hrise
    · -- the top descended: `b` is a child of the descending top
      have hup : upOf (aT d t) t b = 0 :=
        upOf_of_not_sends _ t b (fun h => by obtain ⟨⟨_, _, _, hp⟩, _⟩ := h; omega)
      have h1 : 1 ≤ b.l := by omega
      have hpS : Sends d (b.l - 1) t := ⟨⟨htf.le, by omega, by
        have := alpha_lt_omega d t hd; have := omega_parity t
        rcases Nat.lt_or_ge t 2 with h1 | h2
        · have : t = 1 := by omega
          subst this; rw [alpha_one] at *; rw [omega_one]; omega
        · have := alpha_lt_omega d t hd h2 htf; omega, by omega⟩, htf⟩
      have hpT : topD d (b.l - 1) t := ⟨by omega, by omega⟩
      rw [downIn_topD _ t b h1 hpS hpT,
        Int.toNat_of_nonneg (G_nonneg_wrong hd t ht1 htf hJ b (by omega) (by omega)), hup]
      simp
    · have hG : Gof (aT d t) b = 0 := hJ2 b (by omega)
      have hup : upOf (aT d t) t b = 0 :=
        upOf_of_not_sends _ t b (fun h => by obtain ⟨⟨_, hα, _, _⟩, _⟩ := h; omega)
      have hdn : downIn (aT d t) t b = 0 := by
        by_cases h1 : 1 ≤ b.l
        · exact downIn_not_sends _ t b h1 (fun h => by obtain ⟨⟨_, hα, _, _⟩, _⟩ := h; omega)
        · exact downIn_root _ t b (by omega)
      rw [hG, hup, hdn]; simp

theorem J3_next : ∀ b : KBag 16 d, omega (t + 1) < b.l →
    Gof (aT d (t + 1)) b = (16 : ℤ) ^ (d - b.l) := by
  intro b hb
  have hpo := omega_parity t
  have hpo1 := omega_parity (t + 1)
  have hωs := omega_step_exact t
  have hle := omega_le d t hd htf.le
  have hαω1 : t = 1 → omega (t + 1) = 2 := fun h => by subst h; exact omega_two
  rw [G_next hd t ht1 htf hJ b]
  rcases Nat.lt_or_ge (omega t) b.l with hbelow | habove
  · have hG := hJ.2.2.1 b hbelow
    have hup : upOf (aT d t) t b = 0 :=
      upOf_of_not_sends _ t b (fun h => by obtain ⟨⟨_, _, hω, _⟩, _⟩ := h; omega)
    have hdn : downIn (aT d t) t b = 0 := by
      have h1 : 1 ≤ b.l := by omega
      by_cases hS : Sends d (b.l - 1) t
      · obtain ⟨⟨_, hα, hω, hpar⟩, _⟩ := hS
        have h2 : 2 ≤ t := by
          by_contra h
          have h1' : t = 1 := by omega
          subst h1'
          have := omega_one; have := omega_two; omega
        have := alpha_lt_omega d t hd h2 htf
        exact downIn_botR _ t b h1 ⟨⟨by omega, hα, hω, hpar⟩, htf⟩ ⟨by omega, by omega, by omega⟩
      · exact downIn_not_sends _ t b h1 hS
    rw [hG, hup, hdn]; simp
  · -- `b` is the rising bottom at `t`
    have hbw : b.l = omega t := by omega
    have h2 : 2 ≤ t := by
      by_contra h
      have h1' : t = 1 := by omega
      subst h1'
      have := omega_one; have := omega_two; omega
    have hαω := alpha_lt_omega d t hd h2 htf
    have hS : Sends d b.l t := ⟨⟨htf.le, by omega, by omega, by omega⟩, htf⟩
    have hB : botR d b.l t := ⟨hbw, by omega, by omega⟩
    have hbl : b.l < d := by omega
    rw [upOf_botR _ t b hS hB]
    have hdn : downIn (aT d t) t b = 0 := by
      have h1 : 1 ≤ b.l := by omega
      exact downIn_not_sends _ t b h1 (fun h => by obtain ⟨⟨_, _, _, hp⟩, _⟩ := h; omega)
    rw [hdn]
    have ha := a_eq_deficits (aT d t) b hbl
    have hch : ∀ j : Fin 16, Gof (aT d t) (b.child j.val j.isLt hbl) = (16 : ℤ) ^ (d - (b.l + 1)) :=
      fun j => hJ.2.2.1 _ (by show omega t < b.l + 1; omega)
    rw [Finset.sum_congr rfl (fun j _ => hch j), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] at ha
    rw [ha]
    have : (16 : ℤ) ^ (d - b.l) = 16 * 16 ^ (d - (b.l + 1)) := by
      rw [show d - b.l = (d - (b.l + 1)) + 1 by omega, pow_succ]; ring
    push_cast; rw [this]; ring

theorem J4_next : ∀ b : KBag 16 d, Active d b.l (t + 1) → alpha d (t + 1) < b.l →
    0 ≤ Gof (aT d (t + 1)) b ∧ Gof (aT d (t + 1)) b ≤ (2 : ℤ) ^ (eN d b.l (t + 1) - 15) := by
  intro b ⟨_, hα1, hω1, hpar1⟩ hlt
  have hpa := alpha_parity d t
  have hpa1 := alpha_parity d (t + 1)
  have hpo := omega_parity t
  have hpo1 := omega_parity (t + 1)
  have hαs := alpha_step_exact d hd t
  have hωs := omega_step_exact t
  rw [G_next hd t ht1 htf hJ b]
  have hup : upOf (aT d t) t b = 0 :=
    upOf_of_not_sends _ t b (fun h => by obtain ⟨⟨_, _, _, hp⟩, _⟩ := h; omega)
  have h1 : 1 ≤ b.l := by omega
  have hpS : Sends d (b.l - 1) t := ⟨⟨htf.le, by omega, by omega, by omega⟩, htf⟩
  have hpT : ¬ topD d (b.l - 1) t := fun h => by have := h.1; have := h.2; omega
  have hpB : ¬ botR d (b.l - 1) t := fun h => by have := h.1; have := h.2.2; omega
  obtain ⟨θ, hθ0, hθ1, hdn⟩ := downIn_mid hd t ht1 htf hJ b h1 hpS hpT hpB
  rw [hup, Nat.cast_zero, add_zero, hdn]
  have he : eN d b.l (t + 1) - 15 = eN d (b.l - 1) t - 13 := by unfold eN; omega
  rw [he]
  constructor <;> linarith

theorem J5_next : ∀ b : KBag 16 d, b.l % 2 ≠ (t + 1) % 2 → alpha d (t + 1) < b.l →
    b.l < omega (t + 1) →
    (piC d b.l (t + 1 - 1) : ℤ) ≤ Gof (aT d (t + 1)) b ∧
      Gof (aT d (t + 1)) b ≤ piC d b.l (t + 1 - 1) + (2 : ℤ) ^ (eN d b.l (t + 1 - 1) - 15) := by
  intro b hpar hα1 hω1
  simp only [Nat.add_sub_cancel]
  have hpa := alpha_parity d t
  have hpa1 := alpha_parity d (t + 1)
  have hpo := omega_parity t
  have hpo1 := omega_parity (t + 1)
  have hαs := alpha_step_exact d hd t
  have hωs := omega_step_exact t
  rw [G_next hd t ht1 htf hJ b]
  have hS : Sends d b.l t := ⟨⟨htf.le, by omega, by omega, by omega⟩, htf⟩
  have hB : ¬ botR d b.l t := fun h => by have := h.1; have := h.2.2; omega
  rw [upOf_of_sends _ t b hS hB]
  have hdn : downIn (aT d t) t b = 0 := by
    by_cases h1 : 1 ≤ b.l
    · exact downIn_not_sends _ t b h1 (fun h => by obtain ⟨⟨_, _, _, hp⟩, _⟩ := h; omega)
    · exact downIn_root _ t b (by omega)
  rw [hdn, Nat.cast_zero, sub_zero]
  rcases Nat.eq_or_lt_of_le hS.1.2.1 with htop | hnt
  · have hG := hJ.2.1 b (le_of_eq htop.symm)
    rw [hG]; constructor <;> simp <;> positivity
  · obtain ⟨hG0, hG1⟩ := hJ.2.2.2.1 b hS.1 hnt
    constructor <;> linarith

/-- **The step `J(t) → J(t+1)`.** -/
theorem J_next : JInv d (t + 1) :=
  ⟨J1_next hd t ht1 htf hJ, J2_next hd t ht1 htf hJ, J3_next hd t ht1 htf hJ,
    J4_next hd t ht1 htf hJ, J5_next hd t ht1 htf hJ⟩

end Step

end R1T
