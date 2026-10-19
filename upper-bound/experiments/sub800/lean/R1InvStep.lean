import R1Inv

/-! # Invariants of design P (W1, step 17): the invariant `J(t)` and conservation

`JInv d t` (for `1 ≤ t ≤ t_f`):
* J1 inactive nodes hold no wires;
* J2 at or above the top level, `G = 0`;
* J3 below the bottom level, `G = R` (empty subtree);
* J4 active nodes below the top: `0 ≤ G ≤ g* c = 2^(e−15)`;
* J5 wrong-parity nodes strictly inside: `π(t−1) ≤ G ≤ π(t−1) + 2^(e(t−1)−15)`.

`conserves_of_J`: under `J(t)` every node conserves its wires at stage `t < t_f`. -/

namespace R1T

open Finset
open Chvatal (KBag subtreeBags)

variable {d : ℕ}

/-- The invariant at stage `t`. -/
def JInv (d t : ℕ) : Prop :=
  (∀ b : KBag 16 d, ¬ Active d b.l t → aT d t b = 0) ∧
  (∀ b : KBag 16 d, b.l ≤ alpha d t → Gof (aT d t) b = 0) ∧
  (∀ b : KBag 16 d, omega t < b.l → Gof (aT d t) b = (16 : ℤ) ^ (d - b.l)) ∧
  (∀ b : KBag 16 d, Active d b.l t → alpha d t < b.l →
      0 ≤ Gof (aT d t) b ∧ Gof (aT d t) b ≤ (2 : ℤ) ^ (eN d b.l t - 15)) ∧
  (∀ b : KBag 16 d, b.l % 2 ≠ t % 2 → alpha d t < b.l → b.l < omega t →
      (piC d b.l (t - 1) : ℤ) ≤ Gof (aT d t) b ∧
        Gof (aT d t) b ≤ piC d b.l (t - 1) + (2 : ℤ) ^ (eN d b.l (t - 1) - 15))

/-! ### Small facts -/

theorem thetaOf_eq (A : KBag 16 d → ℕ) (t : ℕ) (q : KBag 16 d) (hq : q.l < d) (j : Fin 16)
    (h1 : ¬ topD d q.l t) (h2 : ¬ botR d q.l t) :
    thetaOf A t q hq j = thetaP (upOf A t q) (Gof A q) (sOf A t q) j.val := by
  unfold thetaOf thetaP; rw [if_neg h1, if_neg h2]

theorem parent_child_self (b : KBag 16 d) (hb : 1 ≤ b.l) (hp : b.parent.l < d) :
    b.parent.child (b.x % 16) (Nat.mod_lt _ (by norm_num)) hp = b :=
  (KBag.eq_parent_child b hb hp).symm

/-- `downIn` in terms of the parent's `θ`. -/
theorem downIn_eq (A : KBag 16 d → ℕ) (t : ℕ) (b : KBag 16 d) (hb : 1 ≤ b.l) :
    downIn A t b = if h : Sends d (b.l - 1) t then
      (Gof A b - thetaOf A t b.parent (by show b.l - 1 < d; have := b.hl; omega)
        ⟨b.x % 16, Nat.mod_lt _ (by norm_num)⟩).toNat else 0 := by
  have hp : b.parent.l < d := by show b.l - 1 < d; have := b.hl; omega
  unfold downIn downOf
  rw [if_pos hb]
  by_cases hS : Sends d (b.l - 1) t
  · rw [dif_pos ⟨hS, hp⟩, dif_pos hS]
    congr 2
    exact congrArg (Gof A) (parent_child_self b hb hp)
  · rw [dif_neg (fun h => hS h.1), dif_neg hS]

theorem piC_ge (d i t : ℕ) (h : ¬ topD d i t) : 2 ^ (eN d i t - 18) ≤ piC d i t := by
  unfold piC
  rw [if_neg h]
  split_ifs
  · exact Nat.pow_le_pow_right (by norm_num) (by omega)
  · omega

theorem piC_topD (d i t : ℕ) (h : topD d i t) : piC d i t = 0 := by unfold piC; rw [if_pos h]

/-- Exponent of a child one stage earlier. -/
theorem eN_child_prev (d i t : ℕ) (h : 3 * t + 6 ≤ 4 * d + 5 * i) (ht : 1 ≤ t) :
    eN d (i + 1) (t - 1) = eN d i t + 8 := by unfold eN; omega

/-- Exponent of a child one stage later. -/
theorem eN_child_next (d i t : ℕ) (h : 3 * t + 6 ≤ 4 * d + 5 * i) :
    eN d (i + 1) (t + 1) = eN d i t + 2 := by unfold eN; omega

/-- Active levels are above the leaves. -/
theorem active_lt (hd : 10 ≤ d) (i t : ℕ) (h : Active d i t) : i + 3 ≤ d := by
  have := omega_le d t hd h.1
  have := h.2.2.1
  omega

/-! ### Conservation -/

section Cons

variable (hd : 10 ≤ d) (t : ℕ) (ht1 : 1 ≤ t) (htf : t < tf d) (hJ : JInv d t)
include hd ht1 htf hJ

/-- Children of an active node have nonnegative deficits. -/
theorem child_G_nonneg (b : KBag 16 d) (hA : Active d b.l t) (hb : b.l < d) (j : Fin 16) :
    0 ≤ Gof (aT d t) (b.child j.val j.isLt hb) := by
  obtain ⟨-, -, hJ3, -, hJ5⟩ := hJ
  have hcl : (b.child j.val j.isLt hb).l = b.l + 1 := rfl
  obtain ⟨_, hα, hω, hpar⟩ := hA
  by_cases hlt : b.l + 1 < omega t
  · have := hJ5 (b.child j.val j.isLt hb) (by rw [hcl]; omega) (by rw [hcl]; omega) (by rw [hcl]; exact hlt)
    exact le_trans (by positivity) this.1
  · have hpo := omega_parity t
    have := hJ3 (b.child j.val j.isLt hb) (by rw [hcl]; omega)
    rw [this]; positivity

/-- Inactive nodes conserve (they hold, send and receive nothing at `t`). -/
theorem conserves_inactive (b : KBag 16 d) (hS : ¬ Sends d b.l t) : Conserves (aT d t) t b := by
  unfold Conserves upOf downOf
  rw [if_neg hS]
  simp only [dif_neg (fun h : Sends d b.l t ∧ b.l < d => hS h.1), Finset.sum_const_zero, add_zero]
  exact hJ.1 b (fun hA => hS ⟨hA, htf⟩)

/-- A descending top conserves: `π = 0`, `θ = 0`, `G = 0`. -/
theorem conserves_topD (b : KBag 16 d) (hS : Sends d b.l t) (hT : topD d b.l t) :
    Conserves (aT d t) t b := by
  have hbl : b.l < d := by have := active_lt hd b.l t hS.1; omega
  unfold Conserves upOf downOf
  rw [if_pos hS, if_neg (fun h : botR d b.l t => h.2.1 hT.1), piC_topD d b.l t hT, zero_add]
  have hθ : ∀ j : Fin 16, thetaOf (aT d t) t b hbl j = 0 := fun j => by
    unfold thetaOf; rw [if_pos hT]
  have hG0 : Gof (aT d t) b = 0 := hJ.2.1 b (le_of_eq hT.1)
  have ha := a_eq_deficits (aT d t) b hbl
  rw [hG0, sub_zero] at ha
  have hsum : ((∑ j : Fin 16, (if h : Sends d b.l t ∧ b.l < d then
      (Gof (aT d t) (b.child j.val j.isLt h.2) - thetaOf (aT d t) t b h.2 j).toNat else 0) : ℕ) : ℤ) =
      ∑ j : Fin 16, Gof (aT d t) (b.child j.val j.isLt hbl) := by
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [dif_pos ⟨hS, hbl⟩, hθ j, sub_zero, Int.toNat_of_nonneg (child_G_nonneg hd t ht1 htf hJ b hS.1 hbl j)]
  have : (aT d t b : ℤ) = ((∑ j : Fin 16, (if h : Sends d b.l t ∧ b.l < d then
      (Gof (aT d t) (b.child j.val j.isLt h.2) - thetaOf (aT d t) t b h.2 j).toNat else 0) : ℕ) : ℤ) := by
    rw [hsum, ha]
  exact_mod_cast this

/-- A rising bottom conserves: it sends everything up. -/
theorem conserves_botR (b : KBag 16 d) (hS : Sends d b.l t) (hB : botR d b.l t) :
    Conserves (aT d t) t b := by
  have hbl : b.l < d := by have := active_lt hd b.l t hS.1; omega
  unfold Conserves upOf downOf
  rw [if_pos hS, if_pos hB]
  have hT : ¬ topD d b.l t := fun h => hB.2.1 h.1
  have : ∀ j : Fin 16, (if h : Sends d b.l t ∧ b.l < d then
      (Gof (aT d t) (b.child j.val j.isLt h.2) - thetaOf (aT d t) t b h.2 j).toNat else 0) = 0 := by
    intro j
    rw [dif_pos ⟨hS, hbl⟩]
    unfold thetaOf; rw [if_neg hT, if_pos hB, sub_self]; rfl
  simp [this]

end Cons

/-! ### Senders other than the extreme roles -/

section Senders

variable (hd : 10 ≤ d) (t : ℕ) (ht1 : 1 ≤ t) (htf : t < tf d) (hJ : JInv d t)
include hd ht1 htf hJ

theorem two_pow_split (e k m : ℕ) (h : m ≤ e) (hk : e - k = (e - m) + (m - k)) (hkm : k ≤ m) :
    (2 : ℤ) ^ (e - k) = 2 ^ (m - k) * 2 ^ (e - m) := by
  rw [hk, pow_add]; ring

/-- `θ` bounds of a sender that is neither a descending top nor a rising bottom. -/
theorem sender_theta_bounds (b : KBag 16 d) (hS : Sends d b.l t) (hT : ¬ topD d b.l t)
    (hB : ¬ botR d b.l t) (hbl : b.l < d) (j : Fin 16) :
    0 ≤ thetaOf (aT d t) t b hbl j ∧ thetaOf (aT d t) t b hbl j ≤ (2 : ℤ) ^ (eN d b.l t - 13) := by
  obtain ⟨hJ1, hJ2, hJ3, hJ4, hJ5⟩ := hJ
  rw [thetaOf_eq _ _ _ _ _ hT hB]
  have hup : (upOf (aT d t) t b : ℤ) = piC d b.l t := by
    unfold upOf; rw [if_pos hS, if_neg hB]
  rw [hup]
  rcases Nat.eq_or_lt_of_le hS.1.2.1 with htop | hnt
  · -- rising top: `G = 0`, `s = 0`, `π = 2^(e−12)`
    have hG : Gof (aT d t) b = 0 := hJ2 b (le_of_eq htop.symm)
    have hs : sOf (aT d t) t b = 0 := by unfold sOf; rw [if_pos hG]
    have he : 13 ≤ eN d b.l t := by
      rcases Nat.lt_or_ge t 2 with h1 | h2
      · obtain rfl : t = 1 := by omega
        have : b.l = 1 := by rw [← htop]; simp [alpha]
        unfold eN; rw [this]; omega
      · have hrise : alpha d (t + 1) < alpha d t := by
          have := alpha_step_exact d hd t; unfold topD at hT; omega
        have := exp_top_rise d t hd h2 hrise
        unfold eN; rw [← htop]; omega
    have hpi : (piC d b.l t : ℤ) = 2 * 2 ^ (eN d b.l t - 13) := by
      unfold piC; rw [if_neg hT, if_pos htop.symm]
      push_cast
      rw [show eN d b.l t - 12 = (eN d b.l t - 13) + 1 by omega, pow_succ]; ring
    rw [hG, hs, hpi]
    have hdiv : (2 * (2 : ℤ) ^ (eN d b.l t - 13)) / 2 = 2 ^ (eN d b.l t - 13) :=
      Int.mul_ediv_cancel_left _ (by norm_num)
    unfold thetaP
    split_ifs with hj hr
    · rw [hdiv]; simp only [add_zero, sub_zero]
      exact ⟨by positivity, le_rfl⟩
    · exfalso
      have hj1 : 1 ≤ j.val := by omega
      simp at hr
      omega
    · simp only [mul_zero, sub_zero, Int.zero_ediv, Int.zero_emod, zero_add]
      exact ⟨le_rfl, by positivity⟩
  · -- non-top: `e ≥ 19`, work in units `X = 2^(e−19)`
    have ht2 : 2 ≤ t := by
      by_contra h
      have : t = 1 := by omega
      subst this
      have h1 : alpha d 1 = 1 := by simp [alpha]
      have h2 : omega 1 = 1 := by simp [omega]
      have := hS.1.2.2.1
      omega
    have he : 19 ≤ eN d b.l t := by
      have := exp_nontop d t b.l ht2 (by have := hS.1.2.2.2; have := alpha_parity d t; omega)
      unfold eN; omega
    set X : ℤ := 2 ^ (eN d b.l t - 19) with hX
    have hX1 : 1 ≤ X := one_le_pow₀ (by norm_num)
    have h13 : (2 : ℤ) ^ (eN d b.l t - 13) = 64 * X := by
      rw [show eN d b.l t - 13 = (eN d b.l t - 19) + 6 by omega, pow_add, hX]; ring
    have h15 : (2 : ℤ) ^ (eN d b.l t - 15) = 16 * X := by
      rw [show eN d b.l t - 15 = (eN d b.l t - 19) + 4 by omega, pow_add, hX]; ring
    have hpi : (piC d b.l t : ℤ) = 2 * (63 * X) := by
      unfold piC; rw [if_neg hT, if_neg (by omega)]
      push_cast
      rw [show eN d b.l t - 18 = (eN d b.l t - 19) + 1 by omega, pow_succ, hX]; ring
    have hsres : (sres d b.l t : ℤ) = 15 * X := by unfold sres; push_cast; rfl
    obtain ⟨hG0, hG1⟩ := hJ4 b hS.1 hnt
    rw [h15] at hG1
    rw [h13, hpi]
    have hdiv : (2 * (63 * X)) / 2 = 63 * X := Int.mul_ediv_cancel_left _ (by norm_num)
    by_cases hGz : Gof (aT d t) b = 0
    · have hs : sOf (aT d t) t b = 0 := by unfold sOf; rw [if_pos hGz]
      rw [hGz, hs]
      unfold thetaP
      simp only [hdiv]
      split_ifs <;> norm_num <;> first | (constructor <;> linarith) | linarith
    · have hs : sOf (aT d t) t b = 15 * X := by unfold sOf; rw [if_neg hGz, hsres]
      rw [hs]
      unfold thetaP
      simp only [hdiv]
      split_ifs with hj hr
      · constructor <;> linarith
      · have hI0 : 14 * X ≤ 2 * (15 * X) - Gof (aT d t) b := by linarith
        have hq0 : X ≤ (2 * (15 * X) - Gof (aT d t) b) / 14 := by
          rw [Int.le_ediv_iff_mul_le (by norm_num)]; linarith
        have hq1 : (2 * (15 * X) - Gof (aT d t) b) / 14 ≤ 3 * X := by
          rw [Int.ediv_le_iff_le_mul (by norm_num)]; linarith
        constructor <;> linarith
      · have hI0 : 14 * X ≤ 2 * (15 * X) - Gof (aT d t) b := by linarith
        have hq0 : X ≤ (2 * (15 * X) - Gof (aT d t) b) / 14 := by
          rw [Int.le_ediv_iff_mul_le (by norm_num)]; linarith
        have hq1 : (2 * (15 * X) - Gof (aT d t) b) / 14 ≤ 3 * X := by
          rw [Int.ediv_le_iff_le_mul (by norm_num)]; linarith
        constructor <;> linarith

/-- Children of such a sender have deficit at least `2^(e−13)` (I2). -/
theorem sender_child_lb (b : KBag 16 d) (hS : Sends d b.l t) (hT : ¬ topD d b.l t)
    (hB : ¬ botR d b.l t) (hbl : b.l < d) (j : Fin 16) :
    (2 : ℤ) ^ (eN d b.l t - 13) ≤ Gof (aT d t) (b.child j.val j.isLt hbl) := by
  obtain ⟨hJ1, hJ2, hJ3, hJ4, hJ5⟩ := hJ
  have hcl : (b.child j.val j.isLt hbl).l = b.l + 1 := rfl
  obtain ⟨⟨_, hα, hω, hpar⟩, _⟩ := hS
  have hpo := omega_parity t
  have hpa := alpha_parity d t
  have hact : 3 * t + 6 ≤ 4 * d + 5 * b.l := by
    rcases Nat.lt_or_ge t 2 with h1 | h2
    · obtain rfl : t = 1 := by omega
      omega
    · have := exp_top d t h2; omega
  rcases Nat.lt_or_ge (b.l + 1) (omega t) with hin | hout
  · -- strictly inside: J5
    have ht2 : 2 ≤ t := by
      by_contra h
      have : t = 1 := by omega
      subst this
      have : omega 1 = 1 := by simp [omega]
      omega
    have h5 := (hJ5 (b.child j.val j.isLt hbl) (by rw [hcl]; omega) (by rw [hcl]; omega)
      (by rw [hcl]; exact hin)).1
    rw [hcl] at h5
    have hnT : ¬ topD d (b.l + 1) (t - 1) := by
      rintro ⟨h1, h2⟩
      have : t - 1 + 1 = t := by omega
      rw [this] at h2
      omega
    have hp := piC_ge d (b.l + 1) (t - 1) hnT
    rw [eN_child_prev d b.l t hact ht1] at hp
    refine le_trans ?_ h5
    have : (2 : ℤ) ^ (eN d b.l t - 13) ≤ 2 ^ (eN d b.l t + 8 - 18) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    exact this.trans (by exact_mod_cast hp)
  · -- below the bottom (descending bottom, or `t = 1`): J3
    have hlt : omega t < b.l + 1 := by omega
    have h3 := hJ3 (b.child j.val j.isLt hbl) (by rw [hcl]; exact hlt)
    rw [h3, hcl]
    have hroom : eN d b.l t - 13 ≤ 4 * (d - (b.l + 1)) := by
      rcases Nat.lt_or_ge t 2 with h1 | h2
      · obtain rfl : t = 1 := by omega
        have : b.l = 1 := by
          have : alpha d 1 = 1 := by simp [alpha]
          have : omega 1 = 1 := by simp [omega]
          omega
        unfold eN; rw [this]; omega
      · have hbw : b.l = omega t := by omega
        have hdesc : omega t < omega (t + 1) := by
          by_contra h
          exact hB ⟨hbw, by
            intro h'
            have := alpha_lt_omega d t hd h2 htf
            omega, h⟩
        have := botD_room t h2 hdesc
        have := omega_le d t hd htf.le
        unfold eN; omega
    calc (2 : ℤ) ^ (eN d b.l t - 13) ≤ 2 ^ (4 * (d - (b.l + 1))) :=
          pow_le_pow_right₀ (by norm_num) hroom
      _ = 16 ^ (d - (b.l + 1)) := by rw [pow_mul]; norm_num

/-- **Conservation of such a sender.** -/
theorem conserves_mid (b : KBag 16 d) (hS : Sends d b.l t) (hT : ¬ topD d b.l t)
    (hB : ¬ botR d b.l t) : Conserves (aT d t) t b := by
  have hbl : b.l < d := by have := active_lt hd b.l t hS.1; omega
  have hπe : 2 ∣ (upOf (aT d t) t b : ℤ) := by
    have hb := sender_theta_bounds hd t ht1 htf hJ b hS hT hB hbl ⟨0, by norm_num⟩
    rw [thetaOf_eq _ _ _ _ _ hT hB] at hb
    -- evenness of `π`
    unfold upOf; rw [if_pos hS, if_neg hB]
    unfold piC; rw [if_neg hT]
    split_ifs with htop
    · have he : 13 ≤ eN d b.l t := by
        rcases Nat.lt_or_ge t 2 with h1 | h2
        · obtain rfl : t = 1 := by omega
          have : b.l = 1 := by rw [htop]; simp [alpha]
          unfold eN; rw [this]; omega
        · have hrise : alpha d (t + 1) < alpha d t := by
            have := alpha_step_exact d hd t; unfold topD at hT; omega
          have := exp_top_rise d t hd h2 hrise
          unfold eN; rw [htop]; omega
      push_cast
      exact Dvd.intro (2 ^ (eN d b.l t - 13)) (by rw [← pow_succ']; congr 1; omega)
    · have he : 19 ≤ eN d b.l t := by
        have ht2 : 2 ≤ t := by
          by_contra h
          have : t = 1 := by omega
          subst this
          have h1 : alpha d 1 = 1 := by simp [alpha]
          have h2 : omega 1 = 1 := by simp [omega]
          have := hS.1.2.2.1
          have := hS.1.2.1
          omega
        have := exp_nontop d t b.l ht2 (by
          have := hS.1.2.2.2; have := alpha_parity d t; have := hS.1.2.1; omega)
        unfold eN; omega
      push_cast
      exact Dvd.intro (63 * 2 ^ (eN d b.l t - 19)) (by
        rw [show eN d b.l t - 18 = (eN d b.l t - 19) + 1 by omega, pow_succ]; ring)
  have hsum := sum_thetaP (upOf (aT d t) t b) (Gof (aT d t) b) (sOf (aT d t) t b) hπe
  have ha := a_eq_deficits (aT d t) b hbl
  unfold Conserves downOf
  have hdown : ∀ j : Fin 16, ((if h : Sends d b.l t ∧ b.l < d then
      (Gof (aT d t) (b.child j.val j.isLt h.2) - thetaOf (aT d t) t b h.2 j).toNat else 0 : ℕ) : ℤ) =
      Gof (aT d t) (b.child j.val j.isLt hbl) - thetaP (upOf (aT d t) t b) (Gof (aT d t) b)
        (sOf (aT d t) t b) j.val := by
    intro j
    rw [dif_pos ⟨hS, hbl⟩]
    have hb := sender_theta_bounds hd t ht1 htf hJ b hS hT hB hbl j
    have hc := sender_child_lb hd t ht1 htf hJ b hS hT hB hbl j
    rw [Int.toNat_of_nonneg (by linarith), thetaOf_eq _ _ _ _ _ hT hB]
  have : (aT d t b : ℤ) = (upOf (aT d t) t b : ℤ) +
      ((∑ j : Fin 16, (if h : Sends d b.l t ∧ b.l < d then
        (Gof (aT d t) (b.child j.val j.isLt h.2) - thetaOf (aT d t) t b h.2 j).toNat else 0) : ℕ) : ℤ) := by
    push_cast
    rw [Finset.sum_congr rfl (fun j _ => hdown j), Finset.sum_sub_distrib]
    have hfin : ∑ j : Fin 16, thetaP (upOf (aT d t) t b) (Gof (aT d t) b) (sOf (aT d t) t b) j.val =
        ∑ j ∈ range 16, thetaP (upOf (aT d t) t b) (Gof (aT d t) b) (sOf (aT d t) t b) j :=
      Fin.sum_univ_eq_sum_range (fun j => thetaP _ _ _ j) 16
    rw [hfin, hsum, ha]
    ring
  exact_mod_cast this

/-- **Conservation at stage `t`.** -/
theorem conserves_of_J : ∀ b, Conserves (aT d t) t b := by
  intro b
  by_cases hS : Sends d b.l t
  · by_cases hT : topD d b.l t
    · exact conserves_topD hd t ht1 htf hJ b hS hT
    · by_cases hB : botR d b.l t
      · exact conserves_botR hd t ht1 htf hJ b hS hB
      · exact conserves_mid hd t ht1 htf hJ b hS hT hB
  · exact conserves_inactive hd t ht1 htf hJ b hS

end Senders

end R1T
