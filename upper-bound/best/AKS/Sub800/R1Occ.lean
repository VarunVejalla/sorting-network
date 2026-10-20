import AKS.Sub800.R1Design

/-! # Occupancy of the design-P senders (W2, step 2; R1-PROOF §2 (I3))

Write `e = eN d i t`, so `c = 2^e`, and `u = 2^(e−12) = c/4096`.

* `a_step`: `a(t+1) = Σ up(children, t) + G(t) − G(t+1)` for a node that does not send at `t`.
* `a_bottom`: `a = 16^(d−i) − G` at or below the bottom.
* `occ_crude`: a non-bottom sender at `t ≥ 2` has `a ≤ 2^(e+19)`.
* `occ_inner`: if moreover `e ≥ 19`, then `4094 u ≤ a ≤ 4104 u`.
* `occ_t1`: at `t = 1` the sender has `a = 2^e`.
* `occ_botD`: a descending bottom has `a = R − G`, `0 ≤ G ≤ 2^(e−15)`, `R ∈ {2^e, 2^(e−6)}`. -/

namespace R1T

open Finset
open Chvatal (KBag)

variable {d : ℕ}

/-- `a(t+1) = Σ up(children) + G(t) − G(t+1)` for a node that does not send at `t`. -/
theorem a_step (hd : 10 ≤ d) (s : ℕ) (hs : s < tf d) (x : KBag 16 d) (hx : x.l < d)
    (hns : ¬ Sends d x.l s) :
    (aT d (s + 1) x : ℤ) = ∑ j : Fin 16, (upOf (aT d s) s (x.child j.val j.isLt hx) : ℤ) +
      Gof (aT d s) x - Gof (aT d (s + 1)) x := by
  have hG : Gof (aT d (s + 1)) x = Gof (aT d s) x + upOf (aT d s) s x - downIn (aT d s) s x :=
    Gof_next (aT d s) s (conserves_all hd s hs) x
  rw [upOf_of_not_sends _ s x hns, Nat.cast_zero, add_zero] at hG
  have ha : aT d (s + 1) x = downIn (aT d s) s x +
      ∑ j : Fin 16, upOf (aT d s) s (x.child j.val j.isLt hx) := by
    show nextA (aT d s) s x = _
    unfold nextA; rw [dif_pos hx]; rfl
  rw [ha]; push_cast; linarith

/-- At or below the bottom, a node holds its whole subtree: `a = 16^(d−i) − G`. -/
theorem a_bottom (t : ℕ) (hJ : JInv d t) (x : KBag 16 d) (hx : x.l < d) (hω : omega t ≤ x.l) :
    (aT d t x : ℤ) = (16 : ℤ) ^ (d - x.l) - Gof (aT d t) x := by
  rw [a_eq_deficits (aT d t) x hx]
  have hc : ∀ j : Fin 16, Gof (aT d t) (x.child j.val j.isLt hx) = (16 : ℤ) ^ (d - (x.l + 1)) := by
    intro j
    have := hJ.2.2.1 (x.child j.val j.isLt hx) (by show omega t < x.l + 1; omega)
    exact this
  rw [Finset.sum_congr rfl (fun j _ => hc j), Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  rw [show d - x.l = (d - (x.l + 1)) + 1 by omega, pow_succ]; push_cast; ring

/-! ### Values of `π` -/

theorem piC_rise (i t : ℕ) (hi : i = alpha d t) (hT : ¬ topD d i t) :
    piC d i t = 2 ^ (eN d i t - 12) := by
  unfold piC; rw [if_neg hT, if_pos hi]

theorem piC_mid (i t : ℕ) (hi : i ≠ alpha d t) : piC d i t = 63 * 2 ^ (eN d i t - 18) := by
  unfold piC; rw [if_neg (fun h => hi h.1), if_neg hi]

theorem piC_le64 (i t : ℕ) : piC d i t ≤ 64 * 2 ^ (eN d i t) := by
  have h1 := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show eN d i t - 12 ≤ eN d i t by omega)
  have h2 := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show eN d i t - 18 ≤ eN d i t by omega)
  unfold piC; split_ifs <;> omega

theorem piC_bounds (i t : ℕ) (hT : ¬ topD d i t) (he : 18 ≤ eN d i t) :
    63 * 2 ^ (eN d i t - 18) ≤ piC d i t ∧ piC d i t ≤ 64 * 2 ^ (eN d i t - 18) := by
  have h6 : 2 ^ (eN d i t - 12) = 64 * 2 ^ (eN d i t - 18) := by
    rw [show eN d i t - 12 = (eN d i t - 18) + 6 by omega, pow_add]; ring
  unfold piC; rw [if_neg hT]; split_ifs <;> omega

/-! ### Non-bottom senders at `t ≥ 2` -/

section Inner

variable (hd : 10 ≤ d) (s : ℕ) (hs1 : 1 ≤ s) (htf : s + 1 < tf d) (x : KBag 16 d)
  (hS : Sends d x.l (s + 1)) (hω : x.l < omega (s + 1))
include hd hs1 htf hS hω

/-- The schedule facts used below. -/
theorem inner_sched :
    x.l < d ∧ x.l + 2 ≤ omega (s + 1) ∧ alpha d (s + 1) ≤ x.l ∧ alpha d s ≤ x.l + 1 ∧
      x.l + 1 ≤ omega s ∧ x.l % 2 ≠ s % 2 ∧ (x.l + 1) % 2 = s % 2 ∧
      3 * (s + 1) + 15 ≤ 4 * d + 5 * x.l ∧ ¬ Sends d x.l s ∧
      Sends d (x.l + 1) s ∧ ¬ botR d (x.l + 1) s := by
  obtain ⟨⟨_, hα, _, hpar⟩, _⟩ := hS
  have hωl := omega_le d (s + 1) hd htf.le
  have hαs := alpha_step_exact d hd s
  have hωs := omega_step_exact s
  have hαp := alpha_parity d s
  have hωp := omega_parity (s + 1)
  have hωp' := omega_parity s
  have hexp := exp_top d (s + 1) (by omega)
  refine ⟨by omega, by omega, hα, by omega, by omega, by omega, by omega, by omega, ?_, ?_, ?_⟩
  · intro h; have := h.1.2.2.2; omega
  · exact ⟨⟨by omega, by omega, by omega, by omega⟩, by omega⟩
  · rintro ⟨h1, _, h3⟩; omega

/-- The deficit at `t = s + 1` is in `[0, 2^(e−15)]`. -/
theorem inner_Gt :
    0 ≤ Gof (aT d (s + 1)) x ∧ Gof (aT d (s + 1)) x ≤ 2 ^ (eN d x.l (s + 1) - 15) := by
  have hJt := J_all hd (s + 1) (by omega) (by omega)
  obtain ⟨hA, _⟩ := hS
  by_cases hle : x.l ≤ alpha d (s + 1)
  · rw [hJt.2.1 x hle]; exact ⟨le_rfl, by positivity⟩
  · exact hJt.2.2.2.1 x hA (by omega)

/-- The deficit at `s`: zero if `x` is at or above the top at `s`, else within `[π, π + 2^(e+6−15)]`
of its `π` at `s − 1`. -/
theorem inner_Gs (hlt : alpha d s < x.l) :
    (piC d x.l (s - 1) : ℤ) ≤ Gof (aT d s) x ∧
      Gof (aT d s) x ≤ piC d x.l (s - 1) + 2 ^ (eN d x.l (s - 1) - 15) := by
  obtain ⟨_, _, _, _, hω1, hp, _⟩ := inner_sched hd s hs1 htf x hS hω
  have hJs := J_all hd s hs1 (by omega)
  exact hJs.2.2.2.2 x hp hlt (by omega)

/-- **Crude bound**: `a ≤ 2^(e+19)`. -/
theorem occ_crude : (aT d (s + 1) x : ℤ) ≤ 2 ^ (eN d x.l (s + 1) + 19) := by
  obtain ⟨hx, _, _, _, _, _, _, hexp, hns, hcS, hcB⟩ := inner_sched hd s hs1 htf x hS hω
  set e := eN d x.l (s + 1) with he
  rw [a_step hd s (by omega) x hx hns]
  have hec : eN d (x.l + 1) s = e + 8 := by simp only [he, eN]; omega
  have hup : ∀ j : Fin 16, (upOf (aT d s) s (x.child j.val j.isLt hx) : ℤ) ≤ 64 * 2 ^ (e + 8) := by
    intro j
    rw [upOf_of_sends _ s _ hcS hcB]
    have := piC_le64 (d := d) (x.l + 1) s
    rw [hec] at this
    exact_mod_cast this
  have hsum : ∑ j : Fin 16, (upOf (aT d s) s (x.child j.val j.isLt hx) : ℤ) ≤ 16 * (64 * 2 ^ (e + 8)) := by
    calc _ ≤ ∑ _j : Fin 16, (64 * (2 : ℤ) ^ (e + 8)) := Finset.sum_le_sum fun j _ => hup j
      _ = _ := by simp
  have hGt := (inner_Gt hd s hs1 htf x hS hω).1
  have hGs : Gof (aT d s) x ≤ 65 * 2 ^ (e + 6) := by
    by_cases hlt : alpha d s < x.l
    · have h := (inner_Gs hd s hs1 htf x hS hω hlt).2
      have hep : eN d x.l (s - 1) = e + 6 := by simp only [he, eN]; omega
      rw [hep] at h
      have h1 := piC_le64 (d := d) x.l (s - 1)
      rw [hep] at h1
      have h2 : (2 : ℤ) ^ (e + 6 - 15) ≤ 2 ^ (e + 6) := pow_le_pow_right₀ (by norm_num) (by omega)
      have h1' : (piC d x.l (s - 1) : ℤ) ≤ 64 * 2 ^ (e + 6) := by exact_mod_cast h1
      linarith
    · have hJs := J_all hd s hs1 (by omega)
      rw [hJs.2.1 x (by omega)]; positivity
  have h8 : (2 : ℤ) ^ (e + 8) = 4 * 2 ^ (e + 6) := by rw [show e + 8 = (e + 6) + 2 by omega, pow_add]; ring
  have h19 : (2 : ℤ) ^ (e + 19) = 8192 * 2 ^ (e + 6) := by
    rw [show e + 19 = (e + 6) + 13 by omega, pow_add]; ring
  have hp : (0 : ℤ) ≤ 2 ^ (e + 6) := by positivity
  rw [h19]; rw [h8] at hsum; linarith

/-- **Occupancy** of a non-bottom sender: `4094 u ≤ a ≤ 4104 u`, `u = 2^(e−12)`. -/
theorem occ_inner (he19 : 19 ≤ eN d x.l (s + 1)) :
    4094 * (2 : ℤ) ^ (eN d x.l (s + 1) - 12) ≤ aT d (s + 1) x ∧
      (aT d (s + 1) x : ℤ) ≤ 4104 * 2 ^ (eN d x.l (s + 1) - 12) := by
  obtain ⟨hx, h2ω, hαt, hαs, _, _, _, hexp, hns, hcS, hcB⟩ := inner_sched hd s hs1 htf x hS hω
  set e := eN d x.l (s + 1) with he
  rw [a_step hd s (by omega) x hx hns]
  set u : ℤ := 2 ^ (e - 12) with hu
  have hec : eN d (x.l + 1) s = e + 8 := by simp only [he, eN]; omega
  have hGt := inner_Gt hd s hs1 htf x hS hω
  rw [← he] at hGt
  have h15 : 8 * (2 : ℤ) ^ (e - 15) = u := by
    rw [hu, show e - 12 = (e - 15) + 3 by omega, pow_add]; ring
  have hJs := J_all hd s hs1 (by omega)
  have hJt := J_all hd (s + 1) (by omega) (by omega)
  have hαstep := alpha_step_exact d hd s
  have hαp := alpha_parity d s
  have hαp1 := alpha_parity d (s + 1)
  have hpar := hS.1.2.2.2
  by_cases hA : alpha d s = x.l + 1
  · -- children are the rising top at `s`
    have hT : ¬ topD d (x.l + 1) s := by rintro ⟨_, h⟩; omega
    have hup : ∀ j : Fin 16, (upOf (aT d s) s (x.child j.val j.isLt hx) : ℤ) = 256 * u := by
      intro j
      rw [upOf_of_sends _ s _ hcS hcB]
      show ((piC d (x.l + 1) s : ℕ) : ℤ) = _
      rw [piC_rise (x.l + 1) s hA.symm hT, hec, hu]
      push_cast
      rw [show e - 4 = (e - 12) + 8 by omega, pow_add]; ring
    rw [Finset.sum_congr rfl (fun j _ => hup j)]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [hJs.2.1 x (by omega), hJt.2.1 x (by omega)]
    have hu0 : 0 ≤ u := by positivity
    push_cast
    constructor <;> nlinarith
  · -- children are interior at `s`
    have hlt : alpha d s < x.l := by omega
    have hup : ∀ j : Fin 16, (upOf (aT d s) s (x.child j.val j.isLt hx) : ℤ) = 252 * u := by
      intro j
      rw [upOf_of_sends _ s _ hcS hcB]
      show ((piC d (x.l + 1) s : ℕ) : ℤ) = _
      rw [piC_mid (x.l + 1) s (by omega), hec, hu]
      push_cast
      rw [show e - 10 = (e - 12) + 2 by omega, pow_add]; ring
    rw [Finset.sum_congr rfl (fun j _ => hup j)]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hGs := inner_Gs hd s hs1 htf x hS hω hlt
    have hep : eN d x.l (s - 1) = e + 6 := by simp only [he, eN]; omega
    rw [hep] at hGs
    have hT : ¬ topD d x.l (s - 1) := by
      rintro ⟨h1, h2⟩
      rw [show s - 1 + 1 = s by omega] at h2
      omega
    have hpb := piC_bounds (d := d) x.l (s - 1) hT (by omega)
    rw [hep, show e + 6 - 18 = e - 12 by omega] at hpb
    have hlo : 63 * u ≤ (piC d x.l (s - 1) : ℤ) := by rw [hu]; exact_mod_cast hpb.1
    have hhi : (piC d x.l (s - 1) : ℤ) ≤ 64 * u := by rw [hu]; exact_mod_cast hpb.2
    have h9 : (2 : ℤ) ^ (e + 6 - 15) = 8 * u := by
      rw [hu, show e + 6 - 15 = (e - 12) + 3 by omega, pow_add]; ring
    rw [h9] at hGs
    push_cast
    constructor <;> linarith [hGt.1, hGt.2, hGs.1, hGs.2]

end Inner

/-- At `t = 1` the senders are the level-1 nodes, each holding `16^(d−1) = 2^e`. -/
theorem occ_t1 (hd : 10 ≤ d) (x : KBag 16 d) (hS : Sends d x.l 1) :
    x.l = 1 ∧ (aT d 1 x : ℤ) = 2 ^ (eN d x.l 1) := by
  have hJ := J_all hd 1 le_rfl (by unfold tf; omega)
  obtain ⟨⟨_, hα, hω, _⟩, _⟩ := hS
  rw [alpha_one] at hα; rw [omega_one] at hω
  have hl : x.l = 1 := by omega
  refine ⟨hl, ?_⟩
  rw [a_bottom 1 hJ x (by rw [hl]; omega) (by rw [omega_one]; omega),
    hJ.2.1 x (by rw [alpha_one]; omega), hl]
  rw [show eN d 1 1 = 4 * (d - 1) by unfold eN; omega, pow_mul]; norm_num

/-- A descending bottom: `a = R − G` with `0 ≤ G ≤ 2^(e−15)` and `R = 2^e` or `R = 2^(e−6)`. -/
theorem occ_botD (hd : 10 ≤ d) (t : ℕ) (h2 : 2 ≤ t) (htf : t < tf d) (x : KBag 16 d)
    (hS : Sends d x.l t) (hωx : x.l = omega t) (hB : ¬ botR d x.l t) :
    19 ≤ eN d x.l t ∧ ∃ R : ℤ, (aT d t x : ℤ) = R - Gof (aT d t) x ∧
      0 ≤ Gof (aT d t) x ∧ Gof (aT d t) x ≤ 2 ^ (eN d x.l t - 15) ∧
      (R = 2 ^ (eN d x.l t) ∨ 64 * R = 2 ^ (eN d x.l t)) := by
  have hJ := J_all hd t (by omega) htf.le
  have hαω := alpha_lt_omega d t hd h2 htf
  have hαp := alpha_parity d t
  have hωp := omega_parity t
  have hωl := omega_le d t hd htf.le
  have hA := hS.1
  have hnt := exp_nontop d t x.l h2 (by omega)
  have hωs : omega t < omega (t + 1) := by
    by_contra h; exact hB ⟨hωx, by omega, h⟩
  have hr := botD_ratio t h2 hωs
  refine ⟨by unfold eN; omega, (16 : ℤ) ^ (d - x.l),
    a_bottom t hJ x (by omega) (by omega), (hJ.2.2.2.1 x hA (by omega)).1,
    (hJ.2.2.2.1 x hA (by omega)).2, ?_⟩
  have h16 : (16 : ℤ) ^ (d - x.l) = 2 ^ (4 * (d - x.l)) := by rw [pow_mul]; norm_num
  rw [h16]
  rcases hr with hr | hr
  · left; congr 1; unfold eN; omega
  · right
    rw [show eN d x.l t = 4 * (d - x.l) + 6 by unfold eN; omega, pow_add]; ring

end R1T
