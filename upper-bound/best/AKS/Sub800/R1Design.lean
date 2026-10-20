import AKS.Sub800.R1InvAll

/-! # The design-P flow table and its facts (W1, step 20)

`designP hd : FlowTableB d (tf d)` with the parity, residual and final-occupancy facts consumed by
`r1_sorter_of_facts`. -/

namespace R1T

open Finset
open Chvatal (KBag subtreeBags)

variable {d : ℕ}

/-- Evenness of the up-flow of senders other than the rising bottom. -/
theorem piC_even (hd : 10 ≤ d) (t : ℕ) (b : KBag 16 d) (hS : Sends d b.l t) :
    2 ∣ piC d b.l t := by
  by_cases hT : topD d b.l t
  · rw [piC_topD d _ t hT]; exact dvd_zero 2
  unfold piC; rw [if_neg hT]
  obtain ⟨⟨htf', hα, hω, hpar⟩, htf⟩ := hS
  have hpa := alpha_parity d t
  have ht1 : 1 ≤ t := by
    by_contra h
    have : t = 0 := by omega
    subst this
    have ha0 : alpha d 0 = 0 := by simp [alpha]
    have hw0 : omega 0 = 0 := by simp [omega]
    rw [ha0] at hα; rw [hw0] at hω
    exact hT ⟨by rw [ha0]; omega, by rw [ha0, alpha_one]; omega⟩
  split_ifs with htop
  · have he : 13 ≤ eN d b.l t := by
      rcases Nat.lt_or_ge t 2 with h1 | h2
      · obtain rfl : t = 1 := by omega
        rw [htop, alpha_one]; unfold eN; omega
      · have hrise : alpha d (t + 1) < alpha d t := by
          have := alpha_step_exact d hd t; unfold topD at hT; omega
        have := exp_top_rise d t hd h2 hrise
        unfold eN; rw [htop]; omega
    exact Dvd.intro (2 ^ (eN d b.l t - 13)) (by rw [← pow_succ']; congr 1; omega)
  · have ht2 : 2 ≤ t := by
      by_contra h
      obtain rfl : t = 1 := by omega
      rw [alpha_one] at hα htop; rw [omega_one] at hω; omega
    have he : 19 ≤ eN d b.l t := by
      have := exp_nontop d t b.l ht2 (by omega)
      unfold eN; omega
    exact Dvd.intro (63 * 2 ^ (eN d b.l t - 19)) (by
      rw [show eN d b.l t - 18 = (eN d b.l t - 19) + 1 by omega, pow_succ]; ring)

/-- **The design-P flow table.** -/
def designP (hd : 10 ≤ d) : FlowTableB d (tf d) where
  a := aT d
  up t b := upOf (aT d t) t b
  down t b j := downOf (aT d t) t b j
  ha_root := by show (if KBag.root 16 d = KBag.root 16 d then 16 ^ d else 0) = 16 ^ d; simp
  ha_init b hb := by show (if b = KBag.root 16 d then 16 ^ d else 0) = 0; rw [if_neg hb]
  hup_even t b ht := by
    by_cases hS : Sends d b.l t
    · by_cases hB : botR d b.l t
      · right; exact upOf_botR _ t b hS hB
      · left; rw [upOf_of_sends _ t b hS hB]; exact piC_even hd t b hS
    · left; rw [upOf_of_not_sends _ t b hS]; exact dvd_zero 2
  hup_root t ht := by
    by_cases hS : Sends d (KBag.root 16 d).l t
    · have h0 : (KBag.root 16 d).l = 0 := rfl
      have hα : alpha d t = 0 := by have := hS.1.2.1; rw [h0] at this; omega
      have hT : topD d (KBag.root 16 d).l t := ⟨by rw [h0, hα], root_topD d hd t hα⟩
      rw [upOf_of_sends _ t _ hS (fun h => h.2.1 hT.1), piC_topD d _ t hT]
    · exact upOf_of_not_sends _ t _ hS
  hdown_leaf t b j ht hb := by
    show downOf (aT d t) t b j = 0
    unfold downOf; rw [dif_neg (fun h => by have := h.2; omega)]
  hsplit t b ht := conserves_all hd t ht b
  hcons t b ht := rfl

theorem designP_a (hd : 10 ≤ d) (t : ℕ) (b : KBag 16 d) : (designP hd).a t b = aT d t b := rfl

/-- The table's deficit is `Gof`. -/
theorem designP_deficit (hd : 10 ≤ d) (t : ℕ) (b : KBag 16 d) :
    (designP hd).deficit t b = ((Gof (aT d t) b : ℤ) : ℚ) := by
  unfold FlowTableB.deficit Gof
  push_cast
  rfl

/-! ### Facts -/

theorem designP_parity (hd : 10 ≤ d) : ∀ t, t ≤ tf d → ParityFact (designP hd) t := by
  intro t ht b hb
  rw [designP_a]
  rcases Nat.eq_zero_or_pos t with rfl | ht1
  · show (if b = KBag.root 16 d then 16 ^ d else 0) = 0
    rw [if_neg]; rintro rfl; exact hb rfl
  · exact (J_all hd t ht1 ht).1 b (fun h => hb h.2.2.2)

theorem designP_final (hd : 10 ≤ d) : FinalFact (designP hd) := by
  intro b
  rw [designP_a]
  have htf1 : 1 ≤ tf d := by unfold tf; omega
  have hJ := J_all hd (tf d) htf1 le_rfl
  have hα := alpha_tf d hd
  have hω := omega_tf d hd
  by_cases hb : b.l = meet d
  · rw [if_pos hb]
    have hbl : b.l < d := by unfold meet at hb; omega
    have ha := a_eq_deficits (aT d (tf d)) b hbl
    have hG0 : Gof (aT d (tf d)) b = 0 := hJ.2.1 b (by omega)
    have hch : ∀ j : Fin 16, Gof (aT d (tf d)) (b.child j.val j.isLt hbl) = (16 : ℤ) ^ (d - (b.l + 1)) :=
      fun j => hJ.2.2.1 _ (by show omega (tf d) < b.l + 1; omega)
    rw [Finset.sum_congr rfl (fun j _ => hch j), Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, hG0, sub_zero] at ha
    have : ((aT d (tf d) b : ℕ) : ℤ) = ((16 ^ 4 : ℕ) : ℤ) := by
      rw [ha]; push_cast
      rw [show d - (b.l + 1) = 3 by unfold meet at hb; omega]; norm_num
    exact_mod_cast this
  · rw [if_neg hb]
    refine hJ.1 b (fun h => hb ?_)
    have := h.2.1; have := h.2.2.1; unfold meet; omega

theorem toNat_cast_real (x : ℤ) (hx : 0 ≤ x) : ((x.toNat : ℕ) : ℝ) = ((x : ℤ) : ℝ) := by
  have : ((x.toNat : ℕ) : ℤ) = x := Int.toNat_of_nonneg hx
  exact_mod_cast this

/-- A node with a positive down-flow sends and is not a rising bottom. -/
theorem sends_of_down (hd : 10 ≤ d) (t : ℕ) (q : KBag 16 d)
    (hpos : 0 < ∑ i, (designP hd).down t q i) :
    Sends d q.l t ∧ q.l < d ∧ ¬ botR d q.l t := by
  by_contra hno
  have hz : ∀ i : Fin 16, (designP hd).down t q i = 0 := by
    intro i
    show downOf (aT d t) t q i = 0
    unfold downOf
    by_cases h : Sends d q.l t ∧ q.l < d
    · rw [dif_pos h]
      have hB : botR d q.l t := by
        by_contra hB; exact hno ⟨h.1, h.2, hB⟩
      have hT : ¬ topD d q.l t := fun h' => hB.2.1 h'.1
      unfold thetaOf; rw [if_neg hT, if_pos hB, sub_self]; rfl
    · rw [dif_neg h]
  simp [hz] at hpos

set_option maxHeartbeats 2000000 in
/-- **The residual fact (I4).** -/
theorem designP_resid (hd : 10 ≤ d) : ResidFact (designP hd) := by
  intro t q hq j hj htf hpos
  obtain ⟨hS, _, hB⟩ := sends_of_down hd t q hpos
  have hc := (cap_pos d q.l t).le
  have hrc : (0 : ℝ) ≤ ((rstar * cap d q.l t : ℚ) : ℝ) := by
    have : (0 : ℚ) ≤ rstar * cap d q.l t := mul_nonneg (by unfold rstar; norm_num) hc
    exact_mod_cast this
  -- the deficits of the children and the `θ`s
  have hGd : ∀ h (hh : h < 16), Gd (designP hd) t q hq h =
      ((Gof (aT d t) (q.child h hh hq) : ℤ) : ℝ) := by
    intro h hh; unfold Gd; rw [dif_pos hh, designP_deficit]; push_cast; rfl
  have hdN : ∀ h (hh : h < 16), downN (designP hd) t q h = downOf (aT d t) t q ⟨h, hh⟩ := by
    intro h hh; unfold downN; rw [dif_pos hh]; rfl
  have hup : (designP hd).up t q = upOf (aT d t) t q := rfl
  by_cases hT : topD d q.l t
  · -- a descending top: `θ = 0`, `π = 0`
    have hdiff : ∀ h (hh : h < 16), Gd (designP hd) t q hq h - downN (designP hd) t q h = 0 := by
      intro h hh
      rw [hGd h hh, hdN h hh]
      unfold downOf
      rw [dif_pos ⟨hS, hq⟩]
      have hθ : thetaOf (aT d t) t q hq ⟨h, hh⟩ = 0 := by unfold thetaOf; rw [if_pos hT]
      show ((Gof (aT d t) (q.child h hh hq) : ℤ) : ℝ) -
        (((Gof (aT d t) (q.child h hh hq) - thetaOf (aT d t) t q hq ⟨h, hh⟩).toNat : ℕ) : ℝ) = 0
      rw [hθ, sub_zero]
      have hnn : 0 ≤ Gof (aT d t) (q.child h hh hq) := by
        rcases Nat.eq_zero_or_pos t with rfl | ht1
        · rw [Gof_zero, if_neg (fun e => by have := congrArg KBag.l e; simp [KBag.child, KBag.root] at this)]
          positivity
        · exact child_G_nonneg hd t ht1 htf (J_all hd t ht1 htf.le) q hS.1 hq ⟨h, hh⟩
      rw [toNat_cast_real _ hnn]; ring
    have hπ0 : (upOf (aT d t) t q : ℝ) = 0 := by
      rw [upOf_of_sends _ t q hS hB, piC_topD d _ t hT]; simp
    unfold residG
    rw [hup, hπ0]
    rw [Finset.sum_congr rfl (fun h hh => hdiff h (by simp at hh; omega)),
      Finset.sum_congr rfl (fun h hh => hdiff h (by simp at hh; omega))]
    simp
    exact_mod_cast hrc
  · -- the other senders
    have ht1 : 1 ≤ t := by
      by_contra h
      obtain rfl : t = 0 := by omega
      have := (sends_zero_iff hd q.l).1 hS
      exact hT (by rw [this]; exact topD_root_zero hd)
    have hJ := J_all hd t ht1 htf.le
    set π : ℤ := (upOf (aT d t) t q : ℤ) with hπ
    set G : ℤ := Gof (aT d t) q with hGdef
    set s : ℤ := sOf (aT d t) t q with hsdef
    have hdiff : ∀ h (hh : h < 16), Gd (designP hd) t q hq h - downN (designP hd) t q h =
        ((thetaP π G s h : ℤ) : ℝ) := by
      intro h hh
      rw [hGd h hh, hdN h hh]
      unfold downOf
      rw [dif_pos ⟨hS, hq⟩]
      show ((Gof (aT d t) (q.child h hh hq) : ℤ) : ℝ) -
        (((Gof (aT d t) (q.child h hh hq) - thetaOf (aT d t) t q hq ⟨h, hh⟩).toNat : ℕ) : ℝ) = _
      have hb := sender_theta_bounds hd t ht1 htf hJ q hS hT hB hq ⟨h, hh⟩
      have hl := sender_child_lb hd t ht1 htf hJ q hS hT hB hq ⟨h, hh⟩
      rw [toNat_cast_real _ (by linarith), thetaOf_eq _ _ _ _ _ hT hB]
      push_cast; ring
    unfold residG
    rw [Finset.sum_congr rfl (fun h hh => hdiff h (by simp at hh; omega)),
      Finset.sum_congr rfl (fun h hh => hdiff h (by simp at hh; omega))]
    have hπe : 2 ∣ π := by
      rw [hπ, upOf_of_sends _ t q hS hB]; exact_mod_cast piC_even hd t q hS
    -- the side conditions of `resid_thetaP` and `s ≤ r* c`
    have key : (0 ≤ π ∧ 0 ≤ G ∧ 0 ≤ s ∧ s ≤ π / 2 + G ∧ 0 ≤ 2 * s - G ∧
        G - (2 * s - G) / 14 ≤ s) ∧ ((s : ℚ) ≤ rstar * cap d q.l t) := by
      have hπv : π = piC d q.l t := by rw [hπ, upOf_of_sends _ t q hS hB]
      have hpi0 : 0 ≤ π := by rw [hπv]; positivity
      rcases Nat.eq_or_lt_of_le hS.1.2.1 with htop | hnt
      · have hG : G = 0 := hJ.2.1 q (le_of_eq htop.symm)
        have hs : s = 0 := by rw [hsdef]; unfold sOf; rw [if_pos hG]
        rw [hG, hs]
        refine ⟨⟨hpi0, le_rfl, le_rfl, by omega, by norm_num, by norm_num⟩, ?_⟩
        push_cast
        exact mul_nonneg (by unfold rstar; norm_num) hc
      · have ht2 : 2 ≤ t := by
          by_contra h
          obtain rfl : t = 1 := by omega
          have := hS.1.2.2.1; rw [omega_one] at this; rw [alpha_one] at hnt; omega
        have he : 19 ≤ eN d q.l t := by
          have := exp_nontop d t q.l ht2 (by
            have := hS.1.2.2.2; have := alpha_parity d t; omega)
          unfold eN; omega
        set X : ℤ := 2 ^ (eN d q.l t - 19) with hX
        have hX1 : 1 ≤ X := one_le_pow₀ (by norm_num)
        have h15 : (2 : ℤ) ^ (eN d q.l t - 15) = 16 * X := by
          rw [show eN d q.l t - 15 = (eN d q.l t - 19) + 4 by omega, pow_add, hX]; ring
        have hpiX : π = 2 * (63 * X) := by
          rw [hπv]; unfold piC; rw [if_neg hT, if_neg (by omega)]
          push_cast
          rw [show eN d q.l t - 18 = (eN d q.l t - 19) + 1 by omega, pow_succ, hX]; ring
        have hdiv : π / 2 = 63 * X := by rw [hpiX]; exact Int.mul_ediv_cancel_left _ (by norm_num)
        obtain ⟨hG0, hG1⟩ := hJ.2.2.2.1 q hS.1 hnt
        rw [h15] at hG1
        have hcap : cap d q.l t = ((2 ^ (eN d q.l t) : ℕ) : ℚ) :=
          cap_eq_pow d q.l t (eN d q.l t) (by
            have := exp_nontop d t q.l ht2 (by
              have := hS.1.2.2.2; have := alpha_parity d t; omega)
            unfold eN; push_cast; omega)
        by_cases hGz : G = 0
        · have hs : s = 0 := by rw [hsdef]; unfold sOf; rw [if_pos hGz]
          rw [hGz, hs]
          refine ⟨⟨hpi0, le_rfl, le_rfl, by omega, by norm_num, by norm_num⟩, ?_⟩
          push_cast
          exact mul_nonneg (by unfold rstar; norm_num) hc
        · have hs : s = 15 * X := by
            rw [hsdef]; unfold sOf; rw [if_neg hGz]; unfold sres; push_cast; rfl
          rw [hs]
          have hq0 : X ≤ (2 * (15 * X) - G) / 14 := by
            rw [Int.le_ediv_iff_mul_le (by norm_num)]; linarith
          refine ⟨⟨hpi0, hG0, by linarith, by rw [hdiv]; linarith, by linarith, by linarith⟩, ?_⟩
          rw [hcap, hX]
          have hsplit2 : ((2 ^ (eN d q.l t) : ℕ) : ℚ) = (2 : ℚ) ^ (eN d q.l t - 19) * 524288 := by
            push_cast
            rw [show eN d q.l t = (eN d q.l t - 19) + 19 by omega, pow_add]
            rw [show eN d q.l t - 19 + 19 - 19 = eN d q.l t - 19 by omega]
            norm_num
          rw [hsplit2]
          unfold rstar
          push_cast
          apply le_of_eq
          ring
    obtain ⟨⟨h1, h2, h3, h4, h5, h6⟩, hsr⟩ := key
    have hres := resid_thetaP π G s hπe h1 h2 h3 h4 h5 h6 j hj
    have hres' : ((max 0 (∑ h ∈ range j, thetaP π G s h - π / 2) +
        max 0 (∑ h ∈ Ico (j + 1) 16, thetaP π G s h - π / 2) : ℤ) : ℝ) ≤ ((s : ℤ) : ℝ) := by
      exact_mod_cast hres
    have hsr' : ((s : ℤ) : ℝ) ≤ ((rstar * cap d q.l t : ℚ) : ℝ) := by exact_mod_cast hsr
    have hπ2 : ((π / 2 : ℤ) : ℝ) = (π : ℝ) / 2 := by
      obtain ⟨p, hp⟩ := hπe; rw [hp]; push_cast; rw [Int.mul_ediv_cancel_left _ (by norm_num)]; ring
    push_cast at hres'
    rw [hπ2] at hres'
    have hcastπ : ((π : ℤ) : ℝ) = ((upOf (aT d t) t q : ℕ) : ℝ) := by rw [hπ]; push_cast; rfl
    rw [hcastπ] at hres'
    rw [hup]
    linarith

/-- **W1: the tree with design P.** For `d ≥ 10` and node networks meeting `R1Specs` on the
design-P table, there is a sorting network on `16^d` wires whose depth is at most the `t_f` stages
plus the final layer of bitonic sorters on `2^16`-wire blocks. -/
theorem r1_sorter_designP {d : ℕ} (sc : R1Scal) (hd : 10 ≤ d)
    (nets : ℕ → (b : KBag 16 d) → (n : ℕ) → ComparatorNetwork n)
    (hspec : R1Specs sc (designP hd) nets) :
    ∃ T : ComparatorNetwork (16 ^ d), ComparatorNetwork.Sorts.{0} T ∧
      T.depth ≤ (stagesNet (designP hd) nets (tf d)).depth +
        (stageNet (finalS (designP hd)) (fun _ n => bitonicNetwork n)).depth :=
  r1_sorter_of_facts hd (designP hd) nets hspec (designP_parity hd) (designP_resid hd)
    (designP_final hd)

end R1T
