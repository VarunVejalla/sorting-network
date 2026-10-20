import AKS.Sub800.R1Geom
import AKS.Bounds.Certificate
import AKS.Sort.Shrink

/-! # The node networks of design P and the sorter (W2, step 4)

* `node_exists`: every sender with a positive down-flow has a node network meeting `NodeSpecAll`,
  of depth `≤ 2709` at `t = 0` and `≤ 1053` afterwards.
* `r1Nets`, `r1Nets_specs`: the chosen family satisfies `R1Specs (designP hd)`.
* `r1_sorter`: for `d ≥ 12` there is a sorting network on `16^d` wires of depth
  `≤ 2709 + 1053 (t_f − 1) + 136`. -/

namespace R1T

open Chvatal Tapered945 Sub800

variable {d : ℕ} (P : R1Point)

theorem cap_pow (d i t : ℕ) (h : 3 * t + 6 ≤ 4 * d + 5 * i) :
    cap d i t = ((2 ^ eN d i t : ℕ) : ℚ) :=
  cap_eq_pow d i t (eN d i t) (by unfold eN; omega)

theorem floor_le_nat {x : ℚ} {k : ℕ} (h : x ≤ k) : ⌊x⌋₊ ≤ k := by
  have := Nat.floor_le_floor h
  rwa [Nat.floor_natCast] at this

theorem mu_pow_lt_one {e : ℕ} (he : e ≤ 16) : P.sc.mu * ((2 ^ e : ℕ) : ℚ) < 1 := by
  have h1 : ((2 ^ e : ℕ) : ℚ) ≤ 2 ^ 16 := by
    push_cast; exact pow_le_pow_right₀ (by norm_num) he
  have h2 : 0 < P.sc.mu := P.sc.mu_pos
  calc P.sc.mu * ((2 ^ e : ℕ) : ℚ) ≤ P.sc.mu * 2 ^ 16 := by gcongr
    _ < 1 := P.sc.mu_final

/-- `3t + 6 ≤ 4d + 5i` for every sender at `t ≥ 1`. -/
theorem sender_exp (hd : 10 ≤ d) (t : ℕ) (ht1 : 1 ≤ t) (q : KBag 16 d) (hS : Sends d q.l t) :
    3 * t + 9 ≤ 4 * d + 5 * q.l := by
  obtain ⟨⟨_, hα, hω, _⟩, _⟩ := hS
  rcases Nat.lt_or_ge t 2 with h | h
  · obtain rfl : t = 1 := by omega
    rw [alpha_one] at hα; omega
  · have := exp_top d t h; omega

/-- No descending top at `t = 1`. -/
theorem not_topD_one (hd : 10 ≤ d) (i : ℕ) : ¬ topD d i 1 := by
  rintro ⟨_, h⟩
  rw [alpha_one, show (1 + 1 : ℕ) = 2 from rfl, alpha_two d hd] at h
  omega

/-- **The fringe range fits in the protected half**: `Jmax ≤ π/2` for every sender at `t ≥ 1`. -/
theorem jmax_le_half (hd : 10 ≤ d) (t : ℕ) (ht1 : 1 ≤ t) (q : KBag 16 d) (hS : Sends d q.l t)
    (hB : ¬ botR d q.l t) : JmaxR P.sc d t q.l ≤ upOf (aT d t) t q / 2 := by
  unfold JmaxR
  split_ifs with hl0
  · exact Nat.zero_le _
  have hexp := sender_exp hd t ht1 q hS
  rw [upOf_of_sends _ t q hS hB, cap_pow d q.l t (by omega)]
  obtain ⟨⟨_, hα, hω, hpar⟩, htf⟩ := hS
  have hαp := alpha_parity d t
  by_cases hT : topD d q.l t
  · have h2 : 2 ≤ t := by
      by_contra h; obtain rfl : t = 1 := by omega
      exact not_topD_one hd _ hT
    have := exp_top_desc d t hd h2 hT.2 (by rw [← hT.1]; exact hl0)
    rw [Nat.floor_eq_zero.mpr (mu_pow_lt_one P (by rw [hT.1]; unfold eN; omega))]
    exact Nat.zero_le _
  by_cases he : eN d q.l t ≤ 16
  · rw [Nat.floor_eq_zero.mpr (mu_pow_lt_one P he)]; exact Nat.zero_le _
  have hmu : 0 < P.sc.mu := P.sc.mu_pos
  by_cases hl : q.l = alpha d t
  · rw [piC_rise q.l t hl hT]
    apply floor_le_nat
    have hd2 : 2 ^ (eN d q.l t - 12) / 2 = 2 ^ (eN d q.l t - 13) := by
      rw [show eN d q.l t - 12 = (eN d q.l t - 13) + 1 by omega, pow_succ, Nat.mul_div_cancel _ (by norm_num)]
    rw [hd2]
    have hp : ((2 ^ eN d q.l t : ℕ) : ℚ) = 8192 * ((2 ^ (eN d q.l t - 13) : ℕ) : ℚ) := by
      rw [show eN d q.l t = (eN d q.l t - 13) + 13 by omega, pow_add]
      rw [show eN d q.l t - 13 + 13 - 13 = eN d q.l t - 13 by omega]; push_cast; ring
    rw [hp]
    have h0 : (0 : ℚ) ≤ ((2 ^ (eN d q.l t - 13) : ℕ) : ℚ) := by positivity
    have : P.sc.mu * 8192 ≤ 1 := P.sc.mu_rise
    push_cast at h0 ⊢
    nlinarith
  · have h2 : 2 ≤ t := by
      by_contra h; obtain rfl : t = 1 := by omega
      rw [alpha_one] at hα hl; rw [omega_one] at hω; omega
    have h19 := exp_nontop d t q.l h2 (by omega)
    rw [piC_mid q.l t hl]
    apply floor_le_nat
    have hd2 : 63 * 2 ^ (eN d q.l t - 18) / 2 = 63 * 2 ^ (eN d q.l t - 19) := by
      rw [show eN d q.l t - 18 = (eN d q.l t - 19) + 1 by unfold eN; omega, pow_succ,
        show 63 * (2 ^ (eN d q.l t - 19) * 2) = 2 * (63 * 2 ^ (eN d q.l t - 19)) by ring,
        Nat.mul_div_cancel_left _ (by norm_num)]
    rw [hd2]
    have hp : ((2 ^ eN d q.l t : ℕ) : ℚ) = 524288 * ((2 ^ (eN d q.l t - 19) : ℕ) : ℚ) := by
      rw [show eN d q.l t = (eN d q.l t - 19) + 19 by unfold eN; omega, pow_add]
      rw [show eN d q.l t - 19 + 19 - 19 = eN d q.l t - 19 by omega]; push_cast; ring
    rw [hp]
    have h0 : (0 : ℚ) ≤ ((2 ^ (eN d q.l t - 19) : ℕ) : ℚ) := by positivity
    have : P.sc.mu * 524288 ≤ 63 := P.sc.mu_mid
    push_cast at h0 ⊢
    nlinarith

/-! ### Role data of large senders -/

/-- A large non-descending-top sender at `t ≥ 1` falls in one of the two fringe classes. -/
theorem role_data (hd : 10 ≤ d) (t : ℕ) (ht1 : 1 ≤ t) (htf : t < tf d) (q : KBag 16 d)
    (hS : Sends d q.l t) (hB : ¬ botR d q.l t) (hT : ¬ topD d q.l t)
    (hbig : 2 ^ P.s < aT d t q) :
    ∃ X : ℕ, cap d q.l t = ((524288 * X : ℕ) : ℚ) ∧
      (((upOf (aT d t) t q / 2 = 64 * X ∨ upOf (aT d t) t q / 2 = 63 * X) ∧
          524032 * X ≤ aT d t q ∧ aT d t q ≤ 525312 * X) ∨
        (upOf (aT d t) t q / 2 = 63 * X ∧ 8176 * X ≤ aT d t q ∧ aT d t q ≤ 8192 * X)) := by
  have hexp := sender_exp hd t ht1 q hS
  have hup := upOf_of_sends (aT d t) t q hS hB
  have hs := P.hs
  -- `π/2` from the role, given `e ≥ 19`
  have hpi : ∀ (he : 19 ≤ eN d q.l t),
      (q.l = alpha d t → upOf (aT d t) t q / 2 = 64 * 2 ^ (eN d q.l t - 19)) ∧
      (q.l ≠ alpha d t → upOf (aT d t) t q / 2 = 63 * 2 ^ (eN d q.l t - 19)) := by
    intro he
    refine ⟨fun hl => ?_, fun hl => ?_⟩
    · rw [hup, piC_rise q.l t hl hT,
        show eN d q.l t - 12 = (eN d q.l t - 19) + 7 by omega, pow_add]
      omega
    · rw [hup, piC_mid q.l t hl, show eN d q.l t - 18 = (eN d q.l t - 19) + 1 by omega, pow_add]
      omega
  have hcap : ∀ (he : 19 ≤ eN d q.l t), cap d q.l t = ((524288 * 2 ^ (eN d q.l t - 19) : ℕ) : ℚ) := by
    intro he
    rw [cap_pow d q.l t (by omega), show eN d q.l t = (eN d q.l t - 19) + 19 by omega, pow_add]
    rw [show eN d q.l t - 19 + 19 - 19 = eN d q.l t - 19 by omega]; push_cast; ring
  have hu : ∀ (he : 19 ≤ eN d q.l t), (2 : ℤ) ^ (eN d q.l t - 12) = 128 * ((2 ^ (eN d q.l t - 19) : ℕ) : ℤ) := by
    intro he
    rw [show eN d q.l t - 12 = (eN d q.l t - 19) + 7 by omega, pow_add]; push_cast; ring
  rcases Nat.lt_or_ge t 2 with h1 | h2
  · -- `t = 1`
    obtain rfl : t = 1 := by omega
    obtain ⟨hl, ha⟩ := occ_t1 hd q hS
    have he : 19 ≤ eN d q.l 1 := by rw [hl]; unfold eN; omega
    set X := 2 ^ (eN d q.l 1 - 19) with hX
    have ha' : aT d 1 q = 524288 * X := by
      have : (aT d 1 q : ℤ) = 524288 * (X : ℤ) := by
        rw [ha, hX, show eN d q.l 1 = (eN d q.l 1 - 19) + 19 by omega, pow_add]; push_cast; ring
      exact_mod_cast this
    refine ⟨X, hcap he, Or.inl ⟨Or.inl ((hpi he).1 (by rw [hl, alpha_one])), by omega,
      by omega⟩⟩
  · obtain ⟨⟨_, hα, hω, hpar⟩, _⟩ := id hS
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    rcases Nat.lt_or_ge q.l (omega (s + 1)) with hlt | hge
    · -- not at the bottom
      have hcr := occ_crude hd s (by omega) htf q hS hlt
      have he : 19 ≤ eN d q.l (s + 1) := by
        by_contra h
        have : (2 : ℤ) ^ (eN d q.l (s + 1) + 19) ≤ 2 ^ P.s := pow_le_pow_right₀ (by norm_num) (by omega)
        have : ((aT d (s + 1) q : ℕ) : ℤ) > 2 ^ P.s := by exact_mod_cast hbig
        linarith
      obtain ⟨hlo, hhi⟩ := occ_inner hd s (by omega) htf q hS hlt he
      rw [hu he] at hlo hhi
      set X := 2 ^ (eN d q.l (s + 1) - 19) with hX
      have hlo' : 524032 * X ≤ aT d (s + 1) q := by
        have : ((524032 * X : ℕ) : ℤ) ≤ aT d (s + 1) q := by push_cast; linarith
        exact_mod_cast this
      have hhi' : aT d (s + 1) q ≤ 525312 * X := by
        have : (aT d (s + 1) q : ℤ) ≤ ((525312 * X : ℕ) : ℤ) := by push_cast; linarith
        exact_mod_cast this
      refine ⟨X, hcap he, Or.inl ⟨?_, hlo', hhi'⟩⟩
      by_cases hl : q.l = alpha d (s + 1)
      · exact Or.inl ((hpi he).1 hl)
      · exact Or.inr ((hpi he).2 hl)
    · -- a descending bottom
      have hωx : q.l = omega (s + 1) := by omega
      have hαω := alpha_lt_omega d (s + 1) hd h2 htf
      obtain ⟨he, R, ha, hG0, hG1, hR⟩ := occ_botD hd (s + 1) h2 htf q
        ⟨⟨by omega, hα, hω, hpar⟩, htf⟩ hωx hB
      set X := 2 ^ (eN d q.l (s + 1) - 19) with hX
      have h15 : (2 : ℤ) ^ (eN d q.l (s + 1) - 15) = 16 * (X : ℤ) := by
        rw [hX, show eN d q.l (s + 1) - 15 = (eN d q.l (s + 1) - 19) + 4 by omega, pow_add]; push_cast; ring
      have he' : (2 : ℤ) ^ eN d q.l (s + 1) = 524288 * (X : ℤ) := by
        rw [hX, show eN d q.l (s + 1) = (eN d q.l (s + 1) - 19) + 19 by omega, pow_add]
        rw [show eN d q.l (s + 1) - 19 + 19 - 19 = eN d q.l (s + 1) - 19 by omega]; push_cast; ring
      rw [h15] at hG1
      have hπ := (hpi he).2 (by omega)
      rcases hR with hR | hR
      · rw [hR, he'] at ha
        have hlo' : 524032 * X ≤ aT d (s + 1) q := by
          have : ((524032 * X : ℕ) : ℤ) ≤ aT d (s + 1) q := by push_cast; linarith
          exact_mod_cast this
        have hhi' : aT d (s + 1) q ≤ 525312 * X := by
          have : (aT d (s + 1) q : ℤ) ≤ ((525312 * X : ℕ) : ℤ) := by push_cast; linarith
          exact_mod_cast this
        exact ⟨X, hcap he, Or.inl ⟨Or.inr hπ, hlo', hhi'⟩⟩
      · rw [he'] at hR
        have hR' : R = 8192 * (X : ℤ) := by linarith
        rw [hR'] at ha
        have hlo' : 8176 * X ≤ aT d (s + 1) q := by
          have : ((8176 * X : ℕ) : ℤ) ≤ aT d (s + 1) q := by push_cast; linarith
          exact_mod_cast this
        have hhi' : aT d (s + 1) q ≤ 8192 * X := by
          have : (aT d (s + 1) q : ℤ) ≤ ((8192 * X : ℕ) : ℤ) := by push_cast; linarith
          exact_mod_cast this
        exact ⟨X, hcap he, Or.inr ⟨hπ, hlo', hhi'⟩⟩

/-! ### Node networks -/

/-- The stage depth budget. -/
def stageD (t : ℕ) : ℕ := if t = 0 then 2709 else P.stage

theorem jmaxR_real_le (t l : ℕ) : ((JmaxR P.sc d t l : ℕ) : ℝ) ≤ (((P.sc.mu * cap d l t : ℚ)) : ℝ) := by
  have h0 : (0 : ℚ) ≤ P.sc.mu * cap d l t := mul_nonneg P.sc.mu_pos.le (cap_pos d l t).le
  have : ((JmaxR P.sc d t l : ℕ) : ℚ) ≤ P.sc.mu * cap d l t := by
    unfold JmaxR; split_ifs
    · simpa using h0
    · exact Nat.floor_le h0
  exact_mod_cast this

/-- The fringe range from the support check. -/
theorem jmax_of_support (F : FClass) (t l X n : ℕ) (hcap : cap d l t = ((524288 * X : ℕ) : ℚ))
    (hsupp : ((P.sc.mu : ℚ) : ℝ) * ((524288 * X : ℕ) : ℝ) ≤ (F.dF : ℝ) * ((F.C.P.f : ℝ) * n)) :
    JmaxR P.sc d t l ≤ F.C.P.jmax n := by
  have hJr := jmaxR_real_le P (d := d) t l
  rw [hcap] at hJr
  unfold F2PD.jmax
  apply Nat.le_floor
  rw [F.hδ]
  push_cast at hJr hsupp ⊢
  linarith

/-- A large non-descending-top sender gets the padded separator. -/
theorem large_spec (hd : 10 ≤ d) (t : ℕ) (ht1 : 1 ≤ t) (htf : t < tf d) (q : KBag 16 d)
    (hS : Sends d q.l t) (hB : ¬ botR d q.l t) (hT : ¬ topD d q.l t)
    (hbig : 2 ^ P.s < aT d t q) :
    ∃ net : ComparatorNetwork (aT d t q), NodeSpecAll (aT d t q) (upOf (aT d t) t q) net
      (EBv P.sc d t q.l) (JmaxR P.sc d t q.l) ((P.sc.epsF : ℚ) : ℝ) ∧ net.depth ≤ P.stage := by
  obtain ⟨X, hcap, hrole⟩ := role_data P hd t ht1 htf q hS hB hT hbig
  have hEBv : EBv P.sc d t q.l =
      ((((P.sc.epsB * P.sc.eta + P.sc.gam) * ((524288 * X : ℕ) : ℚ) / 2 : ℚ)) : ℝ) := by
    unfold EBv; rw [hcap]
  rw [hEBv]
  rcases hrole with ⟨hK, hL, hH⟩ | ⟨hπ, hL, hH⟩
  · obtain ⟨K, hK', hπ⟩ : ∃ K, (K = 63 ∨ K = 64) ∧ upOf (aT d t) t q / 2 = K * X := by
      rcases hK with h | h
      · exact ⟨64, Or.inr rfl, h⟩
      · exact ⟨63, Or.inl rfl, h⟩
    obtain ⟨m, n, hn16, ha, hlive, hfm, hmlo, hmhi, hπa, hfr, hsupp, hEB⟩ :=
      geomA P K _ _ X hK' hπ hL hH hbig
    exact spec_padded P P.A P.hJA m n hn16 ha hlive hfm hmlo hmhi hπa hfr _
      (jmax_of_support P P.A t q.l X n hcap hsupp) _ hEB
  · obtain ⟨m, n, hn16, ha, hlive, hfm, hmlo, hmhi, hπa, hfr, hsupp, hEB⟩ :=
      geomB P _ _ X hπ hL hH hbig
    exact spec_padded P P.B P.hJB m n hn16 ha hlive hfm hmlo hmhi hπa hfr _
      (jmax_of_support P P.B t q.l X n hcap hsupp) _ hEB

/-- A large descending top is the root; it gets the B-only separator. -/
theorem large_topD_spec (hd : 10 ≤ d) (t : ℕ) (ht1 : 1 ≤ t) (htf : t < tf d) (q : KBag 16 d)
    (hS : Sends d q.l t) (hT : topD d q.l t) (hbig : 2 ^ P.s < aT d t q) :
    ∃ net : ComparatorNetwork (aT d t q), NodeSpecAll (aT d t q) (upOf (aT d t) t q) net
      (EBv P.sc d t q.l) (JmaxR P.sc d t q.l) ((P.sc.epsF : ℚ) : ℝ) ∧ net.depth ≤ P.stage := by
  have hs := P.hs
  have h2 : 2 ≤ t := by
    by_contra h; obtain rfl : t = 1 := by omega
    exact not_topD_one hd _ hT
  have hαω := alpha_lt_omega d t hd h2 htf
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  have hlt : q.l < omega (s + 1) := by rw [hT.1]; exact hαω
  have hcr := occ_crude hd s (by omega) htf q hS hlt
  have hbigZ : ((aT d (s + 1) q : ℕ) : ℤ) > 2 ^ P.s := by exact_mod_cast hbig
  have he : 19 ≤ eN d q.l (s + 1) := by
    by_contra h
    have : (2 : ℤ) ^ (eN d q.l (s + 1) + 19) ≤ 2 ^ P.s := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  have hl0 : q.l = 0 := by
    by_contra h0
    have := exp_top_desc d (s + 1) hd h2 hT.2 (by rw [← hT.1]; exact h0)
    have : eN d q.l (s + 1) ≤ 16 := by rw [hT.1]; unfold eN; omega
    omega
  have hJ0 : JmaxR P.sc d (s + 1) q.l = 0 := by unfold JmaxR; rw [if_pos hl0]
  rw [hJ0]
  obtain ⟨-, hhi⟩ := occ_inner hd s (by omega) htf q hS hlt he
  have hexp := sender_exp hd (s + 1) (by omega) q hS
  set e := eN d q.l (s + 1) with he_def
  have hcap := cap_pow d q.l (s + 1) (by omega)
  rw [← he_def] at hcap
  have ha : ((aT d (s + 1) q : ℕ) : ℚ) ≤ 4104 * 2 ^ e / 4096 := by
    have h1 : ((aT d (s + 1) q : ℕ) : ℚ) ≤ 4104 * 2 ^ (e - 12) := by exact_mod_cast hhi
    have h2 : (2 : ℚ) ^ e = 2 ^ (e - 12) * 4096 := by
      rw [show (4096 : ℚ) = 2 ^ 12 by norm_num, ← pow_add, show e - 12 + 12 = e by omega]
    rw [h2]; linarith
  have hEBv : EBv P.sc d (s + 1) q.l =
      ((((P.sc.epsB * P.sc.eta + P.sc.gam) * 2 ^ e / 2 : ℚ)) : ℝ) := by
    unfold EBv; rw [hcap]; push_cast; ring
  rw [hEBv]
  exact spec_Bonly P _ hbig e ha _

/-- **Every active sender has a node network.** -/
theorem node_exists (hd : 12 ≤ d) (t : ℕ) (q : KBag 16 d) (htf : t < tf d)
    (hpos : 0 < ∑ i, (designP (show 10 ≤ d by omega)).down t q i) :
    ∃ net : ComparatorNetwork (aT d t q), NodeSpecAll (aT d t q) (upOf (aT d t) t q) net
      (EBv P.sc d t q.l) (JmaxR P.sc d t q.l) ((P.sc.epsF : ℚ) : ℝ) ∧ net.depth ≤ stageD P t := by
  have hd10 : 10 ≤ d := by omega
  obtain ⟨hS, hq, hB⟩ := sends_of_down hd10 t q hpos
  rcases Nat.eq_zero_or_pos t with rfl | ht1
  · -- the root at `t = 0`
    have hl : q.l = 0 := (sends_zero_iff hd10 q.l).1 hS
    have hr : q = KBag.root 16 d := by
      apply KBag.ext
      · exact hl
      · have := q.hx; rw [hl] at this; simp [KBag.root]; omega
    have ha : aT d 0 q = 16 ^ d := by show (if q = KBag.root 16 d then 16 ^ d else 0) = _; rw [if_pos hr]
    have hJ0 : JmaxR P.sc d 0 q.l = 0 := by unfold JmaxR; rw [if_pos hl]
    rw [ha, hJ0]
    obtain ⟨net, hspec, hdep⟩ := spec_root hd (upOf (aT d 0) 0 q) (EBv P.sc d 0 q.l)
      ((P.sc.epsF : ℚ) : ℝ) (by
      have hcap := cap_pow d 0 0 (by omega)
      rw [show eN d 0 0 = 4 * d - 6 by unfold eN; omega] at hcap
      unfold EBv; rw [hl, hcap]
      have hR : ((((1 / 59000000 : ℚ) / 2 * 64 + 1 / 2 ^ 36 : ℚ)) : ℝ) ≤
          ((((P.sc.epsB * P.sc.eta + P.sc.gam) / 2 : ℚ)) : ℝ) := by exact_mod_cast P.root
      push_cast at hR ⊢
      set C : ℝ := (2 : ℝ) ^ (4 * d - 42) with hC
      have h16 : (16 : ℝ) ^ d = 2 ^ 42 * C := by
        rw [hC, ← pow_add, show 42 + (4 * d - 42) = 4 * d by omega, pow_mul]; norm_num
      have h6 : (2 : ℝ) ^ (4 * d - 6) = 2 ^ 36 * C := by
        rw [hC, ← pow_add, show 36 + (4 * d - 42) = 4 * d - 6 by omega]
      rw [h16, h6]
      have := mul_le_mul_of_nonneg_right hR (by positivity : (0 : ℝ) ≤ 2 ^ 36 * C)
      linarith)
    exact ⟨net, hspec, by unfold stageD; simpa using hdep⟩
  · have hst : stageD P t = P.stage := by unfold stageD; rw [if_neg (by omega)]
    rw [hst]
    by_cases hsmall : aT d t q ≤ 2 ^ P.s
    · refine spec_sorter P _ hsmall ?_ (by exact_mod_cast P.sc.epsF_pos)
        (jmax_le_half P hd10 t ht1 q hS hB)
      unfold EBv
      have : (0 : ℚ) ≤ (P.sc.epsB * P.sc.eta + P.sc.gam) * cap d q.l t / 2 := by
        have := cap_pos d q.l t
        have := P.sc.epsB_nonneg; have := P.sc.eta_nonneg; have := P.sc.gam_nonneg
        positivity
      exact_mod_cast this
    · by_cases hT : topD d q.l t
      · exact large_topD_spec P hd10 t ht1 htf q hS hT (by omega)
      · exact large_spec P hd10 t ht1 htf q hS hB hT (by omega)

/-! ### The chosen family -/

/-- The property a node network must have. -/
def GoodNet (hd : 12 ≤ d) (t : ℕ) (q : KBag 16 d) (n : ℕ) (net : ComparatorNetwork n) : Prop :=
  (n = aT d t q → t < tf d → 0 < ∑ i, (designP (show 10 ≤ d by omega)).down t q i →
    NodeSpecAll n (upOf (aT d t) t q) net (EBv P.sc d t q.l) (JmaxR P.sc d t q.l)
      ((P.sc.epsF : ℚ) : ℝ)) ∧
  net.depth ≤ stageD P t

theorem goodNet_exists (hd : 12 ≤ d) (t : ℕ) (q : KBag 16 d) (n : ℕ) :
    ∃ net : ComparatorNetwork n, GoodNet P hd t q n net := by
  by_cases hc : n = aT d t q ∧ t < tf d ∧ 0 < ∑ i, (designP (show 10 ≤ d by omega)).down t q i
  · obtain ⟨hn, ht, hp⟩ := hc
    subst hn
    obtain ⟨net, hspec, hdep⟩ := node_exists P hd t q ht hp
    exact ⟨net, fun _ _ _ => hspec, hdep⟩
  · exact ⟨⟨[]⟩, fun h1 h2 h3 => absurd ⟨h1, h2, h3⟩ hc, by simp [ComparatorNetwork.depth]⟩

/-- The node networks of design P. -/
noncomputable def r1Nets (hd : 12 ≤ d) : ℕ → (b : KBag 16 d) → (n : ℕ) → ComparatorNetwork n :=
  fun t q n => Classical.choose (goodNet_exists P hd t q n)

theorem r1Nets_good (hd : 12 ≤ d) (t : ℕ) (q : KBag 16 d) (n : ℕ) :
    GoodNet P hd t q n (r1Nets P hd t q n) :=
  Classical.choose_spec (goodNet_exists P hd t q n)

theorem r1Nets_specs (hd : 12 ≤ d) :
    R1Specs P.sc (designP (show 10 ≤ d by omega)) (r1Nets P hd) := by
  intro t q htf hpos
  have hc : (wireSets (designP (show 10 ≤ d by omega)) t q).card = aT d t q :=
    wireSets_card _ htf.le q
  exact (r1Nets_good P hd t q _).1 hc htf hpos

/-! ### The sorter -/

theorem final_depth (hd : 10 ≤ d) :
    (stageNet (finalS (designP hd)) (fun _ n => bitonicNetwork n)).depth ≤ 136 := by
  refine stageNet_depth_le _ (finalS_disjoint _) _ (fun b => ?_)
  rcases finalS_card_cases (designP hd) (designP_final hd) b with h | h
  · rw [h]; refine (bitonicNetwork_depth_le_budget 0).trans ?_; simp [bitonicDepthBudget]
  · rw [h, show (2 : ℕ) ^ 16 = 2 ^ 16 from rfl]
    refine (bitonicNetwork_depth_le_budget _).trans ?_
    rw [Nat.clog_pow 2 16 (by norm_num), bitonicDepthBudget_eq]

theorem sum_stageD (T : ℕ) (hT : 1 ≤ T) :
    ∑ t ∈ Finset.range T, stageD P t = 2709 + P.stage * (T - 1) := by
  induction T, hT using Nat.le_induction with
  | base => simp [stageD]
  | succ T hT ih =>
    rw [Finset.sum_range_succ, ih]
    unfold stageD; rw [if_neg (by omega)]
    rw [show T + 1 - 1 = (T - 1) + 1 by omega]; ring

/-- **The R1 sorter.** For `d ≥ 12`: a sorting network on `16^d` wires of depth
`≤ 2709 + 3 S(q) (3d − 15) + 136`. -/
theorem r1_sorter (hd : 12 ≤ d) :
    ∃ T : ComparatorNetwork (16 ^ d), ComparatorNetwork.Sorts.{0} T ∧
      T.depth ≤ 2709 + P.stage * (3 * d - 15) + 136 := by
  have hd10 : 10 ≤ d := by omega
  obtain ⟨T, hs, hdep⟩ := r1_sorter_designP P.sc hd10 (r1Nets P hd) (r1Nets_specs P hd)
  refine ⟨T, hs, hdep.trans ?_⟩
  have h1 := stagesNet_depth_le (designP hd10) (r1Nets P hd) (stageD P) (tf d) (by omega)
    (fun t _ b n => (r1Nets_good P hd t b n).2)
  rw [sum_stageD P _ (by unfold tf; omega)] at h1
  have h2 := final_depth hd10
  have htf : tf d - 1 = 3 * d - 15 := by unfold tf; omega
  rw [htf] at h1
  omega

end R1T
