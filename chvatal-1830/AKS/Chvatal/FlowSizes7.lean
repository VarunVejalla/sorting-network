module

/-
  # Natural-number flow sizes for the §7 schedule (B2c + B2d)

  Shows that the rational allocation and flows of `FlowTable` at `params7`
  (`k = 64`, `A = 4096`, `ν = 1/64`) are natural numbers for `2 ≤ t ≤ t_f`
  (and that the parent sends `π` are even), and adds the special steps `t = 0, 1`
  (DCS-TR-294 p. 6) to obtain `flowSizes7 d hd : FlowSizes d (tf7 d)`.

  With `capacity params7 d i t = 64^(d+2i) / 64^(t+2)` and `capacityRatio params7 = 64^6`,
  the exponent bounds `e(i,t) = d+2i-t-2 ≥ 3` (top), `≥ 6` (rising top), `≥ 7` (non-top)
  make every formula an explicit natural number.
-/

public import AKS.Chvatal.FlowSizes
public import AKS.Chvatal.FlowTable7

@[expose] public section

namespace Chvatal

theorem capacityRatio_params7 : capacityRatio params7 = (64 : ℚ) ^ 6 := by
  unfold capacityRatio params7; norm_num

theorem exp_nontop (d t i : ℕ) (hd : 7 ≤ d) (ht2 : 2 ≤ t) (ht : t < tf7 d)
    (h1 : alpha7 d t + 2 ≤ i) (h2 : i % 2 = t % 2) : t + 9 ≤ d + 2 * i := by
  rw [alpha7_of_ge_two d t ht2] at h1
  unfold tf7 at ht
  unfold ceilParity alphaStarLower at h1
  split_ifs at h1 <;> omega

theorem exp_top (d t : ℕ) (hd : 7 ≤ d) (ht2 : 2 ≤ t) (ht : t ≤ tf7 d) :
    t + 5 ≤ d + 2 * alpha7 d t := by
  rw [alpha7_of_ge_two d t ht2]
  unfold tf7 at ht
  unfold ceilParity alphaStarLower
  split_ifs <;> omega

theorem exp_top_rise (d t : ℕ) (hd : 7 ≤ d) (ht2 : 2 ≤ t) (ht : t < tf7 d)
    (hs : alpha7 d (t + 1) < alpha7 d t) : t + 8 ≤ d + 2 * alpha7 d t := by
  rw [alpha7_of_ge_two d t ht2] at hs ⊢
  rw [alpha7_of_ge_two d (t + 1) (by omega)] at hs
  unfold tf7 at ht
  unfold ceilParity alphaStarLower at hs ⊢
  split_ifs at hs ⊢ <;> omega

theorem omega7_lt_d (d t : ℕ) (hd : 7 ≤ d) (ht : t ≤ tf7 d) : omega7 d t + 1 ≤ d := by
  by_cases h2 : 2 ≤ t
  · rw [omega7_of_ge_two d t h2]
    unfold tf7 at ht
    unfold ceilParity omegaStarLower
    split_ifs <;> omega
  · unfold omega7; split_ifs <;> omega

theorem omega7_mul3 (d t : ℕ) (ht2 : 2 ≤ t) : 3 * omega7 d t ≤ t + 8 := by
  rw [omega7_of_ge_two d t ht2]
  unfold ceilParity omegaStarLower
  split_ifs <;> omega


theorem cdivQ (f : ℕ) :
    ((64 ^ (6 + f) : ℕ) : ℚ) / capacityRatio params7 = ((64 ^ f : ℕ) : ℚ) := by
  rw [capacityRatio_params7]; push_cast; rw [pow_add]; field_simp

private theorem alpha7_two (d : ℕ) (hd : 7 ≤ d) : alpha7 d 2 = 0 := by
  rw [alpha7_of_ge_two d 2 le_rfl]; unfold ceilParity alphaStarLower; split_ifs <;> omega
  
private theorem omega7_two (d : ℕ) : omega7 d 2 = 2 := by
  rw [omega7_of_ge_two d 2 le_rfl]; unfold ceilParity omegaStarLower; split_ifs <;> omega

/-- Bottom nodes before the final step: an explicit natural-number-valued allocation. -/
theorem alloc_bot_val (d : ℕ) (hd : 7 ≤ d) (t : ℕ) (ht2 : 2 ≤ t) (ht : t < tf7 d) (i : ℕ)
    (hact : t ≤ tf7 d ∧ alpha7 d t ≤ i ∧ i ≤ omega7 d t ∧ i % 2 = t % 2)
    (hα : i ≠ alpha7 d t) (hω : i = omega7 d t) :
    ∃ g h : ℕ, h ≤ g ∧ d = i + (g + 1) ∧ d + 2 * i = t + 9 + h ∧
      allocation params7 d (levelSchedule7 d hd) i t = (64 : ℚ) ^ (g + 1) - 64 ^ (h + 1) := by
  have hlt := alpha7_lt_omega7 d hd t ht2 ht
  have hp1 := alpha7_parity d t
  have hne := exp_nontop d t i hd ht2 ht (by omega) hact.2.2.2
  have hlt2 := omega7_lt_d d t hd hact.1
  have h3 := omega7_mul3 d t ht2
  obtain ⟨g, hg⟩ : ∃ g, d = i + (g + 1) := ⟨d - i - 1, by omega⟩
  obtain ⟨h, hh⟩ : ∃ h, d + 2 * i = t + 9 + h := ⟨d + 2 * i - (t + 9), by omega⟩
  refine ⟨g, h, by omega, hg, hh, ?_⟩
  have hc := capacity_params7 d i t (7 + h) (by omega)
  rw [alloc_bot params7 d (levelSchedule7 d hd) hact hα hω, hc, capacityRatio_params7]
  show (((64 ^ d : ℕ) : ℚ)) / ((params7.br : ℕ) : ℚ) ^ i - _ = _
  have e1 : (7 + h) = 6 + (h + 1) := by omega
  rw [e1]
  have := cdivQ (h + 1)
  rw [capacityRatio_params7] at this
  rw [this]
  have e2 : ((64 ^ d : ℕ) : ℚ) / ((params7.br : ℕ) : ℚ) ^ i = (64 : ℚ) ^ (g + 1) := by
    show ((64 ^ d : ℕ) : ℚ) / ((64 : ℕ) : ℚ) ^ i = _
    rw [hg]; push_cast; rw [pow_add]; field_simp
  rw [e2]; push_cast; rfl


theorem allocNat (d : ℕ) (hd : 7 ≤ d) (t : ℕ) (ht2 : 2 ≤ t) (ht : t ≤ tf7 d) (i : ℕ) :
    ∃ n : ℕ, allocation params7 d (levelSchedule7 d hd) i t = n := by
  by_cases hact : t ≤ tf7 d ∧ alpha7 d t ≤ i ∧ i ≤ omega7 d t ∧ i % 2 = t % 2
  swap
  · exact ⟨0, by rw [allocation_inactive _ _ _ _ _ hact]; simp⟩
  by_cases hα : i = alpha7 d t
  · have he := exp_top d t hd ht2 ht
    refine ⟨64 ^ (d + 2 * i - (t + 2)), ?_⟩
    rw [alloc_top params7 d (levelSchedule7 d hd) hact hα,
      capacity_params7 d i t (d + 2 * i - (t + 2)) (by omega)]
  have hlt : t < tf7 d := by
    by_contra hc
    have teq : t = tf7 d := by omega
    have := alpha7_tf_eq_omega7_tf d hd
    rw [← teq] at this
    have := hact.2.2.1
    have := hact.2.1
    by_cases hω : i = omega7 d t
    · omega
    · omega
  have hlt' := alpha7_lt_omega7 d hd t ht2 hlt
  have hp1 := alpha7_parity d t
  have hne := exp_nontop d t i hd ht2 hlt (by omega) hact.2.2.2
  by_cases hω : i = omega7 d t
  · obtain ⟨g, h, hgh, -, -, hv⟩ := alloc_bot_val d hd t ht2 hlt i hact hα hω
    refine ⟨64 ^ (g + 1) - 64 ^ (h + 1), ?_⟩
    rw [hv, Nat.cast_sub (Nat.pow_le_pow_right (by norm_num) (by omega))]
    push_cast; rfl
  · obtain ⟨f, hf⟩ : ∃ f, d + 2 * i = t + 8 + f := ⟨d + 2 * i - (t + 8), by omega⟩
    refine ⟨64 ^ (6 + f) - 64 ^ f, ?_⟩
    have hc := capacity_params7 d i t (6 + f) (by omega)
    rw [alloc_mid params7 d (levelSchedule7 d hd) hact hα hω, hc,
      Nat.cast_sub (Nat.pow_le_pow_right (by norm_num) (by omega))]
    rw [capacityRatio_params7]
    push_cast
    rw [pow_add]
    field_simp

/-- Parent sends are even natural numbers for `2 ≤ t < tf`. -/
theorem upEven (d : ℕ) (hd : 7 ≤ d) (t : ℕ) (ht2 : 2 ≤ t) (ht : t < tf7 d) (i : ℕ) :
    ∃ n : ℕ, flowUp params7 d (levelSchedule7 d hd) i t = 2 * n := by
  by_cases hact : t ≤ tf7 d ∧ alpha7 d t ≤ i ∧ i ≤ omega7 d t ∧ i % 2 = t % 2
  swap
  · exact ⟨0, by rw [flowUp_inactive _ _ _ hact]; simp⟩
  have hlt := alpha7_lt_omega7 d hd t ht2 ht
  have hp1 := alpha7_parity d t
  have hp2 := alpha7_parity d (t + 1)
  have hst := alpha7_step d t hd ht
  have hq1 := omega7_parity d t
  have hq2 := omega7_parity d (t + 1)
  have hqt := omega7_step d t hd ht
  by_cases hα : i = alpha7 d t
  · by_cases hs : alpha7 d t < alpha7 d (t + 1)
    · exact ⟨0, by rw [flowUp_top_desc params7 d (levelSchedule7 d hd) hact hα hs]; simp⟩
    · have he := exp_top_rise d t hd ht2 ht (by omega)
      obtain ⟨f, hf⟩ : ∃ f, d + 2 * i = t + 8 + f := ⟨d + 2 * i - (t + 8), by omega⟩
      refine ⟨32 * 64 ^ (1 + f), ?_⟩
      have hc := capacity_params7 d i t (6 + f) (by omega)
      rw [flowUp_top_rise params7 d (levelSchedule7 d hd) hact hα hs, hc]
      simp only [params7]
      push_cast
      ring
  · have hne := exp_nontop d t i hd ht2 ht (by omega) hact.2.2.2
    by_cases hω : i = omega7 d t
    · by_cases hs : omega7 d t < omega7 d (t + 1)
      · obtain ⟨g, hg⟩ : ∃ g, d + 2 * i = t + 9 + g := ⟨d + 2 * i - (t + 9), by omega⟩
        refine ⟨4095 * 32 * 64 ^ g, ?_⟩
        have hc := capacity_params7 d i t (7 + g) (by omega)
        rw [flowUp_mid params7 d (levelSchedule7 d hd) hact hα (fun _ => hs), hc,
          capacityRatio_params7]
        simp only [params7]
        push_cast
        ring
      · obtain ⟨g, h, hgh, -, -, hv⟩ := alloc_bot_val d hd t ht2 ht i hact hα hω
        refine ⟨32 * 64 ^ g - 32 * 64 ^ h, ?_⟩
        rw [flowUp_bot_rise params7 d (levelSchedule7 d hd) hact hα hω hs, hv,
          Nat.cast_sub (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hgh))]
        push_cast
        ring
    · obtain ⟨g, hg⟩ : ∃ g, d + 2 * i = t + 9 + g := ⟨d + 2 * i - (t + 9), by omega⟩
      refine ⟨4095 * 32 * 64 ^ g, ?_⟩
      have hc := capacity_params7 d i t (7 + g) (by omega)
      rw [flowUp_mid params7 d (levelSchedule7 d hd) hact hα (fun h => absurd h hω), hc,
        capacityRatio_params7]
      simp only [params7]
      push_cast
      ring

/-- Child sends are natural numbers for `2 ≤ t < tf`. -/
theorem downNat (d : ℕ) (hd : 7 ≤ d) (t : ℕ) (ht2 : 2 ≤ t) (ht : t < tf7 d) (i : ℕ) :
    ∃ n : ℕ, flowDown params7 d (levelSchedule7 d hd) i t = n := by
  by_cases hact : t ≤ tf7 d ∧ alpha7 d t ≤ i ∧ i ≤ omega7 d t ∧ i % 2 = t % 2
  swap
  · exact ⟨0, by rw [flowDown_inactive _ _ _ hact]; simp⟩
  have hlt := alpha7_lt_omega7 d hd t ht2 ht
  have hp1 := alpha7_parity d t
  have hp2 := alpha7_parity d (t + 1)
  have hst := alpha7_step d t hd ht
  have hq1 := omega7_parity d t
  have hq2 := omega7_parity d (t + 1)
  have hqt := omega7_step d t hd ht
  by_cases hα : i = alpha7 d t
  · by_cases hs : alpha7 d t < alpha7 d (t + 1)
    · have he := exp_top d t hd ht2 ht.le
      obtain ⟨g, hg⟩ : ∃ g, d + 2 * i = t + 3 + g := ⟨d + 2 * i - (t + 3), by omega⟩
      refine ⟨64 ^ g, ?_⟩
      have hc := capacity_params7 d i t (1 + g) (by omega)
      rw [flowDown_top_desc params7 d (levelSchedule7 d hd) hact hα hs, hc]
      simp only [params7]
      push_cast
      ring
    · have he := exp_top_rise d t hd ht2 ht (by omega)
      obtain ⟨f, hf⟩ : ∃ f, d + 2 * i = t + 8 + f := ⟨d + 2 * i - (t + 8), by omega⟩
      refine ⟨16777215 * 64 ^ (1 + f), ?_⟩
      have hc := capacity_params7 d i t (6 + f) (by omega)
      rw [flowDown_mid params7 d (levelSchedule7 d hd) hact (fun _ => hs) (by show i ≠ omega7 d t; omega), hc]
      simp only [params7]
      push_cast
      ring
  · have hne := exp_nontop d t i hd ht2 ht (by omega) hact.2.2.2
    by_cases hω : i = omega7 d t
    · by_cases hs : omega7 d t < omega7 d (t + 1)
      · obtain ⟨n, hn⟩ := allocNat d hd (t + 1) (by omega) ht (omega7 d t + 1)
        exact ⟨n, by
          rw [flowDown_bot_desc params7 d (levelSchedule7 d hd) hact hα hω hs]; exact hn⟩
      · exact ⟨0, by
          rw [flowDown_bot_rise params7 d (levelSchedule7 d hd) hact hα hω hs]; simp⟩
    · obtain ⟨g, hg⟩ : ∃ g, d + 2 * i = t + 9 + g := ⟨d + 2 * i - (t + 9), by omega⟩
      refine ⟨16777215 * 64 ^ (2 + g), ?_⟩
      have hc := capacity_params7 d i t (7 + g) (by omega)
      rw [flowDown_mid params7 d (levelSchedule7 d hd) hact (fun h => absurd h hα) hω, hc]
      simp only [params7]
      push_cast
      ring

/-! ## The flow sizes -/

/-- Wires per node: the paper's special steps `t = 0, 1`, and `⌊allocation⌋` for `t ≥ 2`. -/
def flowA7 (d : ℕ) (hd : 7 ≤ d) (l t : ℕ) : ℕ :=
  if t = 0 then (if l = 0 then 64 ^ d else 0)
  else if t = 1 then (if l = 1 then 64 ^ (d - 1) else 0)
  else ⌊allocation params7 d (levelSchedule7 d hd) l t⌋₊

/-- Wires sent to the parent. -/
def flowUp7 (d : ℕ) (hd : 7 ≤ d) (l t : ℕ) : ℕ :=
  if t = 0 then 0
  else if t = 1 then (if l = 1 then 64 ^ (d - 5) else 0)
  else ⌊flowUp params7 d (levelSchedule7 d hd) l t⌋₊

/-- Wires sent to each child. -/
def flowDown7 (d : ℕ) (hd : 7 ≤ d) (l t : ℕ) : ℕ :=
  if t = 0 then (if l = 0 then 64 ^ (d - 1) else 0)
  else if t = 1 then (if l = 1 then 64 ^ (d - 2) - 64 ^ (d - 6) else 0)
  else ⌊flowDown params7 d (levelSchedule7 d hd) l t⌋₊

theorem floor_of_eq (x : ℚ) (n : ℕ) (h : x = n) : ⌊x⌋₊ = n := by
  rw [h, Nat.floor_natCast]

theorem cast_flowA7 (d : ℕ) (hd : 7 ≤ d) (l t : ℕ) (ht2 : 2 ≤ t) (ht : t ≤ tf7 d) :
    ((flowA7 d hd l t : ℕ) : ℚ) = allocation params7 d (levelSchedule7 d hd) l t := by
  obtain ⟨n, hn⟩ := allocNat d hd t ht2 ht l
  have : flowA7 d hd l t = n := by
    unfold flowA7
    rw [if_neg (by omega), if_neg (by omega)]
    exact floor_of_eq _ _ hn
  rw [this, hn]

theorem cast_flowUp7 (d : ℕ) (hd : 7 ≤ d) (l t : ℕ) (ht2 : 2 ≤ t) (ht : t < tf7 d) :
    ((flowUp7 d hd l t : ℕ) : ℚ) = flowUp params7 d (levelSchedule7 d hd) l t ∧
      2 ∣ flowUp7 d hd l t := by
  obtain ⟨n, hn⟩ := upEven d hd t ht2 ht l
  have : flowUp7 d hd l t = 2 * n := by
    unfold flowUp7
    rw [if_neg (by omega), if_neg (by omega)]
    exact floor_of_eq _ _ (by rw [hn]; push_cast; rfl)
  rw [this, hn]
  exact ⟨by push_cast; rfl, ⟨n, rfl⟩⟩

theorem cast_flowDown7 (d : ℕ) (hd : 7 ≤ d) (l t : ℕ) (ht2 : 2 ≤ t) (ht : t < tf7 d) :
    ((flowDown7 d hd l t : ℕ) : ℚ) = flowDown params7 d (levelSchedule7 d hd) l t := by
  obtain ⟨n, hn⟩ := downNat d hd t ht2 ht l
  have : flowDown7 d hd l t = n := by
    unfold flowDown7
    rw [if_neg (by omega), if_neg (by omega)]
    exact floor_of_eq _ _ hn
  rw [this, hn]

/-- Allocation at `t = 2` (`α 2 = 0`, `ω 2 = 2`): `N/k²·(…)`, explicit values. -/
theorem flowA7_two (d : ℕ) (hd : 7 ≤ d) (h2 : 2 ≤ tf7 d) (l : ℕ) :
    flowA7 d hd l 2 =
      if l = 0 then 64 ^ (d - 4) else if l = 2 then 64 ^ (d - 2) - 64 ^ (d - 6) else 0 := by
  have ha := alpha7_two d hd
  have ho := omega7_two d
  unfold flowA7
  rw [if_neg (by omega), if_neg (by omega)]
  by_cases h0 : l = 0
  · subst h0
    rw [if_pos rfl]
    apply floor_of_eq
    have hact : 2 ≤ tf7 d ∧ alpha7 d 2 ≤ 0 ∧ 0 ≤ omega7 d 2 ∧ 0 % 2 = 2 % 2 := by
      refine ⟨h2, ?_, ?_, ?_⟩ <;> omega
    rw [alloc_top params7 d (levelSchedule7 d hd) hact (by show 0 = alpha7 d 2; omega),
      capacity_params7 d 0 2 (d - 4) (by omega)]
  by_cases h2' : l = 2
  · subst h2'
    rw [if_neg (by omega), if_pos rfl]
    apply floor_of_eq
    have hact : 2 ≤ tf7 d ∧ alpha7 d 2 ≤ 2 ∧ 2 ≤ omega7 d 2 ∧ 2 % 2 = 2 % 2 := by
      refine ⟨h2, ?_, ?_, ?_⟩ <;> omega
    rw [alloc_bot params7 d (levelSchedule7 d hd) hact (by show 2 ≠ alpha7 d 2; omega)
      (by show 2 = omega7 d 2; omega), capacity_params7 d 2 2 d (by omega),
      capacityRatio_params7]
    show (((64 ^ d : ℕ) : ℚ)) / ((64 : ℕ) : ℚ) ^ 2 - _ = _
    rw [Nat.cast_sub (Nat.pow_le_pow_right (by norm_num) (by omega))]
    obtain ⟨e, rfl⟩ : ∃ e, d = e + 6 := ⟨d - 6, by omega⟩
    have e1 : e + 6 - 2 = e + 4 := by omega
    have e2 : e + 6 - 6 = e := by omega
    rw [e1, e2]
    push_cast
    rw [pow_add, pow_add]
    field_simp
  · rw [if_neg h0, if_neg h2']
    apply floor_of_eq
    rw [allocation_inactive _ _ _ _ _ (by
      show ¬(2 ≤ tf7 d ∧ alpha7 d 2 ≤ l ∧ l ≤ omega7 d 2 ∧ l % 2 = 2 % 2)
      omega)]
    simp

theorem flowSizes7_split (d : ℕ) (hd : 7 ≤ d) (l t : ℕ) (ht : t < tf7 d) :
    flowA7 d hd l t = flowUp7 d hd l t + 64 * flowDown7 d hd l t := by
  rcases Nat.lt_or_ge t 2 with h | h
  · obtain rfl | rfl : t = 0 ∨ t = 1 := by omega
    · unfold flowA7 flowUp7 flowDown7
      by_cases hl : l = 0
      · subst hl
        simp only [if_true, add_zero]
        obtain ⟨e, rfl⟩ : ∃ e, d = e + 7 := ⟨d - 7, by omega⟩
        rw [show e + 7 - 1 = e + 6 by omega]
        ring
      · simp [hl]
    · unfold flowA7 flowUp7 flowDown7
      by_cases hl : l = 1
      · subst hl
        simp only [if_true, show (1 : ℕ) ≠ 0 by omega, if_false]
        obtain ⟨e, rfl⟩ : ∃ e, d = e + 7 := ⟨d - 7, by omega⟩
        have h1 : 64 ^ (e + 1) ≤ 64 ^ (e + 5) := Nat.pow_le_pow_right (by norm_num) (by omega)
        have e1 : e + 7 - 1 = e + 6 := by omega
        have e2 : e + 7 - 5 = e + 2 := by omega
        have e3 : e + 7 - 2 = e + 5 := by omega
        have e4 : e + 7 - 6 = e + 1 := by omega
        rw [e1, e2, e3, e4]
        zify [h1]
        ring
      · simp [hl]
  · have hf := (cast_flowUp7 d hd l t h ht).1
    have hf' := cast_flowDown7 d hd l t h ht
    have ha := cast_flowA7 d hd l t h ht.le
    have hs := flow_send_params7 d hd t h ht l
    have hbr : ((params7.br : ℕ) : ℚ) = 64 := by norm_num [params7]
    rw [hbr] at hs
    have : ((flowA7 d hd l t : ℕ) : ℚ) =
        ((flowUp7 d hd l t + 64 * flowDown7 d hd l t : ℕ) : ℚ) := by
      push_cast; rw [ha, hf, hf']; exact hs
    exact_mod_cast this

theorem flowSizes7_up_root (d : ℕ) (hd : 7 ≤ d) (t : ℕ) (ht : t < tf7 d) :
    flowUp7 d hd 0 t = 0 := by
  rcases Nat.lt_or_ge t 2 with h | h
  · obtain rfl | rfl : t = 0 ∨ t = 1 := by omega
    all_goals simp [flowUp7]
  · have hc := cast_flowUp7 d hd 0 t h ht
    have hz : flowUp params7 d (levelSchedule7 d hd) 0 t = 0 := by
      by_cases hact : t ≤ tf7 d ∧ alpha7 d t ≤ 0 ∧ 0 ≤ omega7 d t ∧ 0 % 2 = t % 2
      swap
      · exact flowUp_inactive _ _ _ hact
      have hp1 := alpha7_parity d t
      have hp2 := alpha7_parity d (t + 1)
      have hst := alpha7_step d t hd ht
      exact flowUp_top_desc params7 d (levelSchedule7 d hd) hact (by show 0 = alpha7 d t; omega)
        (by show alpha7 d t < alpha7 d (t + 1); omega)
    rw [hz] at hc
    exact_mod_cast hc.1

theorem flowSizes7_down_leaf (d : ℕ) (hd : 7 ≤ d) (t : ℕ) (ht : t < tf7 d) :
    flowDown7 d hd d t = 0 := by
  rcases Nat.lt_or_ge t 2 with h | h
  · obtain rfl | rfl : t = 0 ∨ t = 1 := by omega
    · simp [flowDown7]; omega
    · simp [flowDown7]; omega
  · have hc := cast_flowDown7 d hd d t h ht
    have hz : flowDown params7 d (levelSchedule7 d hd) d t = 0 := by
      apply flowDown_inactive
      have := omega7_lt_d d t hd ht.le
      show ¬(t ≤ tf7 d ∧ alpha7 d t ≤ d ∧ d ≤ omega7 d t ∧ d % 2 = t % 2)
      omega
    rw [hz] at hc
    exact_mod_cast hc

theorem flowSizes7_cons (d : ℕ) (hd : 7 ≤ d) (l t : ℕ) (ht : t < tf7 d) :
    flowA7 d hd l (t + 1) =
      (if 1 ≤ l then flowDown7 d hd (l - 1) t else 0) +
        (if l < d then 64 * flowUp7 d hd (l + 1) t else 0) := by
  rcases Nat.lt_or_ge t 2 with h | h
  · obtain rfl | rfl : t = 0 ∨ t = 1 := by omega
    · unfold flowA7 flowUp7 flowDown7
      by_cases hl : l = 0
      · subst hl; simp
      · by_cases hl1 : l = 1
        · subst hl1; simp
        · simp [hl, hl1]; intro h; omega
    · rw [flowA7_two d hd (by omega) l]
      unfold flowUp7 flowDown7
      by_cases hl : l = 0
      · subst hl
        simp only [show (0 : ℕ) < d by omega, if_true, show ¬ (1 ≤ 0) by omega, if_false,
          zero_add]
        simp only [show (0 + 1 : ℕ) = 1 from rfl, show (1 : ℕ) ≠ 0 by omega, if_false, if_true,
          show (1 : ℕ) = 1 from rfl]
        obtain ⟨e, rfl⟩ : ∃ e, d = e + 7 := ⟨d - 7, by omega⟩
        rw [show e + 7 - 4 = e + 3 by omega, show e + 7 - 5 = e + 2 by omega, ← pow_succ']
      · by_cases hl2 : l = 2
        · subst hl2
          simp
        · simp only [hl, hl2, if_false]
          by_cases hl1 : l = 1
          · subst hl1; simp
          · simp [hl, hl1, hl2]
  · have hbr : ((params7.br : ℕ) : ℚ) = 64 := by norm_num [params7]
    have hc := flow_conservation_params7 d hd t h (by omega) l
    rw [hbr] at hc
    have ha := cast_flowA7 d hd l (t + 1) (by omega) (by omega)
    have hdn : 1 ≤ l → ((flowDown7 d hd (l - 1) t : ℕ) : ℚ) =
        flowDown params7 d (levelSchedule7 d hd) (l - 1) t :=
      fun _ => cast_flowDown7 d hd (l - 1) t h ht
    have hup := (cast_flowUp7 d hd (l + 1) t h ht).1
    have hupz : ¬ l < d → flowUp params7 d (levelSchedule7 d hd) (l + 1) t = 0 := by
      intro hl
      apply flowUp_inactive
      have := omega7_lt_d d t hd ht.le
      show ¬(t ≤ tf7 d ∧ alpha7 d t ≤ l + 1 ∧ l + 1 ≤ omega7 d t ∧ (l + 1) % 2 = t % 2)
      omega
    have : ((flowA7 d hd l (t + 1) : ℕ) : ℚ) =
        (((if 1 ≤ l then flowDown7 d hd (l - 1) t else 0) +
          (if l < d then 64 * flowUp7 d hd (l + 1) t else 0) : ℕ) : ℚ) := by
      rw [ha, hc]
      by_cases h1 : 1 ≤ l <;> by_cases h2 : l < d
      · simp only [h1, h2, if_true]; push_cast; rw [hdn h1, hup]
      · simp only [h1, h2, if_true, if_false]; push_cast; rw [hdn h1, hupz h2]; simp
      · simp only [h1, h2, if_true, if_false]; push_cast; rw [hup]
      · simp only [h1, h2, if_true, if_false]; push_cast; rw [hupz h2]; simp
    exact_mod_cast this

/-- **B2c + B2d.** Natural-number flow sizes for the §7 schedule. -/
def flowSizes7 (d : ℕ) (hd : 7 ≤ d) : FlowSizes d (tf7 d) where
  a := flowA7 d hd
  up := flowUp7 d hd
  down := flowDown7 d hd
  ha_root := by simp [flowA7]
  ha_init := fun l hl => by simp [flowA7]; omega
  hup_even := fun l t ht => by
    rcases Nat.lt_or_ge t 2 with h | h
    · obtain rfl | rfl : t = 0 ∨ t = 1 := by omega
      · simp [flowUp7]
      · unfold flowUp7
        by_cases hl : l = 1
        · subst hl
          simp only [if_true, show (1 : ℕ) ≠ 0 by omega, if_false]
          exact Dvd.dvd.pow (by norm_num) (by omega)
        · simp [hl]
    · exact (cast_flowUp7 d hd l t h ht).2
  hup_root := fun t ht => flowSizes7_up_root d hd t ht
  hdown_leaf := fun t ht => flowSizes7_down_leaf d hd t ht
  hsplit := fun l t _ ht => flowSizes7_split d hd l t ht
  hcons := fun l t _ ht => flowSizes7_cons d hd l t ht

end Chvatal
