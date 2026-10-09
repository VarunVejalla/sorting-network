module

public import AKS.Chvatal.GeometryScale
public import AKS.Chvatal.FlowSizes7

@[expose] public section

/-! Node geometry (B5c/A10, DCS-TR-294 §5/§7): every node that sends wires down and holds more
than `2^64` wires runs the separator on an `m × n` matrix with `2^59 < m ≤ 2^60`; `nodeGeom_of_template`
scales a template into this range and each node type of the `flowSizes7` schedule has one. -/

namespace Chvatal

/-- Geometry of the separator at a node with `a` wires, sending `up` wires to the parent
and `down` wires to each child. -/
structure NodeGeom (a up down : ℕ) where
  m : ℕ
  n : ℕ
  f : ℕ
  b : ℕ
  hm : m = 2 * f + 64 * b
  ha : a = m * n
  hup : up = 2 * f * n
  hdown : down = b * n
  hm1 : 2 ^ 59 < m
  hm2 : m ≤ 2 ^ 60
  hn : 16 ≤ n
  hf : f = 0 ∨ (17 * 10 ^ 9 ≤ f ∧ Even f)

/-! ## G1: generic scaling -/

theorem nodeGeom_of_template (s m' f0 b0 : ℕ) (hm' : m' = 2 * f0 + 64 * b0)
    (hm'le : m' ≤ 2 ^ 37) (hm'pos : 0 < m') (hf0 : f0 = 0 ∨ 4095 * m' ≤ f0 * 2 ^ 37)
    (a up down : ℕ) (ha : a = 2 ^ s * m') (hup : up = 2 * (2 ^ s * f0))
    (hdown : down = 2 ^ s * b0) (hbig : 2 ^ 64 < a) : Nonempty (NodeGeom a up down) := by
  have h37 : 2 ^ 37 ≤ 2 ^ 60 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
  obtain ⟨r, hr1, hr2⟩ := exists_pow_scale m' hm'pos (le_trans hm'le h37)
  have hrs : r < s := by
    by_contra hc
    have h1 : 2 ^ s ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 2 ^ s * m' ≤ 2 ^ r * m' := Nat.mul_le_mul_right _ h1
    have h3 : (2 : ℕ) ^ 60 < 2 ^ 64 := by norm_num
    omega
  have hpow : 2 ^ s = 2 ^ r * 2 ^ (s - r) := by
    rw [← pow_add]; congr 1; omega
  have hmn : a = 2 ^ r * m' * 2 ^ (s - r) := by rw [ha, hpow]; ring
  have hn : 16 ≤ 2 ^ (s - r) := by
    by_contra hc
    push_neg at hc
    have h1 : 2 ^ r * m' * 2 ^ (s - r) ≤ 2 ^ 60 * 15 :=
      Nat.mul_le_mul hr2 (by omega)
    have h3 : (2 : ℕ) ^ 60 * 15 < 2 ^ 64 := by norm_num
    omega
  refine ⟨⟨2 ^ r * m', 2 ^ (s - r), 2 ^ r * f0, 2 ^ r * b0, ?_, hmn, ?_, ?_, hr1, hr2, hn, ?_⟩⟩
  · exact scaled_m_eq f0 b0 64 r m' hm'
  · rw [hup, hpow]; ring
  · rw [hdown, hpow]; ring
  · rcases hf0 with h | h
    · left; rw [h]; simp
    · right
      obtain ⟨h1, h2⟩ := scaled_fringe_big_ratio f0 m' r hm'pos hm'le h hr1
      exact ⟨by omega, h2⟩


/-! ## G2: explicit sizes per node type (§7 schedule, `2 ≤ t < tf7 d`) -/

theorem p64 (n : ℕ) : (64 : ℕ) ^ n = 2 ^ (6 * n) := by
  rw [show (64 : ℕ) = 2 ^ 6 by norm_num, ← pow_mul]

theorem omega7_bounds (d t : ℕ) (ht2 : 2 ≤ t) : t + 2 ≤ 3 * omega7 d t ∧ 3 * omega7 d t ≤ t + 6 := by
  rw [omega7_of_ge_two d t ht2]
  unfold ceilParity omegaStarLower
  split_ifs <;> omega

theorem nodeGeom_top {a up down : ℕ} (g : ℕ) (ha : a = 64 ^ (g + 1)) (hu : up = 0)
    (hdn : down = 64 ^ g) (hbig : 2 ^ 64 < a) : Nonempty (NodeGeom a up down) := by
  refine nodeGeom_of_template (6 * g) 64 0 1 (by norm_num) (by norm_num) (by norm_num)
    (Or.inl rfl) _ _ _ ?_ ?_ ?_ hbig
  · rw [ha, pow_succ, p64]
  · rw [hu]; simp
  · rw [hdn]; simp [p64]

theorem nodeGeom_rise {a up down : ℕ} (f : ℕ) (ha : a = 64 ^ (6 + f))
    (hu : up = 2 * (32 * 64 ^ (1 + f))) (hdn : down = 16777215 * 64 ^ (1 + f))
    (hbig : 2 ^ 64 < a) : Nonempty (NodeGeom a up down) := by
  refine nodeGeom_of_template (6 * f + 6) (2 ^ 30) 32 (2 ^ 24 - 1) (by norm_num) (by norm_num)
    (by norm_num) (Or.inr (by norm_num)) _ _ _ ?_ ?_ ?_ hbig
  · rw [ha, p64, show 6 * (6 + f) = 6 * f + 6 + 30 by ring, pow_add]
  · rw [hu, p64, show 6 * (1 + f) = 6 * f + 6 by ring]; ring
  · rw [hdn, p64, show 6 * (1 + f) = 6 * f + 6 by ring]; norm_num; ring

/-- Descending bottom node. -/
theorem val_bot_desc (d : ℕ) (hd : 7 ≤ d) (t : ℕ) (ht2 : 2 ≤ t) (ht : t < tf7 d) (i : ℕ)
    (hact : t ≤ tf7 d ∧ alpha7 d t ≤ i ∧ i ≤ omega7 d t ∧ i % 2 = t % 2)
    (hα : i ≠ alpha7 d t) (hω : i = omega7 d t) (hs : omega7 d t < omega7 d (t + 1)) :
    ∃ g h : ℕ, h ≤ g ∧ d = i + (g + 1) ∧ d + 2 * i = t + 9 + h ∧
      flowA7 d hd i t = 64 ^ (g + 1) - 64 ^ (h + 1) ∧
      flowUp7 d hd i t = 2 * (4095 * 32 * 64 ^ h) ∧
      flowDown7 d hd i t = 64 ^ g - 64 ^ (h + 2) := by
  obtain ⟨g, h, hgh, hdg, hh, hv⟩ := alloc_bot_val d hd t ht2 ht i hact hα hω
  refine ⟨g, h, hgh, hdg, hh, ?_, ?_, ?_⟩
  · have hc := cast_flowA7 d hd i t ht2 ht.le
    rw [hv] at hc
    have h2 : ((flowA7 d hd i t : ℕ) : ℚ) =
        (((64 ^ (g + 1) - 64 ^ (h + 1) : ℕ)) : ℚ) := by
      rw [hc, Nat.cast_sub (Nat.pow_le_pow_right (by norm_num) (by omega))]; push_cast; rfl
    exact_mod_cast h2
  · have hlt := alpha7_lt_omega7 d hd t ht2 ht
    have hp1 := alpha7_parity d t
    have hne := exp_nontop d t i hd ht2 ht (by omega) hact.2.2.2
    have hc := capacity_params7 d i t (7 + h) (by omega)
    have h1 := (cast_flowUp7 d hd i t ht2 ht).1
    rw [flowUp_mid params7 d (levelSchedule7 d hd) hact hα (fun _ => hs), hc,
      capacityRatio_params7] at h1
    have h2 : ((flowUp7 d hd i t : ℕ) : ℚ) = ((2 * (4095 * 32 * 64 ^ h) : ℕ) : ℚ) := by
      rw [h1]; simp only [params7]; push_cast; ring
    exact_mod_cast h2
  · have hlt := alpha7_lt_omega7 d hd t ht2 ht
    have hp1 := alpha7_parity d t
    have hp2 := alpha7_parity d (t + 1)
    have hst := alpha7_step d t hd ht
    have hq1 := omega7_parity d t
    have hq2 := omega7_parity d (t + 1)
    have hqt := omega7_step d t hd ht
    have hact1 : t + 1 ≤ tf7 d ∧ alpha7 d (t + 1) ≤ omega7 d t + 1 ∧
        omega7 d t + 1 ≤ omega7 d (t + 1) ∧ (omega7 d t + 1) % 2 = (t + 1) % 2 := by
      refine ⟨by omega, by omega, by omega, by omega⟩
    have hd1 : ((flowDown7 d hd i t : ℕ) : ℚ) =
        allocation params7 d (levelSchedule7 d hd) (omega7 d t + 1) (t + 1) := by
      rw [cast_flowDown7 d hd i t ht2 ht]
      exact flowDown_bot_desc params7 d (levelSchedule7 d hd) hact hα hω hs
    have hal := alloc_bot params7 d (levelSchedule7 d hd) hact1 (by
      show omega7 d t + 1 ≠ alpha7 d (t + 1); omega) (by
      show omega7 d t + 1 = omega7 d (t + 1); omega)
    have hc := capacity_params7 d (omega7 d t + 1) (t + 1) (8 + h) (by omega)
    rw [hal] at hd1
    change _ = (((64 ^ d : ℕ) : ℚ)) / ((params7.br : ℕ) : ℚ) ^ (omega7 d t + 1) -
      capacity params7 d (omega7 d t + 1) (t + 1) / capacityRatio params7 at hd1
    rw [hc, capacityRatio_params7] at hd1
    have key : ∀ w, d = w + g →
        ((64 ^ d : ℕ) : ℚ) / ((params7.br : ℕ) : ℚ) ^ w = (64 : ℚ) ^ g := by
      intro w hw
      show ((64 ^ d : ℕ) : ℚ) / ((64 : ℕ) : ℚ) ^ w = _
      rw [hw]; push_cast; rw [pow_add]; field_simp
    have e2 := key (omega7 d t + 1) (by omega)
    rw [e2] at hd1
    have hb := omega7_bounds d t ht2
    have hle : 64 ^ (h + 2) ≤ 64 ^ g := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : ((flowDown7 d hd i t : ℕ) : ℚ) = ((64 ^ g - 64 ^ (h + 2) : ℕ) : ℚ) := by
      rw [hd1, Nat.cast_sub hle]
      push_cast
      rw [pow_add, pow_add]; field_simp
    exact_mod_cast h2

/-! ## G2: the node geometry for each node type -/

/-- (T0) the root at `t = 0`. -/
theorem nodeGeom_T0 (d : ℕ) (hd : 7 ≤ d) (hbig : 2 ^ 64 < flowA7 d hd 0 0) :
    Nonempty (NodeGeom (flowA7 d hd 0 0) (flowUp7 d hd 0 0) (flowDown7 d hd 0 0)) := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  exact nodeGeom_top e (by simp [flowA7]) (by simp [flowUp7]) (by simp [flowDown7]) hbig

/-- (T1, `t = 1`) the level-1 node at `t = 1`. -/
theorem nodeGeom_T1_one (d : ℕ) (hd : 7 ≤ d) (hbig : 2 ^ 64 < flowA7 d hd 1 1) :
    Nonempty (NodeGeom (flowA7 d hd 1 1) (flowUp7 d hd 1 1) (flowDown7 d hd 1 1)) := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 7 := ⟨d - 7, by omega⟩
  refine nodeGeom_rise e ?_ ?_ ?_ hbig
  · simp [flowA7, add_comm]
  · simp [flowUp7]; ring
  · simp [flowDown7]; rw [show (64 : ℕ) ^ (e + 5) = 64 ^ (1 + e) * 64 ^ 4 by ring]
    rw [show e + 1 = 1 + e by omega, ← Nat.mul_sub_one]; ring_nf

/-- (T1', `t ≥ 2`) a descending top node: `a = c`, `up = 0`, `down = c/64`. -/
theorem nodeGeom_T1_desc (d : ℕ) (hd : 7 ≤ d) (t : ℕ) (ht2 : 2 ≤ t) (ht : t < tf7 d) (i : ℕ)
    (hact : t ≤ tf7 d ∧ alpha7 d t ≤ i ∧ i ≤ omega7 d t ∧ i % 2 = t % 2)
    (hα : i = alpha7 d t) (hs : alpha7 d t < alpha7 d (t + 1))
    (hbig : 2 ^ 64 < flowA7 d hd i t) :
    Nonempty (NodeGeom (flowA7 d hd i t) (flowUp7 d hd i t) (flowDown7 d hd i t)) := by
  have he := exp_top d t hd ht2 ht.le
  obtain ⟨g, hg⟩ : ∃ g, d + 2 * i = t + 3 + g := ⟨d + 2 * i - (t + 3), by omega⟩
  have ha : flowA7 d hd i t = 64 ^ (g + 1) := by
    have h := cast_flowA7 d hd i t ht2 ht.le
    rw [alloc_top params7 d (levelSchedule7 d hd) hact hα,
      capacity_params7 d i t (g + 1) (by omega)] at h
    exact_mod_cast h
  have hu : flowUp7 d hd i t = 0 := by
    have h := (cast_flowUp7 d hd i t ht2 ht).1
    rw [flowUp_top_desc params7 d (levelSchedule7 d hd) hact hα hs] at h
    exact_mod_cast h
  have hdn : flowDown7 d hd i t = 64 ^ g := by
    have h := cast_flowDown7 d hd i t ht2 ht
    rw [flowDown_top_desc params7 d (levelSchedule7 d hd) hact hα hs,
      capacity_params7 d i t (g + 1) (by omega)] at h
    exact Nat.cast_injective (R := ℚ) (h.trans (by simp only [params7]; push_cast; ring))
  refine nodeGeom_of_template (6 * g) 64 0 1 (by norm_num) (by norm_num) (by norm_num)
    (Or.inl rfl) _ _ _ ?_ ?_ ?_ hbig
  · rw [ha, pow_succ, p64]
  · rw [hu]; simp
  · rw [hdn]; simp [p64]

/-- (T1, `t ≥ 2`) a rising top node: `a = c`, `up/2 = c/2^25`, `down = c(2^24-1)/2^30`. -/
theorem nodeGeom_T1_rise (d : ℕ) (hd : 7 ≤ d) (t : ℕ) (ht2 : 2 ≤ t) (ht : t < tf7 d) (i : ℕ)
    (hact : t ≤ tf7 d ∧ alpha7 d t ≤ i ∧ i ≤ omega7 d t ∧ i % 2 = t % 2)
    (hα : i = alpha7 d t) (hs : alpha7 d (t + 1) < alpha7 d t)
    (hbig : 2 ^ 64 < flowA7 d hd i t) :
    Nonempty (NodeGeom (flowA7 d hd i t) (flowUp7 d hd i t) (flowDown7 d hd i t)) := by
  have he := exp_top_rise d t hd ht2 ht hs
  rw [← hα] at he
  obtain ⟨f, hf⟩ : ∃ f, d + 2 * i = t + 8 + f := ⟨d + 2 * i - (t + 8), by omega⟩
  have hns : ¬ alpha7 d t < alpha7 d (t + 1) := by omega
  have hc := capacity_params7 d i t (6 + f) (by omega)
  have hωi : i ≠ omega7 d t := by
    have := alpha7_lt_omega7 d hd t ht2 ht
    omega
  have ha : flowA7 d hd i t = 64 ^ (6 + f) := by
    have h := cast_flowA7 d hd i t ht2 ht.le
    rw [alloc_top params7 d (levelSchedule7 d hd) hact hα, hc] at h
    exact_mod_cast h
  have hu : flowUp7 d hd i t = 2 * (32 * 64 ^ (1 + f)) := by
    have h := (cast_flowUp7 d hd i t ht2 ht).1
    rw [flowUp_top_rise params7 d (levelSchedule7 d hd) hact hα hns, hc] at h
    exact Nat.cast_injective (R := ℚ) (h.trans (by simp only [params7]; push_cast; ring))
  have hdn : flowDown7 d hd i t = 16777215 * 64 ^ (1 + f) := by
    have h := cast_flowDown7 d hd i t ht2 ht
    rw [flowDown_mid params7 d (levelSchedule7 d hd) hact (fun _ => hns) hωi, hc] at h
    exact Nat.cast_injective (R := ℚ) (h.trans (by simp only [params7]; push_cast; ring))
  refine nodeGeom_of_template (6 * f + 6) (2 ^ 30) 32 (2 ^ 24 - 1) (by norm_num) (by norm_num)
    (by norm_num) (Or.inr (by norm_num)) _ _ _ ?_ ?_ ?_ hbig
  · rw [ha, p64, show 6 * (6 + f) = 6 * f + 6 + 30 by ring, pow_add]
  · rw [hu, p64, show 6 * (1 + f) = 6 * f + 6 by ring]; ring
  · rw [hdn, p64, show 6 * (1 + f) = 6 * f + 6 by ring]; norm_num; ring

/-- (T2) an interior node: `a = c - c/2^36`, `up/2 = 4095 c/2^37`, `down = c(2^24-1)/2^30`. -/
theorem nodeGeom_T2 (d : ℕ) (hd : 7 ≤ d) (t : ℕ) (ht2 : 2 ≤ t) (ht : t < tf7 d) (i : ℕ)
    (hact : t ≤ tf7 d ∧ alpha7 d t ≤ i ∧ i ≤ omega7 d t ∧ i % 2 = t % 2)
    (hα : i ≠ alpha7 d t) (hω : i ≠ omega7 d t)
    (hbig : 2 ^ 64 < flowA7 d hd i t) :
    Nonempty (NodeGeom (flowA7 d hd i t) (flowUp7 d hd i t) (flowDown7 d hd i t)) := by
  have hlt := alpha7_lt_omega7 d hd t ht2 ht
  have hp1 := alpha7_parity d t
  have hne := exp_nontop d t i hd ht2 ht (by omega) hact.2.2.2
  obtain ⟨g, hg⟩ : ∃ g, d + 2 * i = t + 9 + g := ⟨d + 2 * i - (t + 9), by omega⟩
  have hc := capacity_params7 d i t (7 + g) (by omega)
  have hle : 64 ^ (1 + g) ≤ 64 ^ (7 + g) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have ha : flowA7 d hd i t = 64 ^ (7 + g) - 64 ^ (1 + g) := by
    have h := cast_flowA7 d hd i t ht2 ht.le
    rw [alloc_mid params7 d (levelSchedule7 d hd) hact hα hω, hc, capacityRatio_params7] at h
    refine Nat.cast_injective (R := ℚ) (h.trans ?_)
    rw [Nat.cast_sub hle]; push_cast
    rw [pow_add, pow_add]; field_simp
  have hu : flowUp7 d hd i t = 2 * (4095 * 32 * 64 ^ g) := by
    have h := (cast_flowUp7 d hd i t ht2 ht).1
    rw [flowUp_mid params7 d (levelSchedule7 d hd) hact hα (fun h => absurd h hω), hc,
      capacityRatio_params7] at h
    exact Nat.cast_injective (R := ℚ) (h.trans (by simp only [params7]; push_cast; ring))
  have hdn : flowDown7 d hd i t = 16777215 * 64 ^ (2 + g) := by
    have h := cast_flowDown7 d hd i t ht2 ht
    rw [flowDown_mid params7 d (levelSchedule7 d hd) hact (fun h => absurd h hα) hω, hc] at h
    exact Nat.cast_injective (R := ℚ) (h.trans (by simp only [params7]; push_cast; ring))
  refine nodeGeom_of_template (6 * g + 5) 137438953470 4095 2147483520 (by norm_num)
    (by norm_num) (by norm_num) (Or.inr (by norm_num)) _ _ _ ?_ ?_ ?_ hbig
  · rw [ha]
    apply Nat.sub_eq_of_eq_add
    simp only [p64]
    ring
  · rw [hu]; simp only [p64]; ring
  · rw [hdn]; simp only [p64]; ring

/-- (T3) a descending bottom node: `up` as interior, `a = 64^(d-l) - c/2^36`,
`down = 64^(d-l-1) - 64^(e-5)`; `down > 0` is needed (it fails exactly when `down = 0`). -/
theorem nodeGeom_T3 (d : ℕ) (hd : 7 ≤ d) (t : ℕ) (ht2 : 2 ≤ t) (ht : t < tf7 d) (i : ℕ)
    (hact : t ≤ tf7 d ∧ alpha7 d t ≤ i ∧ i ≤ omega7 d t ∧ i % 2 = t % 2)
    (hα : i ≠ alpha7 d t) (hω : i = omega7 d t) (hs : omega7 d t < omega7 d (t + 1))
    (hdown : 0 < flowDown7 d hd i t) (hbig : 2 ^ 64 < flowA7 d hd i t) :
    Nonempty (NodeGeom (flowA7 d hd i t) (flowUp7 d hd i t) (flowDown7 d hd i t)) := by
  obtain ⟨g, h, hgh, hdg, hh, ha, hu, hdn⟩ := val_bot_desc d hd t ht2 ht i hact hα hω hs
  have hb := omega7_bounds d t ht2
  have hj4 : g ≤ h + 6 := by omega
  have hj1 : h + 3 ≤ g := by
    by_contra hc
    have : 64 ^ g ≤ 64 ^ (h + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [hdn] at hdown
    omega
  obtain ⟨j, hj⟩ : ∃ j, g = h + 2 + j := ⟨g - (h + 2), by omega⟩
  have hjle : j ≤ 4 := by omega
  have hP : 1 ≤ 64 ^ j := Nat.one_le_pow _ _ (by norm_num)
  obtain ⟨R, hR⟩ : ∃ R, 64 ^ j = R + 1 := ⟨64 ^ j - 1, by omega⟩
  have hP4 : 64 ^ j ≤ 16777216 :=
    calc 64 ^ j ≤ 64 ^ 4 := Nat.pow_le_pow_right (by norm_num) hjle
      _ = 16777216 := by norm_num
  have hRle : R ≤ 16777215 := by omega
  have hm'le : 8192 * R + 8190 ≤ 2 ^ 37 := by
    have : (2 : ℕ) ^ 37 = 137438953472 := by norm_num
    omega
  refine nodeGeom_of_template (6 * h + 5) (8192 * R + 8190) 4095 (128 * R) (by omega) hm'le
    (by omega) (Or.inr (by
      have : 4095 * (8192 * R + 8190) ≤ 4095 * 2 ^ 37 := Nat.mul_le_mul_left _ hm'le
      omega)) _ _ _ ?_ ?_ ?_ hbig
  · rw [ha]
    apply Nat.sub_eq_of_eq_add
    have e1 : 64 ^ (g + 1) = 64 ^ h * 64 ^ 3 * 64 ^ j := by
      rw [hj]; ring
    rw [e1, hR, p64 (h + 1), p64 h, show 6 * h + 5 = 6 * h + 5 from rfl]
    rw [show (2 : ℕ) ^ (6 * h + 5) = 2 ^ (6 * h) * 32 by rw [pow_add]; norm_num]
    norm_num
    ring
  · rw [hu]; simp only [p64]; ring
  · rw [hdn]
    apply Nat.sub_eq_of_eq_add
    have e1 : 64 ^ g = 64 ^ h * 64 ^ 2 * 64 ^ j := by
      rw [hj]; ring
    rw [e1, hR, p64 (h + 2), p64 h]
    rw [show (2 : ℕ) ^ (6 * h + 5) = 2 ^ (6 * h) * 32 by rw [pow_add]; norm_num]
    norm_num
    ring

/-- **B5c geometry (A10).** Every node of the §7 schedule that sends wires down and holds more
than `2^64` wires carries a separator geometry. -/
theorem nodeGeom_exists (d : ℕ) (hd : 7 ≤ d) (l t : ℕ) (hdown : 0 < flowDown7 d hd l t)
    (hbig : 2 ^ 64 < flowA7 d hd l t) (ht : t < tf7 d) :
    Nonempty (NodeGeom (flowA7 d hd l t) (flowUp7 d hd l t) (flowDown7 d hd l t)) := by
  rcases Nat.lt_or_ge t 2 with h2 | h2
  · obtain rfl | rfl : t = 0 ∨ t = 1 := by omega
    · by_cases hl : l = 0
      · subst hl; exact nodeGeom_T0 d hd hbig
      · exfalso; simp [flowA7, hl] at hbig
    · by_cases hl : l = 1
      · subst hl; exact nodeGeom_T1_one d hd hbig
      · exfalso; simp [flowA7, hl] at hbig
  · by_cases hact : t ≤ tf7 d ∧ alpha7 d t ≤ l ∧ l ≤ omega7 d t ∧ l % 2 = t % 2
    swap
    · exfalso
      have h := cast_flowA7 d hd l t h2 ht.le
      rw [allocation_inactive _ _ _ _ _ hact] at h
      have : flowA7 d hd l t = 0 := by exact_mod_cast h
      omega
    have hlt := alpha7_lt_omega7 d hd t h2 ht
    have hp1 := alpha7_parity d t
    have hp2 := alpha7_parity d (t + 1)
    have hst := alpha7_step d t hd ht
    by_cases hα : l = alpha7 d t
    · by_cases hs : alpha7 d t < alpha7 d (t + 1)
      · exact nodeGeom_T1_desc d hd t h2 ht l hact hα hs hbig
      · exact nodeGeom_T1_rise d hd t h2 ht l hact hα (by omega) hbig
    · by_cases hω : l = omega7 d t
      · by_cases hs : omega7 d t < omega7 d (t + 1)
        · exact nodeGeom_T3 d hd t h2 ht l hact hα hω hs hdown hbig
        · exfalso
          have h := cast_flowDown7 d hd l t h2 ht
          rw [flowDown_bot_rise params7 d (levelSchedule7 d hd) hact hα hω hs] at h
          have : flowDown7 d hd l t = 0 := by exact_mod_cast h
          omega
      · exact nodeGeom_T2 d hd t h2 ht l hact hα hω hbig

end Chvatal
