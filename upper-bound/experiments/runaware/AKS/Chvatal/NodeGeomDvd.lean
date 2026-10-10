module

public import AKS.Chvatal.NodeGeom
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.IntervalCases

@[expose] public section

/-! # 2-adic divisibility of the node geometry and of the sources (run-aware first column sort)

* `NodeShape.dvd_geom`: for *every* separator geometry of a sending node, `2^22 ∣ f`, `2^29 ∣ b`.
* `NodeShape.geomD` / `nodeGeomD_exists`: a normalised geometry (the odd part of `n` chosen as
  `195` or `63`) with `2^29 ∣ f` and `2^29 ∣ b`.
* `parent_down_dvd`, `child_up_half_dvd`: the sources feeding a big node send multiples of
  `2^30` (`down`) and `2^47` (`up / 2`). -/

namespace Chvatal


/-- 2-adic divisibility from a product with a bounded cofactor. -/
theorem key_dvd (X N S c K : ℕ) (hc : Odd c) (hX : X * N = 2 ^ S * c) (hN : 0 < N)
    (hK : N * 2 ^ 58 < 2 ^ K) : 2 ^ (S + 59 - K) ∣ X := by
  have hK58 : 58 < K := by
    have h1 : 2 ^ 58 ≤ N * 2 ^ 58 := Nat.le_mul_of_pos_left _ hN
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).1 (lt_of_le_of_lt h1 hK)
  have hNK : N < 2 ^ (K - 58) := by
    have : 2 ^ K = 2 ^ (K - 58) * 2 ^ 58 := by rw [← pow_add]; congr 1; omega
    rw [this] at hK
    exact Nat.lt_of_mul_lt_mul_right hK
  obtain ⟨j, n', hn', hNe⟩ := Nat.exists_eq_two_pow_mul_odd hN.ne'
  have hjK : j < K - 58 := by
    have : 2 ^ j ≤ N := by rw [hNe]; exact Nat.le_mul_of_pos_right _ hn'.pos
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).1 (lt_of_le_of_lt this hNK)
  have hcop2c : Nat.Coprime (2 ^ j) c := Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hc)
  have hjS : j ≤ S := by
    have h1 : 2 ^ j ∣ 2 ^ S * c := ⟨X * n', by rw [← hX, hNe]; ring⟩
    have h2 : 2 ^ j ∣ 2 ^ S := hcop2c.dvd_of_dvd_mul_right h1
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 h2
  have hX2 : X * n' = 2 ^ (S - j) * c := by
    have h1 : 2 ^ j * (X * n') = 2 ^ j * (2 ^ (S - j) * c) := by
      calc 2 ^ j * (X * n') = X * (2 ^ j * n') := by ring
        _ = 2 ^ S * c := by rw [← hNe, hX]
        _ = 2 ^ j * (2 ^ (S - j) * c) := by rw [← mul_assoc, ← pow_add]; congr 2; omega
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h1
  have hcop : Nat.Coprime (2 ^ (S - j)) n' := Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hn')
  have h3 : 2 ^ (S - j) ∣ X * n' := ⟨c, hX2⟩
  have h4 : 2 ^ (S - j) ∣ X := hcop.dvd_of_dvd_mul_right h3
  exact (pow_dvd_pow 2 (by omega)).trans h4

theorem odd_pow64_sub_one (j : ℕ) (hj : 1 ≤ j) : Odd (64 ^ j - 1) := by
  obtain ⟨q, hq⟩ : Even (64 ^ j) := (Nat.even_pow.2 ⟨by decide, by omega⟩)
  have : 1 ≤ 64 ^ j := Nat.one_le_pow _ _ (by norm_num)
  exact ⟨q - 1, by omega⟩

/-- **Divisibility for every geometry.** For any `m × N` geometry of a sending node (`NodeShape`),
`f` is a multiple of `2^22` and `b` of `2^29`. -/
theorem NodeShape.dvd_geom {d t i a u n : ℕ} (h : NodeShape d t i a u n) (hn : 0 < n)
    {m N f b : ℕ} (hN : 0 < N) (ha : a = m * N) (hup : u = 2 * f * N) (hdn : n = b * N)
    (hm1 : 2 ^ 58 < m) : 2 ^ 22 ∣ f ∧ 2 ^ 29 ∣ b := by
  have hwin : N * 2 ^ 58 < a := by rw [ha]; nlinarith
  have hf2 : u = 2 * (f * N) := by rw [hup]; ring
  cases h with
  | off => omega
  | botRise => omega
  | topDesc g =>
    have hf : f = 0 := by
      have : f * N = 0 := by omega
      rcases Nat.mul_eq_zero.1 this with h | h
      · exact h
      · omega
    refine ⟨by rw [hf]; exact dvd_zero _, ?_⟩
    have hb : b * N = 2 ^ (6 * g) * 1 := by rw [← hdn, p64]; ring
    have hK : N * 2 ^ 58 < 2 ^ (6 * g + 6) := by
      rw [show 2 ^ (6 * g + 6) = 64 ^ (g + 1) by rw [p64]; congr 1]; exact hwin
    exact (pow_dvd_pow 2 (by omega)).trans (key_dvd b N _ 1 _ odd_one hb hN hK)
  | topRise g =>
    have hK : N * 2 ^ 58 < 2 ^ (6 * g + 36) := by
      rw [show 2 ^ (6 * g + 36) = 64 ^ (6 + g) by rw [p64]; congr 1; ring]; exact hwin
    have hf : f * N = 2 ^ (6 * g + 11) * 1 := by
      have e : f * N = 32 * 64 ^ (1 + g) := by omega
      rw [e, p64, show 2 ^ (6 * g + 11) = 2 ^ 5 * 2 ^ (6 * (1 + g)) by
        rw [← pow_add]; congr 1; ring]; ring
    have hb : b * N = 2 ^ (6 * g + 6) * 16777215 := by
      rw [← hdn, p64, show 2 ^ (6 * g + 6) = 2 ^ (6 * (1 + g)) by congr 1; ring]; ring
    exact ⟨(pow_dvd_pow 2 (by omega)).trans (key_dvd f N _ 1 _ odd_one hf hN hK),
      (pow_dvd_pow 2 (by omega)).trans (key_dvd b N _ _ _ (by decide) hb hN hK)⟩
  | mid g =>
    have hK : N * 2 ^ 58 < 2 ^ (6 * g + 42) := by
      have : 64 ^ (7 + g) - 64 ^ (1 + g) < 2 ^ (6 * g + 42) := by
        have h1 : 0 < 64 ^ (1 + g) := by positivity
        rw [show 2 ^ (6 * g + 42) = 64 ^ (7 + g) by rw [p64]; congr 1; ring]; omega
      exact lt_trans hwin this
    have hf : f * N = 2 ^ (6 * g + 5) * 4095 := by
      have e : f * N = 4095 * 32 * 64 ^ g := by omega
      rw [e, p64, show 2 ^ (6 * g + 5) = 2 ^ 5 * 2 ^ (6 * g) by ring]; ring
    have hb : b * N = 2 ^ (6 * g + 12) * 16777215 := by
      rw [← hdn, p64, show 2 ^ (6 * g + 12) = 2 ^ (6 * (2 + g)) by congr 1; ring]; ring
    exact ⟨(pow_dvd_pow 2 (by omega)).trans (key_dvd f N _ _ _ (by decide) hf hN hK),
      (pow_dvd_pow 2 (by omega)).trans (key_dvd b N _ _ _ (by decide) hb hN hK)⟩
  | botDesc g h' hgh hg =>
    have hK : N * 2 ^ 58 < 2 ^ (6 * g + 6) := by
      have : 64 ^ (g + 1) - 64 ^ (h' + 1) < 2 ^ (6 * g + 6) := by
        have h1 : 0 < 64 ^ (h' + 1) := by positivity
        rw [show 2 ^ (6 * g + 6) = 64 ^ (g + 1) by rw [p64]; congr 1]; omega
      exact lt_trans hwin this
    have hf : f * N = 2 ^ (6 * h' + 5) * 4095 := by
      have e : f * N = 4095 * 32 * 64 ^ h' := by omega
      rw [e, p64, show 2 ^ (6 * h' + 5) = 2 ^ 5 * 2 ^ (6 * h') by ring]; ring
    have hgt : h' + 2 < g := by
      by_contra hc
      have : g = h' + 2 := by omega
      subst this
      simp at hn
    obtain ⟨j, hj⟩ : ∃ j, g = h' + 2 + j := ⟨g - (h' + 2), by omega⟩
    have hb : b * N = 2 ^ (6 * h' + 12) * (64 ^ j - 1) := by
      rw [← hdn, show 64 ^ g = 64 ^ (h' + 2) * 64 ^ j by rw [hj]; ring, p64 (h' + 2),
        show 2 ^ (6 * h' + 12) = 2 ^ (6 * (h' + 2)) by congr 1, Nat.mul_sub_one]
    exact ⟨(pow_dvd_pow 2 (by omega)).trans (key_dvd f N _ _ _ (by decide) hf hN hK),
      (pow_dvd_pow 2 (by omega)).trans (key_dvd b N _ _ _ (odd_pow64_sub_one j (by omega)) hb hN hK)⟩



/-- A separator geometry whose fringe `f` and block `b` are multiples of `2^29`. -/
structure NodeGeomD (a up down : ℕ) extends NodeGeom a up down where
  dvf : 2 ^ 29 ∣ f
  dvb : 2 ^ 29 ∣ b

/-- Template scaling with a common divisor `o` kept in `n` (so that the scale `2^r`, and
hence the 2-adic valuation of `f`, `b`, is at least `29` because `m'' ≤ 2^30`). -/
theorem nodeGeomD_of_template (s o m'' f0 b0 : ℕ) (ho : 0 < o) (hm'' : m'' = 2 * f0 + 64 * b0)
    (hle : m'' ≤ 2 ^ 30) (hpos : 0 < m'') (hf0 : f0 = 0 ∨ 4095 * m'' ≤ f0 * 2 ^ 37)
    (hs : 2 ^ 58 < 2 ^ s * m'')
    (a up down : ℕ) (ha : a = 2 ^ s * (o * m'')) (hup : up = 2 * (2 ^ s * (o * f0)))
    (hdown : down = 2 ^ s * (o * b0)) (hbig : 2 ^ 63 < a) : Nonempty (NodeGeomD a up down) := by
  have h30 : 2 ^ 30 ≤ 2 ^ 59 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have h37 : m'' ≤ 2 ^ 37 := le_trans hle (Nat.pow_le_pow_right (by norm_num) (by norm_num))
  obtain ⟨r, hr1, hr2⟩ := exists_pow_scale m'' hpos (le_trans hle h30)
  have hr29 : 29 ≤ r := by
    by_contra hc
    have h1 : 2 ^ r ≤ 2 ^ 28 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 2 ^ r * m'' ≤ 2 ^ 28 * 2 ^ 30 := Nat.mul_le_mul h1 hle
    have h3 : (2 : ℕ) ^ 28 * 2 ^ 30 = 2 ^ 58 := by norm_num
    omega
  have hrs : r ≤ s := by
    by_contra hc
    have h1 : 2 ^ (s + 1) ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 2 ^ (s + 1) * m'' ≤ 2 ^ r * m'' := Nat.mul_le_mul_right _ h1
    have h3 : 2 ^ (s + 1) * m'' = 2 * (2 ^ s * m'') := by ring
    have h4 : (2 : ℕ) ^ 59 = 2 * 2 ^ 58 := by norm_num
    omega
  have hpow : 2 ^ s = 2 ^ r * 2 ^ (s - r) := by
    rw [← pow_add]; congr 1; omega
  have hmn : a = 2 ^ r * m'' * (o * 2 ^ (s - r)) := by rw [ha, hpow]; ring
  have hn : 16 ≤ o * 2 ^ (s - r) := by
    by_contra hc
    push_neg at hc
    have h1 : 2 ^ r * m'' * (o * 2 ^ (s - r)) ≤ 2 ^ 59 * 15 :=
      Nat.mul_le_mul hr2 (by omega)
    have h3 : (2 : ℕ) ^ 59 * 15 < 2 ^ 63 := by norm_num
    omega
  have hd29 : (2 : ℕ) ^ 29 ∣ 2 ^ r := pow_dvd_pow 2 hr29
  refine ⟨⟨⟨2 ^ r * m'', o * 2 ^ (s - r), 2 ^ r * f0, 2 ^ r * b0, ?_, hmn, ?_, ?_, hr1, hr2, hn, ?_⟩,
    hd29.mul_right _, hd29.mul_right _⟩⟩
  · exact scaled_m_eq f0 b0 64 r m'' hm''
  · rw [hup, hpow]; ring
  · rw [hdown, hpow]; ring
  · rcases hf0 with h | h
    · left; rw [h]; simp
    · right
      obtain ⟨h1, h2⟩ := scaled_fringe_big_ratio f0 m'' r hpos h37 h hr1
      exact ⟨by omega, h2⟩

theorem geomD_botDesc (g h j o m'' f0 b0 : ℕ) (hj : g = h + 2 + j) (hj1 : 1 ≤ j) (ho : 0 < o)
    (hmm : 8192 * (64 ^ j - 1) + 8190 = o * m'') (hff : 4095 = o * f0)
    (hbb : 128 * (64 ^ j - 1) = o * b0) (hm'' : m'' = 2 * f0 + 64 * b0) (hle : m'' ≤ 2 ^ 30)
    (hpos : 0 < m'') (hrat : 4095 * m'' ≤ f0 * 2 ^ 37) (hs : 2 ^ 58 < 2 ^ (6 * h + 5) * m'')
    (a up down : ℕ) (ha : a = 64 ^ (g + 1) - 64 ^ (h + 1))
    (hup : up = 2 * (4095 * 32 * 64 ^ h)) (hdown : down = 64 ^ g - 64 ^ (h + 2))
    (hbig : 2 ^ 63 < a) : Nonempty (NodeGeomD a up down) := by
  have hP : 1 ≤ 64 ^ j := Nat.one_le_pow _ _ (by norm_num)
  obtain ⟨R, hR⟩ : ∃ R, 64 ^ j = R + 1 := ⟨64 ^ j - 1, by omega⟩
  rw [hR, Nat.add_sub_cancel] at hmm hbb
  refine nodeGeomD_of_template (6 * h + 5) o m'' f0 b0 ho hm'' hle hpos (Or.inr hrat) hs a up down
    ?_ ?_ ?_ hbig
  · rw [ha, ← hmm]
    apply Nat.sub_eq_of_eq_add
    rw [show 64 ^ (g + 1) = 64 ^ h * 64 ^ 3 * 64 ^ j by rw [hj]; ring, hR, p64 (h + 1), p64 h,
      show (2 : ℕ) ^ (6 * h + 5) = 2 ^ (6 * h) * 32 by rw [pow_add]; norm_num]
    norm_num; ring
  · rw [hup, ← hff]; simp only [p64]
    rw [pow_add]; norm_num; ring
  · rw [hdown, ← hbb]
    apply Nat.sub_eq_of_eq_add
    rw [show 64 ^ g = 64 ^ h * 64 ^ 2 * 64 ^ j by rw [hj]; ring, hR, p64 (h + 2), p64 h,
      show (2 : ℕ) ^ (6 * h + 5) = 2 ^ (6 * h) * 32 by rw [pow_add]; norm_num]
    norm_num; ring

/-- Every sending node with more than `2^63` wires has a separator geometry with `2^29 ∣ f, b`. -/
theorem NodeShape.geomD {d t i a u n : ℕ} (h : NodeShape d t i a u n) (hn : 0 < n)
    (hbig : 2 ^ 63 < a) : Nonempty (NodeGeomD a u n) := by
  cases h with
  | off => omega
  | botRise => omega
  | topDesc g =>
    refine nodeGeomD_of_template (6 * g) 1 64 0 1 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (Or.inl rfl) ?_ _ _ _ ?_ ?_ ?_ hbig
    · have : (2 : ℕ) ^ 63 < 2 ^ (6 * g) * 64 := by
        have e : (64 : ℕ) ^ (g + 1) = 2 ^ (6 * g) * 64 := by rw [p64]; ring
        rw [← e]; exact hbig
      omega
    · rw [p64]; ring
    · simp
    · simp [p64]
  | topRise g =>
    refine nodeGeomD_of_template (6 * g + 6) 1 (2 ^ 30) 32 (2 ^ 24 - 1) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (Or.inr (by norm_num)) ?_ _ _ _ ?_ ?_ ?_ hbig
    · have e : (64 : ℕ) ^ (6 + g) = 2 ^ (6 * g + 6) * 2 ^ 30 := by
        rw [p64, ← pow_add]; congr 1; ring
      rw [e] at hbig
      omega
    · rw [p64, show 6 * (6 + g) = 6 * g + 6 + 30 by ring, pow_add]; ring
    · rw [p64, show 6 * (1 + g) = 6 * g + 6 by ring]; ring
    · rw [p64, show 6 * (1 + g) = 6 * g + 6 by ring]; norm_num; ring
  | mid g =>
    have hg : 4 ≤ g := by
      by_contra hc
      have h1 : 64 ^ (7 + g) ≤ 64 ^ 10 := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2 : (64 : ℕ) ^ 10 < 2 ^ 63 := by norm_num
      have h3 : 64 ^ (7 + g) - 64 ^ (1 + g) ≤ 64 ^ (7 + g) := Nat.sub_le _ _
      omega
    have hs : 2 ^ 58 < 2 ^ (6 * g + 5) * 704815146 := by
      have h1 : 2 ^ 29 ≤ 2 ^ (6 * g + 5) := Nat.pow_le_pow_right (by norm_num) (by omega)
      calc (2 : ℕ) ^ 58 < 2 ^ 29 * 704815146 := by norm_num
        _ ≤ 2 ^ (6 * g + 5) * 704815146 := Nat.mul_le_mul_right _ h1
    refine nodeGeomD_of_template (6 * g + 5) 195 704815146 21 11012736 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (Or.inr (by norm_num)) hs _ _ _ ?_ ?_ ?_ hbig
    · apply Nat.sub_eq_of_eq_add
      simp only [p64]; ring
    · simp only [p64]; ring
    · simp only [p64]; ring
  | botDesc g h' hgh hg =>
    have hg10 : 10 ≤ g := by
      by_contra hc
      have h1 : 64 ^ (g + 1) ≤ 64 ^ 10 := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2 : (64 : ℕ) ^ 10 < 2 ^ 63 := by norm_num
      have h3 : 64 ^ (g + 1) - 64 ^ (h' + 1) ≤ 64 ^ (g + 1) := Nat.sub_le _ _
      omega
    have hj1 : h' + 3 ≤ g := by
      by_contra hc
      have : g = h' + 2 := by omega
      subst this
      simp at hn
    obtain ⟨j, hj⟩ : ∃ j, g = h' + 2 + j := ⟨g - (h' + 2), by omega⟩
    have hj4 : j ≤ 4 := by omega
    have key : ∀ (h0 : ℕ), h0 ≤ h' → ∀ m'' : ℕ, 2 ^ 58 < 2 ^ (6 * h0 + 5) * m'' →
        2 ^ 58 < 2 ^ (6 * h' + 5) * m'' := by
      intro h0 hh m'' hm
      have := Nat.mul_le_mul_right m'' (Nat.pow_le_pow_right (show 0 < 2 by norm_num)
        (show 6 * h0 + 5 ≤ 6 * h' + 5 by omega))
      omega
    interval_cases j
    · omega
    · exact geomD_botDesc g h' 1 63 8322 65 128 hj (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (key 7 (by omega) _ (by norm_num)) _ _ _ rfl rfl rfl hbig
    · exact geomD_botDesc g h' 2 63 532610 65 8320 hj (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (key 6 (by omega) _ (by norm_num)) _ _ _ rfl rfl rfl hbig
    · exact geomD_botDesc g h' 3 63 34087042 65 532608 hj (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (key 5 (by omega) _ (by norm_num)) _ _ _ rfl rfl rfl hbig
    · exact geomD_botDesc g h' 4 195 704815146 21 11012736 hj (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (key 4 (by omega) _ (by norm_num)) _ _ _ rfl rfl rfl hbig


/-- **Normalised geometry for every sending node at stage `t ≥ 1`.** -/
theorem nodeGeomD_exists (d : ℕ) (hd : 7 ≤ d) (l t : ℕ) (hdown : 0 < flowDown7 d hd l t)
    (hbig : 2 ^ 63 < flowA7 d hd l t) (ht : t < tf7 d) (ht1 : 1 ≤ t) :
    Nonempty (NodeGeomD (flowA7 d hd l t) (flowUp7 d hd l t) (flowDown7 d hd l t)) :=
  (node_shape d hd t l ht1 ht).geomD hdown hbig


/-- A sending node at exponent `E = d + 2 i - t` sends blocks `down` that are multiples of
`2^(6E - 42)`. -/
theorem NodeShape.dvd_down {d t i a u n : ℕ} (h : NodeShape d t i a u n) (hn : 0 < n) :
    2 ^ (6 * (d + 2 * i - t) - 42) ∣ n := by
  cases h with
  | off => omega
  | botRise => omega
  | topDesc g e =>
    rw [p64]
    exact pow_dvd_pow 2 (by omega)
  | topRise g e =>
    rw [p64]
    exact Dvd.dvd.mul_left (pow_dvd_pow 2 (by omega)) _
  | mid g e =>
    rw [p64]
    exact Dvd.dvd.mul_left (pow_dvd_pow 2 (by omega)) _
  | botDesc g h' hgh hg e hd =>
    refine Nat.dvd_sub ?_ ?_
    · rw [p64]; exact pow_dvd_pow 2 (by omega)
    · rw [p64]; exact pow_dvd_pow 2 (by omega)

/-- Half of the parent send `u / 2` is a multiple of `2^(6E - 49)`. -/
theorem NodeShape.dvd_up_half {d t i a u n : ℕ} (h : NodeShape d t i a u n) (hn : 0 < n) :
    2 ^ (6 * (d + 2 * i - t) - 49) ∣ u / 2 := by
  cases h with
  | off => omega
  | botRise => omega
  | topDesc g e => simp
  | topRise g e =>
    rw [Nat.mul_div_cancel_left _ (by norm_num), p64]
    exact Dvd.dvd.mul_left (pow_dvd_pow 2 (by omega)) _
  | mid g e =>
    rw [Nat.mul_div_cancel_left _ (by norm_num), p64]
    exact (pow_dvd_pow 2 (by omega : 6 * (d + 2 * i - t) - 49 ≤ 6 * g + 5)).trans
      ⟨4095, by rw [pow_add]; ring⟩
  | botDesc g h' hgh hg e hd =>
    rw [Nat.mul_div_cancel_left _ (by norm_num), p64]
    exact (pow_dvd_pow 2 (by omega : 6 * (d + 2 * i - t) - 49 ≤ 6 * h' + 5)).trans
      ⟨4095, by rw [pow_add]; ring⟩

/-- A sending node with more than `2^63` wires sits at exponent `E ≥ 13`. -/
theorem NodeShape.big_exponent {d t i a u n : ℕ} (h : NodeShape d t i a u n) (hn : 0 < n)
    (hbig : 2 ^ 63 < a) : 13 ≤ d + 2 * i - t := by
  cases h with
  | off => omega
  | botRise => omega
  | topDesc g e =>
    have : 10 ≤ g := by
      by_contra hc
      have h1 : 64 ^ (g + 1) ≤ 64 ^ 10 := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2 : (64 : ℕ) ^ 10 < 2 ^ 63 := by norm_num
      omega
    omega
  | topRise g e =>
    have : 5 ≤ g := by
      by_contra hc
      have h1 : 64 ^ (6 + g) ≤ 64 ^ 10 := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2 : (64 : ℕ) ^ 10 < 2 ^ 63 := by norm_num
      omega
    omega
  | mid g e =>
    have : 4 ≤ g := by
      by_contra hc
      have h1 : 64 ^ (7 + g) ≤ 64 ^ 10 := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2 : (64 : ℕ) ^ 10 < 2 ^ 63 := by norm_num
      have h3 : 64 ^ (7 + g) - 64 ^ (1 + g) ≤ 64 ^ (7 + g) := Nat.sub_le _ _
      omega
    omega
  | botDesc g h' hgh hg e hd =>
    have : 10 ≤ g := by
      by_contra hc
      have h1 : 64 ^ (g + 1) ≤ 64 ^ 10 := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2 : (64 : ℕ) ^ 10 < 2 ^ 63 := by norm_num
      have h3 : 64 ^ (g + 1) - 64 ^ (h' + 1) ≤ 64 ^ (g + 1) := Nat.sub_le _ _
      omega
    omega

/-- **Parent source.** A node at `(t, l-1)` sending `down > 0` to a big node at `(t+1, l)`:
`down` is a multiple of `2^30`. -/
theorem parent_down_dvd (d : ℕ) (hd : 7 ≤ d) (l t : ℕ) (ht1 : 1 ≤ t) (ht : t + 1 < tf7 d)
    (hl : 1 ≤ l) (hdr : 0 < flowDown7 d hd l (t + 1)) (hbig : 2 ^ 63 < flowA7 d hd l (t + 1))
    (hsrc : 0 < flowDown7 d hd (l - 1) t) : 2 ^ 30 ∣ flowDown7 d hd (l - 1) t := by
  have hE := (node_shape d hd (t + 1) l (by omega) ht).big_exponent hdr hbig
  have h := (node_shape d hd t (l - 1) ht1 (by omega)).dvd_down hsrc
  exact (pow_dvd_pow 2 (by omega)).trans h

/-- **Child source.** A node at `(t, l+1)` sending `up > 0` to a big node at `(t+1, l)`:
`up / 2` is a multiple of `2^47`. -/
theorem child_up_half_dvd (d : ℕ) (hd : 7 ≤ d) (l t : ℕ) (ht1 : 1 ≤ t) (ht : t + 1 < tf7 d)
    (hdr : 0 < flowDown7 d hd l (t + 1)) (hbig : 2 ^ 63 < flowA7 d hd l (t + 1))
    (hsrc : 0 < flowDown7 d hd (l + 1) t) : 2 ^ 47 ∣ flowUp7 d hd (l + 1) t / 2 := by
  have hE := (node_shape d hd (t + 1) l (by omega) ht).big_exponent hdr hbig
  have h := (node_shape d hd t (l + 1) ht1 (by omega)).dvd_up_half hsrc
  exact (pow_dvd_pow 2 (by omega)).trans h


end Chvatal
