module

public import AKS.Chvatal.NodeGeom
import Mathlib.Tactic.IntervalCases

@[expose] public section

namespace Chvatal

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

end Chvatal
