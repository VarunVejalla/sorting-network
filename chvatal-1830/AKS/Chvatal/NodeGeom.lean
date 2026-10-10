module

public import AKS.Chvatal.GeometryScale
public import AKS.Chvatal.FlowSizes7

@[expose] public section

namespace Chvatal

/-! Node geometry: every node with >2^64 wires runs separator on m×n matrix with 2^59 < m ≤ 2^60. -/

/-- Geometry of a separator node with `a` wires, `up` to parent, `down` to each child. -/
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

theorem p64 (n : ℕ) : (64 : ℕ) ^ n = 2 ^ (6 * n) := by
  rw [show (64 : ℕ) = 2 ^ 6 by norm_num, ← pow_mul]

/-- Descending top node (also the root at `t = 0`). -/
theorem nodeGeom_top {a up down : ℕ} (g : ℕ) (ha : a = 64 ^ (g + 1)) (hu : up = 0)
    (hdn : down = 64 ^ g) (hbig : 2 ^ 64 < a) : Nonempty (NodeGeom a up down) := by
  refine nodeGeom_of_template (6 * g) 64 0 1 (by norm_num) (by norm_num) (by norm_num)
    (Or.inl rfl) _ _ _ ?_ ?_ ?_ hbig
  · rw [ha, pow_succ, p64]
  · rw [hu]; simp
  · rw [hdn]; simp [p64]

/-- Geometry from the node classification: the four sending shapes use the templates
`(m', f₀, b₀) = (64, 0, 1)`, `(2^30, 32, 2^24 - 1)`, `(137438953470, 4095, 2147483520)`,
`(8192 R + 8190, 4095, 128 R)`. -/
theorem NodeShape.geom {d t i a u n : ℕ} (h : NodeShape d t i a u n) (hn : 0 < n)
    (hbig : 2 ^ 64 < a) : Nonempty (NodeGeom a u n) := by
  cases h with
  | off => omega
  | botRise => omega
  | topDesc g => exact nodeGeom_top g rfl rfl rfl hbig
  | topRise f =>
    refine nodeGeom_of_template (6 * f + 6) (2 ^ 30) 32 (2 ^ 24 - 1) (by norm_num) (by norm_num)
      (by norm_num) (Or.inr (by norm_num)) _ _ _ ?_ ?_ ?_ hbig
    · rw [p64, show 6 * (6 + f) = 6 * f + 6 + 30 by ring, pow_add]
    · rw [p64, show 6 * (1 + f) = 6 * f + 6 by ring]; ring
    · rw [p64, show 6 * (1 + f) = 6 * f + 6 by ring]; norm_num; ring
  | mid g =>
    refine nodeGeom_of_template (6 * g + 5) 137438953470 4095 2147483520 (by norm_num)
      (by norm_num) (by norm_num) (Or.inr (by norm_num)) _ _ _ ?_ ?_ ?_ hbig
    · apply Nat.sub_eq_of_eq_add
      simp only [p64]; ring
    · simp only [p64]; ring
    · simp only [p64]; ring
  | botDesc g h hgh hg =>
    have hj1 : h + 3 ≤ g := by
      by_contra hc
      have : 64 ^ g ≤ 64 ^ (h + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    obtain ⟨j, hj⟩ : ∃ j, g = h + 2 + j := ⟨g - (h + 2), by omega⟩
    have hP4 : 64 ^ j ≤ 16777216 :=
      calc 64 ^ j ≤ 64 ^ 4 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 16777216 := by norm_num
    obtain ⟨R, hR⟩ : ∃ R, 64 ^ j = R + 1 := ⟨64 ^ j - 1, by have := Nat.one_le_pow j 64 (by norm_num); omega⟩
    have hm'le : 8192 * R + 8190 ≤ 2 ^ 37 := by
      have : (2 : ℕ) ^ 37 = 137438953472 := by norm_num
      omega
    refine nodeGeom_of_template (6 * h + 5) (8192 * R + 8190) 4095 (128 * R) (by omega) hm'le
      (by omega) (Or.inr (by
        have : 4095 * (8192 * R + 8190) ≤ 4095 * 2 ^ 37 := Nat.mul_le_mul_left _ hm'le
        omega)) _ _ _ ?_ ?_ ?_ hbig
    · apply Nat.sub_eq_of_eq_add
      rw [show 64 ^ (g + 1) = 64 ^ h * 64 ^ 3 * 64 ^ j by rw [hj]; ring, hR, p64 (h + 1), p64 h,
        show (2 : ℕ) ^ (6 * h + 5) = 2 ^ (6 * h) * 32 by rw [pow_add]; norm_num]
      norm_num; ring
    · simp only [p64]; ring
    · apply Nat.sub_eq_of_eq_add
      rw [show 64 ^ g = 64 ^ h * 64 ^ 2 * 64 ^ j by rw [hj]; ring, hR, p64 (h + 2), p64 h,
        show (2 : ℕ) ^ (6 * h + 5) = 2 ^ (6 * h) * 32 by rw [pow_add]; norm_num]
      norm_num; ring

/-- **B5c (A10):** Every node with >2^64 wires and down>0 carries separator geometry. -/
theorem nodeGeom_exists (d : ℕ) (hd : 7 ≤ d) (l t : ℕ) (hdown : 0 < flowDown7 d hd l t)
    (hbig : 2 ^ 64 < flowA7 d hd l t) (ht : t < tf7 d) :
    Nonempty (NodeGeom (flowA7 d hd l t) (flowUp7 d hd l t) (flowDown7 d hd l t)) := by
  rcases Nat.eq_zero_or_pos t with rfl | ht1
  · obtain rfl : l = 0 := by
      by_contra hl; simp [flowA7, hl] at hbig
    obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
    exact nodeGeom_top e (by simp [flowA7]) (by simp [flowUp7]) (by simp [flowDown7]) hbig
  · exact (node_shape d hd t l ht1 ht).geom hdown hbig

end Chvatal
