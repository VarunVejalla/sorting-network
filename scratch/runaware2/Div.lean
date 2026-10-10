import AKS.Chvatal.NodeGeom
import Mathlib.Data.Nat.Factorization.Basic

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

end Chvatal
