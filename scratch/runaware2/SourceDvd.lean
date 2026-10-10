module

public import AKS.Chvatal.NodeGeom

@[expose] public section

namespace Chvatal

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
