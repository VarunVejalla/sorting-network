import R1NodeSpec
import AKS.Chvatal.BadSendReal

/-! # Lemma 4.2′, sorted part, for unequal blocks (W1, step 5)

Natural-number keys `K`, `|K| = π + Σ_{h<k} b_h`, `π` even; child `h` owns the address interval
`[U + hS, U + (h+1)S)` and the node holds at most `G_h + ρ` keys addressed to it (Lemma 4.1′).
Sorted window `j` is the rank range `[π/2 + off_j, π/2 + off_{j+1})`, `off_j = Σ_{h<j} b_h`.
Then the keys in window `j` that are not addressed to child `j` number at most

  `O_L + O_R + (k−1)ρ + (Σ_{h<j} θ_h − π/2)⁺ + (Σ_{j<h<k} θ_h − π/2)⁺`,   `θ_h = G_h − b_h`,

with `O_L`, `O_R` the keys addressed left/right of the node's range (`window_wrong_gen`). -/

namespace R1T

open Finset
open Chvatal.BW (rankN sorted_window_wrong_le card_lt_split card_lt_add_card_ge)

/-- Keys below `U + jS` = keys below `U` plus the keys of the first `j` address intervals. -/
theorem count_below (K : Finset ℕ) (U S : ℕ) : ∀ j : ℕ,
    (K.filter (· < U + j * S)).card =
      (K.filter (· < U)).card + ∑ h ∈ range j, (K.filter fun κ => U + h * S ≤ κ ∧ κ < U + (h + 1) * S).card
  | 0 => by simp
  | j + 1 => by
    rw [sum_range_succ, ← add_assoc, ← count_below K U S j]
    exact card_lt_split K (Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _)

/-- Keys at or above `U + (j+1)S`, inside the node range, are the keys of the intervals above `j`. -/
theorem count_above (K : Finset ℕ) (U S k j : ℕ) (hj : j < k) :
    ((K.filter (U + (j + 1) * S ≤ ·)).card : ℝ) =
      (K.filter (U + k * S ≤ ·)).card +
        ∑ h ∈ Ico (j + 1) k, ((K.filter fun κ => U + h * S ≤ κ ∧ κ < U + (h + 1) * S).card : ℝ) := by
  have h1 := card_lt_add_card_ge K (U + (j + 1) * S)
  have h2 := card_lt_add_card_ge K (U + k * S)
  have h3 := count_below K U S (j + 1)
  have h4 := count_below K U S k
  have hs : ∑ h ∈ range k, ((K.filter fun κ => U + h * S ≤ κ ∧ κ < U + (h + 1) * S).card : ℝ) =
      ∑ h ∈ range (j + 1), ((K.filter fun κ => U + h * S ≤ κ ∧ κ < U + (h + 1) * S).card : ℝ) +
        ∑ h ∈ Ico (j + 1) k, ((K.filter fun κ => U + h * S ≤ κ ∧ κ < U + (h + 1) * S).card : ℝ) := by
    rw [range_eq_Ico, ← sum_Ico_consecutive _ (Nat.zero_le _) (by omega : j + 1 ≤ k)]
  have h1' : ((K.filter (· < U + (j + 1) * S)).card : ℝ) + (K.filter (U + (j + 1) * S ≤ ·)).card =
      K.card := by exact_mod_cast h1
  have h2' : ((K.filter (· < U + k * S)).card : ℝ) + (K.filter (U + k * S ≤ ·)).card = K.card := by
    exact_mod_cast h2
  have h3' : ((K.filter (· < U + (j + 1) * S)).card : ℝ) = (K.filter (· < U)).card +
      ∑ h ∈ range (j + 1), ((K.filter fun κ => U + h * S ≤ κ ∧ κ < U + (h + 1) * S).card : ℝ) := by
    exact_mod_cast h3
  have h4' : ((K.filter (· < U + k * S)).card : ℝ) = (K.filter (· < U)).card +
      ∑ h ∈ range k, ((K.filter fun κ => U + h * S ≤ κ ∧ κ < U + (h + 1) * S).card : ℝ) := by
    exact_mod_cast h4
  linarith

/-- **Window bound for unequal blocks.** -/
theorem window_wrong_gen (K : Finset ℕ) (k π U S j : ℕ) (b : ℕ → ℕ) (G : ℕ → ℝ) (ρ : ℝ)
    (hj : j < k) (hρ : 0 ≤ ρ) (hπ : 2 ∣ π) (hK : K.card = π + ∑ h ∈ range k, b h)
    (hM : ∀ h < k, ((K.filter fun κ => U + h * S ≤ κ ∧ κ < U + (h + 1) * S).card : ℝ) ≤ G h + ρ) :
    ((K.filter fun κ => π / 2 + ∑ h ∈ range j, b h ≤ rankN K κ ∧
        rankN K κ < π / 2 + ∑ h ∈ range j, b h + b j ∧
          ¬ (U + j * S ≤ κ ∧ κ < U + (j + 1) * S)).card : ℝ) ≤
      (K.filter (· < U)).card + (K.filter (U + k * S ≤ ·)).card + ((k : ℝ) - 1) * ρ +
        max 0 (∑ h ∈ range j, (G h - b h) - (π : ℝ) / 2) +
        max 0 (∑ h ∈ Ico (j + 1) k, (G h - b h) - (π : ℝ) / 2) := by
  set s := π / 2 + ∑ h ∈ range j, b h with hs
  have hsplitK : ∑ h ∈ range k, b h = ∑ h ∈ range j, b h + b j + ∑ h ∈ Ico (j + 1) k, b h := by
    rw [range_eq_Ico, ← sum_Ico_consecutive _ (Nat.zero_le _) (by omega : j + 1 ≤ k),
      ← range_eq_Ico, sum_range_succ]
  have hW := sorted_window_wrong_le K s (b j) (U + j * S) (U + (j + 1) * S) (by
    rw [hK, hsplitK, hs]; obtain ⟨p, rfl⟩ := hπ; omega)
  set L := (K.filter (· < U + j * S)).card with hL
  set R := (K.filter (U + (j + 1) * S ≤ ·)).card with hR
  have hT : K.card - s - b j = π / 2 + ∑ h ∈ Ico (j + 1) k, b h := by
    rw [hK, hsplitK, hs]; obtain ⟨p, rfl⟩ := hπ; omega
  rw [hT] at hW
  -- real bounds on L and R
  have hLr : (L : ℝ) ≤ (K.filter (· < U)).card + ∑ h ∈ range j, (G h + ρ) := by
    have := count_below K U S j
    have e : (L : ℝ) = (K.filter (· < U)).card +
        ∑ h ∈ range j, ((K.filter fun κ => U + h * S ≤ κ ∧ κ < U + (h + 1) * S).card : ℝ) := by
      rw [hL]; exact_mod_cast this
    rw [e]
    have := sum_le_sum fun h (hh : h ∈ range j) => hM h (by simp at hh; omega)
    linarith
  have hRr : (R : ℝ) ≤ (K.filter (U + k * S ≤ ·)).card + ∑ h ∈ Ico (j + 1) k, (G h + ρ) := by
    rw [hR, count_above K U S k j hj]
    have := sum_le_sum fun h (hh : h ∈ Ico (j + 1) k) => hM h (by simp at hh; omega)
    linarith
  have hsr : (s : ℝ) = (π : ℝ) / 2 + ∑ h ∈ range j, (b h : ℝ) := by
    rw [hs]; obtain ⟨p, rfl⟩ := hπ; push_cast; rw [show 2 * p / 2 = p by omega]; push_cast; ring
  have hx : (((L - s : ℕ)) : ℝ) ≤ (K.filter (· < U)).card + j * ρ +
      max 0 (∑ h ∈ range j, (G h - b h) - (π : ℝ) / 2) := by
    have e1 : ∑ h ∈ range j, (G h + ρ) = ∑ h ∈ range j, (G h - b h) + ∑ h ∈ range j, (b h : ℝ) + j * ρ := by
      rw [← sum_add_distrib]; simp only [sum_add_distrib, sum_const, card_range, nsmul_eq_mul]
      rw [← sum_add_distrib]; congr 1; · exact sum_congr rfl fun _ _ => by ring
    have hO : (0 : ℝ) ≤ (K.filter (· < U)).card := Nat.cast_nonneg _
    have hjρ : 0 ≤ (j : ℝ) * ρ := mul_nonneg (Nat.cast_nonneg _) hρ
    by_cases h : L ≤ s
    · rw [Nat.sub_eq_zero_of_le h]; push_cast
      have := le_max_left 0 (∑ h ∈ range j, (G h - b h) - (π : ℝ) / 2)
      linarith
    · rw [Nat.cast_sub (by omega)]
      have := le_max_right 0 (∑ h ∈ range j, (G h - b h) - (π : ℝ) / 2)
      linarith
  have hy : (((R - (π / 2 + ∑ h ∈ Ico (j + 1) k, b h) : ℕ)) : ℝ) ≤ (K.filter (U + k * S ≤ ·)).card +
      ((k : ℝ) - 1 - j) * ρ + max 0 (∑ h ∈ Ico (j + 1) k, (G h - b h) - (π : ℝ) / 2) := by
    have hcard : ((Ico (j + 1) k).card : ℝ) = (k : ℝ) - 1 - j := by
      rw [Nat.card_Ico, Nat.cast_sub (by omega)]; push_cast; ring
    have e1 : ∑ h ∈ Ico (j + 1) k, (G h + ρ) =
        ∑ h ∈ Ico (j + 1) k, (G h - b h) + ∑ h ∈ Ico (j + 1) k, (b h : ℝ) + ((k : ℝ) - 1 - j) * ρ := by
      rw [← hcard, ← sum_add_distrib]; simp only [sum_add_distrib, sum_const, nsmul_eq_mul]
      rw [← sum_add_distrib]; congr 1; · exact sum_congr rfl fun _ _ => by ring
    have hπ2 : (((π / 2 + ∑ h ∈ Ico (j + 1) k, b h : ℕ)) : ℝ) =
        (π : ℝ) / 2 + ∑ h ∈ Ico (j + 1) k, (b h : ℝ) := by
      obtain ⟨p, rfl⟩ := hπ; push_cast; rw [show 2 * p / 2 = p by omega]; push_cast; ring
    have hO : (0 : ℝ) ≤ (K.filter (U + k * S ≤ ·)).card := Nat.cast_nonneg _
    have hkρ : 0 ≤ ((k : ℝ) - 1 - j) * ρ := mul_nonneg (by
      have : (j : ℝ) + 1 ≤ k := by exact_mod_cast hj
      linarith) hρ
    by_cases h : R ≤ π / 2 + ∑ h ∈ Ico (j + 1) k, b h
    · rw [Nat.sub_eq_zero_of_le h]; push_cast
      have := le_max_left 0 (∑ h ∈ Ico (j + 1) k, (G h - b h) - (π : ℝ) / 2)
      linarith
    · rw [Nat.cast_sub (by omega), hπ2]
      have := le_max_right 0 (∑ h ∈ Ico (j + 1) k, (G h - b h) - (π : ℝ) / 2)
      linarith
  have hWr : ((K.filter fun κ => s ≤ rankN K κ ∧ rankN K κ < s + b j ∧
        ¬ (U + j * S ≤ κ ∧ κ < U + (j + 1) * S)).card : ℝ) ≤
      (((L - s : ℕ)) : ℝ) + (((R - (π / 2 + ∑ h ∈ Ico (j + 1) k, b h) : ℕ)) : ℝ) := by
    exact_mod_cast hW
  have e : ((k : ℝ) - 1) * ρ = j * ρ + ((k : ℝ) - 1 - j) * ρ := by ring
  linarith

end R1T
