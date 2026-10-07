module

/-
  # Sorted-window count (Chvátal, DCS-TR-294, Lemma 4.2)

  A node holds a finite set `K` of keys (values are addresses).  The rank of a key is its
  position in the sorted order.  A perfect sorter puts into the block window of positions
  `[π/2 + jτ, π/2 + (j+1)τ)` exactly the keys whose ranks lie there; this file bounds how many
  of those are not addressed to the child interval `I_j`, and how a physical output with an
  arbitrary position function differs from the sorted one.
-/

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

namespace Chvatal

open Finset

/-- Rank of a key in the sorted order of `K`. -/
def rankIn (K : Finset ℕ) (κ : ℕ) : ℕ := (K.filter (· < κ)).card

theorem rankIn_lt_of_lt {K : Finset ℕ} {κ κ' : ℕ} (hκ : κ ∈ K) (h : κ < κ') :
    rankIn K κ < rankIn K κ' := by
  unfold rankIn
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨κ, by simp [hκ, h], by simp⟩
  · intro x hx
    simp only [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, lt_trans hx.2 h⟩

theorem rankIn_injOn (K : Finset ℕ) : Set.InjOn (rankIn K) (K : Set ℕ) := by
  intro x hx y hy hxy
  rcases lt_trichotomy x y with h | h | h
  · exact absurd hxy (ne_of_lt (rankIn_lt_of_lt hx h))
  · exact h
  · exact absurd hxy.symm (ne_of_lt (rankIn_lt_of_lt hy h))

/-- Keys below `lo` have rank below `L`. -/
theorem rankIn_lt_of_lt_lo {K : Finset ℕ} {κ lo : ℕ} (hκ : κ ∈ K) (h : κ < lo) :
    rankIn K κ < (K.filter (· < lo)).card := by
  unfold rankIn
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨κ, by simp [hκ, h], by simp⟩
  · intro x hx
    simp only [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, lt_trans hx.2 h⟩

theorem card_lt_add_card_ge (K : Finset ℕ) (hi : ℕ) :
    (K.filter (· < hi)).card + (K.filter (hi ≤ ·)).card = K.card := by
  have := Finset.card_filter_add_card_filter_not (s := K) (fun x => x < hi)
  simpa [not_lt] using this

/-- Keys at least `hi` have rank at least `a - R`. -/
theorem le_rankIn_of_hi_le {K : Finset ℕ} {κ hi : ℕ} (h : hi ≤ κ) :
    K.card - (K.filter (hi ≤ ·)).card ≤ rankIn K κ := by
  have h1 := card_lt_add_card_ge K hi
  have h2 : (K.filter (· < hi)).card ≤ rankIn K κ := by
    unfold rankIn
    apply Finset.card_le_card
    intro x hx
    simp only [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, lt_of_lt_of_le hx.2 h⟩
  omega

/-- W-A: the sorted window contains few keys outside the address interval. -/
theorem sorted_window_wrong_le (K : Finset ℕ) (s τ lo hi : ℕ) (hsτ : s + τ ≤ K.card) :
    (K.filter fun κ => s ≤ rankIn K κ ∧ rankIn K κ < s + τ ∧ ¬ (lo ≤ κ ∧ κ < hi)).card ≤
      ((K.filter (· < lo)).card - s) +
        ((K.filter (hi ≤ ·)).card - (K.card - s - τ)) := by
  set L := (K.filter (· < lo)).card with hL
  set R := (K.filter (hi ≤ ·)).card with hR
  have hRa : R ≤ K.card := Finset.card_le_card (Finset.filter_subset _ _)
  let t : Finset ℕ := Finset.Ico s (min L (s + τ)) ∪ Finset.Ico (max (K.card - R) s) (s + τ)
  have hsub : (K.filter fun κ => s ≤ rankIn K κ ∧ rankIn K κ < s + τ ∧
      ¬ (lo ≤ κ ∧ κ < hi)).card ≤ t.card := by
    apply Finset.card_le_card_of_injOn (rankIn K)
    · intro κ hκ
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hκ
      obtain ⟨hmem, h1, h2, h3⟩ := hκ
      simp only [Finset.mem_coe, t, Finset.mem_union, Finset.mem_Ico, lt_min_iff, max_le_iff]
      by_cases hlo : κ < lo
      · left
        exact ⟨h1, rankIn_lt_of_lt_lo hmem hlo, h2⟩
      · have hhi : hi ≤ κ := by
          by_contra hh
          exact h3 ⟨by omega, by omega⟩
        right
        exact ⟨⟨le_rankIn_of_hi_le hhi, h1⟩, h2⟩
    · exact (rankIn_injOn K).mono (by intro x hx; simp only [Finset.coe_filter] at hx; exact hx.1)
  have hcard : t.card ≤ (L - s) + (R - (K.card - s - τ)) := by
    refine le_trans (Finset.card_union_le _ _) ?_
    simp only [Nat.card_Ico]
    omega
  exact le_trans hsub hcard

/-- W-B: intruders in the physical window are intruders of the sorted window, or displaced
keys. -/
theorem intruder_decomposition (K : Finset ℕ) (pos : ℕ → ℕ) (s τ : ℕ) (Q : ℕ → Prop)
    [DecidablePred Q] :
    (K.filter fun κ => s ≤ pos κ ∧ pos κ < s + τ ∧ ¬ Q κ).card ≤
      (K.filter fun κ => s ≤ rankIn K κ ∧ rankIn K κ < s + τ ∧ ¬ Q κ).card +
      (K.filter fun κ => s ≤ pos κ ∧ pos κ < s + τ ∧
        ¬ (s ≤ rankIn K κ ∧ rankIn K κ < s + τ)).card ∧
    (K.filter fun κ => s ≤ pos κ ∧ pos κ < s + τ ∧
        ¬ (s ≤ rankIn K κ ∧ rankIn K κ < s + τ)).card ≤
      (K.filter fun κ => s + τ ≤ rankIn K κ ∧ pos κ < s + τ).card +
      (K.filter fun κ => rankIn K κ < s ∧ s ≤ pos κ).card := by
  constructor
  · refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
    intro κ hκ
    simp only [Finset.mem_filter, Finset.mem_union] at hκ ⊢
    obtain ⟨hm, h1, h2, h3⟩ := hκ
    by_cases h : s ≤ rankIn K κ ∧ rankIn K κ < s + τ
    · left; exact ⟨hm, h.1, h.2, h3⟩
    · right; exact ⟨hm, h1, h2, h⟩
  · refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
    intro κ hκ
    simp only [Finset.mem_filter, Finset.mem_union] at hκ ⊢
    obtain ⟨hm, h1, h2, h3⟩ := hκ
    by_cases h : s + τ ≤ rankIn K κ
    · left; exact ⟨hm, h, h2⟩
    · right
      refine ⟨hm, ?_, h1⟩
      by_contra hh
      exact h3 ⟨by omega, by omega⟩

/-! ### Counting keys below the child intervals -/

theorem card_lt_split (K : Finset ℕ) {lo hi : ℕ} (h : lo ≤ hi) :
    (K.filter (· < hi)).card =
      (K.filter (· < lo)).card + (K.filter fun κ => lo ≤ κ ∧ κ < hi).card := by
  have : K.filter (· < hi) = K.filter (· < lo) ∪ K.filter (fun κ => lo ≤ κ ∧ κ < hi) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hx, hh⟩
      by_cases hl : x < lo
      · exact Or.inl ⟨hx, hl⟩
      · exact Or.inr ⟨hx, by omega, hh⟩
    · rintro (⟨hx, hl⟩ | ⟨hx, _, hh⟩)
      · exact ⟨hx, by omega⟩
      · exact ⟨hx, hh⟩
  rw [this, Finset.card_union_of_disjoint]
  rw [Finset.disjoint_filter]
  intro x _ h1 h2
  omega

theorem lower_count_le (K : Finset ℕ) (k τ S Ulo : ℕ) (ρ : ℝ)
    (hM : ∀ j' < k, ((K.filter fun κ => Ulo + j'*S ≤ κ ∧ κ < Ulo + (j'+1)*S).card : ℝ) ≤ τ + ρ)
    (m n : ℕ) (hn : m + n ≤ k) :
    ((K.filter (· < Ulo + (m + n)*S)).card : ℝ) ≤
      (K.filter (· < Ulo + m*S)).card + n * (τ + ρ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 := ih (by omega)
    have h2 := hM (m + n) (by omega)
    have hle : Ulo + (m + n)*S ≤ Ulo + (m + n + 1)*S :=
      Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _
    have h3 := card_lt_split K hle
    have h4 : ((K.filter (· < Ulo + (m + (n+1))*S)).card : ℝ) =
        (K.filter (· < Ulo + (m + n)*S)).card +
          (K.filter fun κ => Ulo + (m + n)*S ≤ κ ∧ κ < Ulo + (m + n + 1)*S).card := by
      rw [show m + (n+1) = m + n + 1 by ring, h3]; push_cast; ring
    rw [h4]
    push_cast
    nlinarith

/-- W-C (Lemma 4.2). -/
theorem window_wrong_le (K : Finset ℕ) (k π τ S Ulo j : ℕ) (hj : j < k)
    (ha : K.card = π + k * τ) (hπ : 2 ∣ π) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hM : ∀ j' < k, ((K.filter fun κ => Ulo + j'*S ≤ κ ∧ κ < Ulo + (j'+1)*S).card : ℝ) ≤ τ + ρ)
    (hpos : (π : ℝ) / 2 ≤ (K.filter (· < Ulo)).card + (K.filter (Ulo + k*S ≤ ·)).card +
      ((k : ℝ) - 1) * ρ) :
    ((K.filter fun κ => π/2 + j*τ ≤ rankIn K κ ∧ rankIn K κ < π/2 + (j+1)*τ ∧
        ¬ (Ulo + j*S ≤ κ ∧ κ < Ulo + (j+1)*S)).card : ℝ) ≤
      (K.filter (· < Ulo)).card + (K.filter (Ulo + k*S ≤ ·)).card +
        ((k : ℝ) - 1) * ρ - π / 2 := by
  obtain ⟨p, rfl⟩ := hπ
  have hp : 2 * p / 2 = p := by omega
  rw [hp]
  obtain ⟨m, rfl⟩ : ∃ m, k = j + 1 + m := ⟨k - (j+1), by omega⟩
  set OL := (K.filter (· < Ulo)).card with hOL
  set OR := (K.filter (Ulo + (j+1+m)*S ≤ ·)).card with hOR
  have hW := sorted_window_wrong_le K (p + j*τ) τ (Ulo + j*S) (Ulo + (j+1)*S) (by
    rw [ha]; nlinarith [Nat.zero_le (m*τ)])
  have hwin : (p + j*τ) + τ = p + (j+1)*τ := by ring
  rw [hwin] at hW
  set L := (K.filter (· < Ulo + j*S)).card with hLdef
  set R := (K.filter (Ulo + (j+1)*S ≤ ·)).card with hRdef
  have hT : K.card - (p + j*τ) - τ = p + m*τ := by
    rw [ha]; apply Nat.sub_eq_of_eq_add; apply Nat.sub_eq_of_eq_add; ring
  -- real bounds
  have hLb : (L : ℝ) ≤ OL + j * (τ + ρ) := by
    have := lower_count_le K (j+1+m) τ S Ulo ρ hM 0 j (by omega)
    simpa [hLdef, hOL] using this
  have hRtot := card_lt_add_card_ge K (Ulo + (j+1)*S)
  have hk := lower_count_le K (j+1+m) τ S Ulo ρ hM (j+1) m (by omega)
  have hkt := card_lt_add_card_ge K (Ulo + (j+1+m)*S)
  have hRb : (R : ℝ) ≤ OR + m * (τ + ρ) := by
    have e1 : ((K.filter (· < Ulo + (j+1+m)*S)).card : ℝ) + OR = K.card := by
      exact_mod_cast hkt
    have e2 : ((K.filter (· < Ulo + (j+1)*S)).card : ℝ) + R = K.card := by
      exact_mod_cast hRtot
    linarith
  rw [hT] at hW
  have hx : (((L - (p + j*τ) : ℕ)) : ℝ) ≤ max 0 ((OL : ℝ) + j*ρ - p) := by
    by_cases h : L ≤ p + j*τ
    · rw [Nat.sub_eq_zero_of_le h]; simp
    · rw [Nat.cast_sub (by omega)]
      push_cast
      exact le_max_of_le_right (by linarith)
  have hy : (((R - (p + m*τ) : ℕ)) : ℝ) ≤ max 0 ((OR : ℝ) + m*ρ - p) := by
    by_cases h : R ≤ p + m*τ
    · rw [Nat.sub_eq_zero_of_le h]; simp
    · rw [Nat.cast_sub (by omega)]
      push_cast
      exact le_max_of_le_right (by linarith)
  have hWr : ((K.filter fun κ => p + j*τ ≤ rankIn K κ ∧ rankIn K κ < p + (j+1)*τ ∧
        ¬ (Ulo + j*S ≤ κ ∧ κ < Ulo + (j+1)*S)).card : ℝ) ≤
      (((L - (p + j*τ) : ℕ)) : ℝ) + (((R - (p + m*τ) : ℕ)) : ℝ) := by
    exact_mod_cast hW
  have hOLn : (0 : ℝ) ≤ OL := Nat.cast_nonneg _
  have hORn : (0 : ℝ) ≤ OR := Nat.cast_nonneg _
  have hpn : (0 : ℝ) ≤ p := Nat.cast_nonneg _
  have hmρ : 0 ≤ (m : ℝ) * ρ := mul_nonneg (Nat.cast_nonneg _) hρ
  have hjρ : 0 ≤ (j : ℝ) * ρ := mul_nonneg (Nat.cast_nonneg _) hρ
  have goal : ((((j+1+m : ℕ) : ℝ) - 1) * ρ) = j * ρ + m * ρ := by push_cast; ring
  have h2 : ((2 * p : ℕ) : ℝ) / 2 = p := by push_cast; ring
  rw [goal, h2] at hpos ⊢
  rcases max_cases 0 ((OL : ℝ) + j*ρ - p) with ⟨c1, _⟩ | ⟨c1, _⟩ <;>
    rcases max_cases 0 ((OR : ℝ) + m*ρ - p) with ⟨c2, _⟩ | ⟨c2, _⟩ <;>
    · rw [c1] at hx; rw [c2] at hy; linarith

end Chvatal
