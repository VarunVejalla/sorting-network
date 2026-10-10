module

public import AKS.Separator.PatersonConstruction

/-! # Local restricted-halver estimates inside the separator network -/

@[expose] public section

namespace Paterson

/-- The near-initial-stranger estimate needs a restricted halver only for the
actual cohort `k`, not for every cohort up to half the local block. -/
theorem restricted_near_initial {n : ℕ} {ε α : ℚ}
    {halvers : (m : ℕ) → ComparatorNetwork (2 * m)} (t : ℕ)
    (w₁ : Fin n → Fin n) (hw₁ : Function.Injective w₁)
    (hhalver : IsEpsilonAlphaHalver (halvers ((n / 2 ^ t) / 2)) ε α)
    (hε : 0 ≤ ε) (h_even : 2 ∣ n / 2 ^ t)
    (k : ℕ) (hk : (k : ℝ) ≤ (α : ℝ) * ↑(n / 2 ^ t / 2)) :
    let C := n / 2 ^ t
    let H := C / 2
    let w₂ := (halverAtLevel n halvers t).exec w₁
    let a := (Finset.univ.filter (fun pos : Fin n ↦
      pos.val < C ∧ (w₁ pos).val < k)).card
    ((Finset.univ.filter (fun pos : Fin n ↦
      H ≤ pos.val ∧ pos.val < C ∧ (w₂ pos).val < k)).card : ℝ) ≤
      (ε : ℝ) * a := by
  intro C H w₂ a
  have h2H_eq : 2 * H = C := by have := Nat.div_mul_cancel h_even; omega
  have hC_le_n : C ≤ n := Nat.div_le_self n _
  have h2H_le_n : 2 * H ≤ n := by omega
  by_cases hH : H = 0
  · have hC0 : C = 0 := by omega
    have hempty : (Finset.univ.filter (fun pos : Fin n ↦
        H ≤ pos.val ∧ pos.val < C ∧ (w₂ pos).val < k)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro pos _ ⟨_, h, _⟩; omega
    simp [hempty]
    exact mul_nonneg (by exact_mod_cast hε) (Nat.cast_nonneg _)
  · have h2H_pos : 0 < 2 * H := by omega
    set u : Fin (2 * H) → Fin n :=
      fun j ↦ w₁ ⟨j.val, by have := j.isLt; omega⟩ with hu_def
    have hu_inj : Function.Injective u := by
      intro j₁ j₂ heq
      have h := hw₁ heq
      exact Fin.ext (by have := congr_arg Fin.val h; dsimp at this; exact this)
    have ha_eq : a = (Finset.univ.filter (fun i : Fin (2 * H) ↦ (u i).val < k)).card := by
      apply Finset.card_nbij'
        (fun pos : Fin n ↦
          if h : pos.val < 2 * H then ⟨pos.val, h⟩ else ⟨0, h2H_pos⟩)
        (fun i : Fin (2 * H) ↦ ⟨i.val, by have := i.isLt; omega⟩)
      · intro pos hpos
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hpos ⊢
        rw [dif_pos (show pos.val < 2 * H by omega)]
        exact hpos.2
      · intro i hi
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        exact ⟨by show i.val < C; have := i.isLt; omega, hi⟩
      · intro pos hpos
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hpos
        ext; simp only [dif_pos (show pos.val < 2 * H by omega)]
      · intro i _
        ext; dsimp only; split_ifs with h
        · rfl
        · exact absurd i.isLt h
    have ha_le : ((Finset.univ.filter (fun i : Fin (2 * H) ↦
        (u i).val < k)).card : ℝ) ≤ (α : ℝ) * H := by
      calc
        _ ≤ (k : ℝ) := by exact_mod_cast injective_count_lt_le u hu_inj k
        _ ≤ (α : ℝ) * H := by simpa only [H, C] using hk
    have hcard_eq : (Finset.univ.filter (fun pos : Fin n ↦
        H ≤ pos.val ∧ pos.val < C ∧ (w₂ pos).val < k)).card =
      (Finset.univ.filter (fun pos : Fin (2 * H) ↦
        H ≤ pos.val ∧ ((halvers H).exec u pos).val < k)).card := by
      apply Finset.card_nbij'
        (fun pos : Fin n ↦
          if h : pos.val < 2 * H then ⟨pos.val, h⟩ else ⟨0, h2H_pos⟩)
        (fun i : Fin (2 * H) ↦ ⟨i.val, by have := i.isLt; omega⟩)
      · intro pos hpos
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hpos ⊢
        have hlt : pos.val < 2 * H := by omega
        rw [dif_pos hlt]
        refine ⟨hpos.1, ?_⟩
        have hlocal := halverAtLevel_local_eq (halvers := halvers) t w₁ pos hlt
        show ((halvers H).exec u ⟨pos.val, hlt⟩).val < k
        rw [← hlocal]; exact hpos.2.2
      · intro i hi
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        refine ⟨hi.1, by show i.val < C; have := i.isLt; omega, ?_⟩
        change ((halverAtLevel n halvers t).exec w₁ ⟨i.val, _⟩).val < k
        rw [halverAtLevel_local_eq (halvers := halvers) t w₁
          (⟨i.val, by have := i.isLt; omega⟩ : Fin n) i.isLt]
        convert hi.2 using 2
      · intro pos hpos
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hpos
        ext; simp only [dif_pos (show pos.val < 2 * H by omega)]
      · intro i _
        ext; dsimp only; split_ifs with h
        · rfl
        · exact absurd i.isLt h
    have hhalved := restricted_injective_initial hhalver u hu_inj k ha_le
    calc
      ((Finset.univ.filter (fun pos : Fin n ↦
          H ≤ pos.val ∧ pos.val < C ∧ (w₂ pos).val < k)).card : ℝ)
          = ↑(Finset.univ.filter (fun pos : Fin (2 * H) ↦
              H ≤ pos.val ∧ ((halvers H).exec u pos).val < k)).card := by
            exact_mod_cast hcard_eq
      _ ≤ (ε : ℝ) * ↑(Finset.univ.filter (fun i : Fin (2 * H) ↦
          (u i).val < k)).card := hhalved
      _ = (ε : ℝ) * ↑a := by rw [← ha_eq]

/-- Symmetric estimate for large values in the left half of the last block. -/
theorem restricted_near_final {n : ℕ} {ε α : ℚ}
    {halvers : (m : ℕ) → ComparatorNetwork (2 * m)} (t : ℕ)
    (w₁ : Fin n → Fin n) (hw₁ : Function.Injective w₁)
    (hhalver : IsEpsilonAlphaHalver (halvers ((n / 2 ^ t) / 2)) ε α)
    (hε : 0 ≤ ε) (h_even : 2 ∣ n / 2 ^ t) (h_pow_div : 2 ^ t ∣ n)
    (k : ℕ) (hk : (k : ℝ) ≤ (α : ℝ) * ↑(n / 2 ^ t / 2)) :
    let C := n / 2 ^ t
    let H := C / 2
    let w₂ := (halverAtLevel n halvers t).exec w₁
    let a := (Finset.univ.filter (fun pos : Fin n ↦
      n - C ≤ pos.val ∧ n - k ≤ (w₁ pos).val)).card
    ((Finset.univ.filter (fun pos : Fin n ↦
      n - C ≤ pos.val ∧ pos.val < n - H ∧ n - k ≤ (w₂ pos).val)).card : ℝ) ≤
      (ε : ℝ) * a := by
  intro C H w₂ a
  have h2H_eq : 2 * H = C := by have := Nat.div_mul_cancel h_even; omega
  have hC_le_n : C ≤ n := Nat.div_le_self n _
  have h2H_le_n : 2 * H ≤ n := by omega
  by_cases hH : H = 0
  · have hC0 : C = 0 := by omega
    have hempty : (Finset.univ.filter (fun pos : Fin n ↦
        n - C ≤ pos.val ∧ pos.val < n - H ∧ n - k ≤ (w₂ pos).val)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro pos _ ⟨_, h, _⟩; omega
    rw [hempty]; simp
    exact mul_nonneg (by exact_mod_cast hε) (Nat.cast_nonneg _)
  · have h2H_pos : 0 < 2 * H := by omega
    set u : Fin (2 * H) → Fin n :=
      fun j ↦ w₁ ⟨(n - C) + j.val, by have := j.isLt; omega⟩ with hu_def
    have hu_inj : Function.Injective u := by
      intro j₁ j₂ heq
      have h := hw₁ heq
      exact Fin.ext (by have := congr_arg Fin.val h; dsimp at this; omega)
    have ha_eq : a = (Finset.univ.filter (fun i : Fin (2 * H) ↦
        n - k ≤ (u i).val)).card := by
      apply Finset.card_nbij'
        (fun pos : Fin n ↦
          if h : n - C ≤ pos.val then ⟨pos.val - (n - C), by omega⟩ else ⟨0, h2H_pos⟩)
        (fun i : Fin (2 * H) ↦ ⟨(n - C) + i.val, by have := i.isLt; omega⟩)
      · intro pos hpos
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hpos ⊢
        rw [dif_pos hpos.1]
        show n - k ≤ (u ⟨pos.val - (n - C), _⟩).val
        simp only [hu_def]
        have heq : (⟨(n - C) + (pos.val - (n - C)), (by omega)⟩ : Fin n) = pos := by
          ext; show (n - C) + (pos.val - (n - C)) = pos.val; omega
        rw [heq]; exact hpos.2
      · intro i hi
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        exact ⟨by omega, hi⟩
      · intro pos hpos
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hpos
        ext; simp only [dif_pos hpos.1]
        show (n - C) + (pos.val - (n - C)) = pos.val; omega
      · intro i _
        ext; simp only [dif_pos (show n - C ≤ (n - C) + i.val from by omega)]
        show (n - C) + i.val - (n - C) = i.val; omega
    have ha_le : ((Finset.univ.filter (fun i : Fin (2 * H) ↦
        n - k ≤ (u i).val)).card : ℝ) ≤ (α : ℝ) * H := by
      calc
        _ ≤ (k : ℝ) := by exact_mod_cast injective_count_ge_le u hu_inj k
        _ ≤ (α : ℝ) * H := by simpa only [H, C] using hk
    have hcard_eq : (Finset.univ.filter (fun pos : Fin n ↦
        n - C ≤ pos.val ∧ pos.val < n - H ∧ n - k ≤ (w₂ pos).val)).card =
      (Finset.univ.filter (fun pos : Fin (2 * H) ↦
        pos.val < H ∧ n - k ≤ ((halvers H).exec u pos).val)).card := by
      apply Finset.card_nbij'
        (fun pos : Fin n ↦
          if h : n - C ≤ pos.val then ⟨pos.val - (n - C), by omega⟩ else ⟨0, h2H_pos⟩)
        (fun i : Fin (2 * H) ↦ ⟨(n - C) + i.val, by have := i.isLt; omega⟩)
      · intro pos hpos
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hpos ⊢
        rw [dif_pos hpos.1]
        refine ⟨by show pos.val - (n - C) < H; omega, ?_⟩
        have hlocal := halverAtLevel_local_eq_last (halvers := halvers) t h_pow_div w₁ pos hpos.1
          (show pos.val < n - C + 2 * H by omega)
        show n - k ≤ ((halvers H).exec u ⟨pos.val - (n - C), _⟩).val
        simp only [hu_def]
        rw [← hlocal]; exact hpos.2.2
      · intro i hi
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        obtain ⟨hi_lt, hi_val⟩ := hi
        refine ⟨by omega, offset_add_lt_sub h2H_eq hC_le_n hi_lt, ?_⟩
        change n - k ≤ ((halverAtLevel n halvers t).exec w₁ ⟨(n - C) + i.val, _⟩).val
        have hlocal := halverAtLevel_local_eq_last (halvers := halvers) t h_pow_div w₁
          (⟨(n - C) + i.val, by have := i.isLt; omega⟩ : Fin n)
          (show n - C ≤ (n - C) + i.val from by omega)
          (show (n - C) + i.val < n - C + 2 * H from by have := i.isLt; omega)
        rw [hlocal]
        have hfin : (⟨(n - C) + i.val - (n - C), (by omega)⟩ : Fin (2 * H)) = i := by
          ext; show (n - C) + i.val - (n - C) = i.val; omega
        rw [hfin]
        exact hi_val
      · intro pos hpos
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hpos
        ext; simp only [dif_pos hpos.1]
        show (n - C) + (pos.val - (n - C)) = pos.val; omega
      · intro i _
        ext; simp only [dif_pos (show n - C ≤ (n - C) + i.val from by omega)]
        show (n - C) + i.val - (n - C) = i.val; omega
    have hhalved := restricted_injective_final hhalver u hu_inj (n - k) ha_le
    calc
      ((Finset.univ.filter (fun pos : Fin n ↦
          n - C ≤ pos.val ∧ pos.val < n - H ∧ n - k ≤ (w₂ pos).val)).card : ℝ)
          = ↑(Finset.univ.filter (fun pos : Fin (2 * H) ↦
              pos.val < H ∧ n - k ≤ ((halvers H).exec u pos).val)).card := by
            exact_mod_cast hcard_eq
      _ ≤ (ε : ℝ) * ↑(Finset.univ.filter (fun i : Fin (2 * H) ↦
          n - k ≤ (u i).val)).card := hhalved
      _ = (ε : ℝ) * ↑a := by rw [← ha_eq]

end Paterson
