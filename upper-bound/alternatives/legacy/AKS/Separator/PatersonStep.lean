module

public import AKS.Separator.PatersonNear

/-! # Supported-range separator induction for even local chunks -/

@[expose] public section

namespace Paterson

/-- A restricted halver refines a supported-range separator on even chunks.
The support budget is measured against the local half-chunk size; no
full-range halver hypothesis is used. -/
theorem supported_halving_step {n : ℕ} {ε α : ℚ} {μ e : ℝ} (t : ℕ)
    {net : ComparatorNetwork n}
    {halvers : (m : ℕ) → ComparatorNetwork (2 * m)}
    (hsep : IsSupportedSeparator net (n / 2 ^ t) μ e)
    (hhalver : IsEpsilonAlphaHalver (halvers ((n / 2 ^ t) / 2)) ε α)
    (hε : 0 ≤ ε)
    (h_even : 2 ∣ n / 2 ^ t) (h_pow_div : 2 ^ t ∣ n)
    (hsupport : μ * n ≤ (α : ℝ) * ↑(n / 2 ^ t / 2)) :
    IsSupportedSeparator
      (⟨net.comparators ++ (halverAtLevel n halvers t).comparators⟩ :
        ComparatorNetwork n)
      (n / 2 ^ (t + 1)) μ (e + ε) := by
  intro v
  obtain ⟨hbase_initial, hbase_final⟩ := hsep v
  set w₁ := net.exec (v : Fin n → Fin n) with hw₁_def
  have hw₁_inj : Function.Injective w₁ :=
    ComparatorNetwork.exec_injective net (Equiv.injective v)
  set w₂ := (halverAtLevel n halvers t).exec w₁ with hw₂_def
  set C := n / 2 ^ t with hC_def
  set H := C / 2 with hH_def
  have hH_eq : H = n / 2 ^ (t + 1) := by
    simpa only [H, C] using half_chunk_eq n t
  have hC_le_n : C ≤ n := Nat.div_le_self n _
  have hH_le_C : H ≤ C := Nat.div_le_self C 2
  have hlocal (k : ℕ) (hk : (k : ℝ) ≤ μ * n) :
      (k : ℝ) ≤ (α : ℝ) * H := hk.trans hsupport
  rw [ComparatorNetwork.exec_append, ← hH_eq]
  change
    (∀ k : ℕ, (k : ℝ) ≤ μ * n →
      ((Finset.univ.filter (fun pos : Fin n ↦
        H ≤ pos.val ∧ (w₂ pos).val < k)).card : ℝ) ≤ (e + ε) * k) ∧
    (∀ k : ℕ, (k : ℝ) ≤ μ * n →
      ((Finset.univ.filter (fun pos : Fin n ↦
        pos.val < n - H ∧ n - k ≤ (w₂ pos).val)).card : ℝ) ≤ (e + ε) * k)
  constructor
  · intro k hk
    have hpart : (Finset.univ.filter (fun pos : Fin n ↦
        H ≤ pos.val ∧ (w₂ pos).val < k)).card =
      (Finset.univ.filter (fun pos : Fin n ↦
        H ≤ pos.val ∧ pos.val < C ∧ (w₂ pos).val < k)).card +
      (Finset.univ.filter (fun pos : Fin n ↦
        C ≤ pos.val ∧ (w₂ pos).val < k)).card := by
      rw [← Finset.card_union_of_disjoint]
      · congr 1; ext pos
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
        constructor
        · intro ⟨hge, hval⟩
          by_cases hpos : pos.val < C
          · exact Or.inl ⟨hge, hpos, hval⟩
          · exact Or.inr ⟨by omega, hval⟩
        · rintro (⟨hge, _, hval⟩ | ⟨hge, hval⟩)
          · exact ⟨hge, hval⟩
          · exact ⟨hH_le_C.trans hge, hval⟩
      · rw [Finset.disjoint_filter]
        intro pos _ ⟨_, hlt, _⟩ ⟨hge, _⟩; omega
    have hnear : ((Finset.univ.filter (fun pos : Fin n ↦
        H ≤ pos.val ∧ pos.val < C ∧ (w₂ pos).val < k)).card : ℝ) ≤
        (ε : ℝ) * ↑(Finset.univ.filter (fun pos : Fin n ↦
          pos.val < C ∧ (w₁ pos).val < k)).card := by
      rw [hw₂_def]
      exact restricted_near_initial t w₁ hw₁_inj hhalver hε h_even k (hlocal k hk)
    have hfar : (Finset.univ.filter (fun pos : Fin n ↦
        C ≤ pos.val ∧ (w₂ pos).val < k)).card =
      (Finset.univ.filter (fun pos : Fin n ↦
        C ≤ pos.val ∧ (w₁ pos).val < k)).card := by
      rw [hw₂_def]
      exact far_outsider_count_preserved t w₁ hw₁_inj k
    have hbase : ((Finset.univ.filter (fun pos : Fin n ↦
        C ≤ pos.val ∧ (w₁ pos).val < k)).card : ℝ) ≤ e * k := by
      simpa only [hC_def, hw₁_def] using hbase_initial k hk
    have ha : ((Finset.univ.filter (fun pos : Fin n ↦
        pos.val < C ∧ (w₁ pos).val < k)).card : ℝ) ≤ k := by
      have hh : (Finset.univ.filter (fun pos : Fin n ↦
          pos.val < C ∧ (w₁ pos).val < k)).card ≤ k := by
        calc
          _ ≤ (Finset.univ.filter (fun pos : Fin n ↦ (w₁ pos).val < k)).card := by
            apply Finset.card_le_card
            intro pos; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            exact And.right
          _ ≤ k := injective_count_lt_le w₁ hw₁_inj k
      exact_mod_cast hh
    have hεreal : (0 : ℝ) ≤ ε := by exact_mod_cast hε
    rw [hpart]
    push_cast
    rw [hfar]
    nlinarith [mul_le_mul_of_nonneg_left ha hεreal]
  · intro k hk
    have hpart : (Finset.univ.filter (fun pos : Fin n ↦
        pos.val < n - H ∧ n - k ≤ (w₂ pos).val)).card =
      (Finset.univ.filter (fun pos : Fin n ↦
        n - C ≤ pos.val ∧ pos.val < n - H ∧ n - k ≤ (w₂ pos).val)).card +
      (Finset.univ.filter (fun pos : Fin n ↦
        pos.val < n - C ∧ n - k ≤ (w₂ pos).val)).card := by
      rw [← Finset.card_union_of_disjoint]
      · congr 1; ext pos
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
        constructor
        · intro ⟨hlt, hval⟩
          by_cases hpos : n - C ≤ pos.val
          · exact Or.inl ⟨hpos, hlt, hval⟩
          · exact Or.inr ⟨by omega, hval⟩
        · rintro (⟨_, hlt, hval⟩ | ⟨hlt, hval⟩)
          · exact ⟨hlt, hval⟩
          · exact ⟨by omega, hval⟩
      · rw [Finset.disjoint_filter]
        intro pos _ ⟨hge, _, _⟩ ⟨hlt, _⟩; omega
    have hnear : ((Finset.univ.filter (fun pos : Fin n ↦
        n - C ≤ pos.val ∧ pos.val < n - H ∧ n - k ≤ (w₂ pos).val)).card : ℝ) ≤
        (ε : ℝ) * ↑(Finset.univ.filter (fun pos : Fin n ↦
          n - C ≤ pos.val ∧ n - k ≤ (w₁ pos).val)).card := by
      rw [hw₂_def]
      exact restricted_near_final t w₁ hw₁_inj hhalver hε h_even h_pow_div k (hlocal k hk)
    have hfar : (Finset.univ.filter (fun pos : Fin n ↦
        pos.val < n - C ∧ n - k ≤ (w₂ pos).val)).card =
      (Finset.univ.filter (fun pos : Fin n ↦
        pos.val < n - C ∧ n - k ≤ (w₁ pos).val)).card := by
      rw [hw₂_def]
      exact far_outsider_count_preserved_final t h_pow_div w₁ hw₁_inj (n - k)
    have hbase : ((Finset.univ.filter (fun pos : Fin n ↦
        pos.val < n - C ∧ n - k ≤ (w₁ pos).val)).card : ℝ) ≤ e * k := by
      simpa only [hC_def, hw₁_def] using hbase_final k hk
    have ha : ((Finset.univ.filter (fun pos : Fin n ↦
        n - C ≤ pos.val ∧ n - k ≤ (w₁ pos).val)).card : ℝ) ≤ k := by
      have hh : (Finset.univ.filter (fun pos : Fin n ↦
          n - C ≤ pos.val ∧ n - k ≤ (w₁ pos).val)).card ≤ k := by
        calc
          _ ≤ (Finset.univ.filter (fun pos : Fin n ↦ n - k ≤ (w₁ pos).val)).card := by
            apply Finset.card_le_card
            intro pos; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            exact And.right
          _ ≤ k := injective_count_ge_le w₁ hw₁_inj k
      exact_mod_cast hh
    have hεreal : (0 : ℝ) ≤ ε := by exact_mod_cast hε
    rw [hpart]
    push_cast
    rw [hfar]
    nlinarith [mul_le_mul_of_nonneg_left ha hεreal]

end Paterson
