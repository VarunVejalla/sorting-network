import Round2Col
import Round2Det
import Pushforward

/-! # Round 2 for a fixed output set `S` and base row `b` (ROUND2.md §3–§5)

`#{σ : x ≤ Σ_j Y_j^{S,b}(λ)} ≤ e^{-t x} · M^n · #Scramble`, with the column moment
`M = Lb t α δ + Lb t β δ - 1`, from the pushforward to row subsets, the flip of the backward
rows, negative association across columns and the one-column bound. -/

open Finset BigOperators Chvatal

namespace Round2Fixed

variable {m n : ℕ}

open Round2Col

theorem walkN_eq_Nω (σ : Scramble m n) (S : Finset (Fin n)) (j : Fin n) (h : ℕ) :
    Round2.walkN σ S j h = Nω (fun r => Push.rowSet (σ r) S) j h := by
  classical
  simp only [Round2.walkN, Nω, Push.rowSet, Finset.mem_filter, Finset.mem_univ, true_and]

theorem Ydual_eq_Yω (σ : Scramble m n) (S : Finset (Fin n)) (j : Fin n) (b : ℕ) (lam : ℝ) :
    Round2.Ydual σ S j b lam = Yω ((S.card : ℝ) / n) lam (fun r => Push.rowSet (σ r) S) j b := by
  simp only [Round2.Ydual, Yω, Round2.walkW, Wω, walkN_eq_Nω]

theorem bit_inter_self (j : Fin n) (T : Finset (Fin n)) : bit j (T ∩ {j}) = bit j T := by
  classical
  by_cases h : j ∈ T <;> simp [bit, h]

theorem Dfwd_inter (p lam : ℝ) (j : Fin n) (b : ℕ) (r : Fin m) (T : Finset (Fin n)) :
    Dfwd p lam j b r (T ∩ {j}) = Dfwd p lam j b r T := by
  simp [Dfwd, bit_inter_self]

theorem Dbwd_inter (p lam : ℝ) (j : Fin n) (b : ℕ) (r : Fin m) (T : Finset (Fin n)) :
    Dbwd p lam j b r (T ∩ {j}) = Dbwd p lam j b r T := by
  simp [Dbwd, bit_inter_self]

theorem Yplus_inter (p lam : ℝ) (j : Fin n) (b : ℕ) (ζ : Fin m → Finset (Fin n)) :
    Yplus p lam j b (fun r => ζ r ∩ {j}) = Yplus p lam j b ζ := by
  simp only [Yplus, Ville.prefixSum, Dfwd_inter]

theorem Yminus_inter (p lam : ℝ) (j : Fin n) (b : ℕ) (ζ : Fin m → Finset (Fin n)) :
    Yminus p lam j b (fun r => ζ r ∩ {j}) = Yminus p lam j b ζ := by
  simp only [Yminus, Ville.prefixSum, Dbwd_inter]

theorem bit_mono (j : Fin n) {T T' : Finset (Fin n)} (h : T ⊆ T') : bit j T ≤ bit j T' := by
  classical
  by_cases h1 : j ∈ T
  · simp [bit, h1, h h1]
  · by_cases h2 : j ∈ T' <;> simp [bit, h1, h2]

theorem Yplus_mono (p lam : ℝ) (j : Fin n) (b : ℕ) :
    Monotone (Yplus (m := m) p lam j b) := by
  intro y y' hy
  apply Finset.sup'_mono_fun
  intro h _
  simp only [Ville.prefixSum]
  refine Finset.sum_le_sum fun r _ => ?_
  split_ifs
  · simp only [Dfwd]; split_ifs
    · linarith [bit_mono j (hy (Fin.rev r))]
    · exact le_rfl
  · exact le_rfl

theorem Yminus_mono (p lam : ℝ) (j : Fin n) (b : ℕ) :
    Monotone (Yminus (m := m) p lam j b) := by
  intro y y' hy
  apply Finset.sup'_mono_fun
  intro h _
  simp only [Ville.prefixSum]
  refine Finset.sum_le_sum fun r _ => ?_
  split_ifs
  · simp only [Dbwd]; split_ifs
    · linarith [bit_mono j (hy r)]
    · exact le_rfl
  · exact le_rfl

theorem unflip_unflip (b : ℕ) (ζ : Fin m → Finset (Fin n)) : unflip b (unflip b ζ) = ζ := by
  funext r
  by_cases h : r.val < m - b <;> simp [unflip, h]

theorem sum_unflip (b s : ℕ) (hs : s ≤ n) (F : (Fin m → Finset (Fin n)) → ℝ) :
    ∑ ω ∈ Fintype.piFinset (fun _ : Fin m => (Finset.univ : Finset (Fin n)).powersetCard s), F ω =
      ∑ ζ ∈ Zs m b s n, F (unflip b ζ) := by
  classical
  refine (Finset.sum_nbij' (unflip b) (unflip b) ?_ ?_ ?_ ?_ ?_).symm
  · intro ζ hζ
    simp only [Zs, Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_powersetCard] at hζ ⊢
    intro r
    refine ⟨Finset.subset_univ _, ?_⟩
    have := hζ r
    by_cases h : r.val < m - b
    · simp only [unflip, if_pos h]; simpa [kflip, h] using this.2
    · simp only [unflip, if_neg h]
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
      have h2 : (ζ r).card = n - s := by simpa [kflip, h] using this.2
      omega
  · intro ω hω
    simp only [Zs, Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_powersetCard] at hω ⊢
    intro r
    refine ⟨Finset.subset_univ _, ?_⟩
    have := hω r
    by_cases h : r.val < m - b
    · simp only [unflip, if_pos h, kflip]; exact this.2
    · simp only [unflip, if_neg h, kflip]
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
        this.2]
  · intro ζ _; exact unflip_unflip b ζ
  · intro ω _; exact unflip_unflip b ω
  · intro ζ _; rfl

theorem card_Zs_nat (b s : ℕ) (hs : s ≤ n) : (Zs m b s n).card = (n.choose s) ^ m := by
  rw [Zs, Fintype.card_piFinset]
  have : ∀ r : Fin m, ((Finset.univ : Finset (Fin n)).powersetCard (kflip m b s n r)).card =
      n.choose s := by
    intro r
    rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
    simp only [kflip]
    split_ifs
    · rfl
    · exact Nat.choose_symm hs
  rw [Finset.prod_congr rfl fun r _ => this r, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem card_Zs (b s : ℕ) (hs : s ≤ n) : ((Zs m b s n).card : ℝ) = ((n.choose s : ℕ) : ℝ) ^ m := by
  rw [card_Zs_nat b s hs]; push_cast; ring

theorem card_scramble_eq (s : ℕ) (hs : s ≤ n) :
    ((Fintype.card (Scramble m n) : ℕ) : ℝ) =
      ((s.factorial * (n - s).factorial : ℕ) : ℝ) ^ m * ((n.choose s : ℕ) : ℝ) ^ m := by
  rw [card_scramble, Fintype.card_perm, Fintype.card_fin, ← mul_pow]
  push_cast
  congr 1
  have := Nat.choose_mul_factorial_mul_factorial hs
  have h' : ((n.choose s : ℕ) : ℝ) * (s.factorial : ℝ) * ((n - s).factorial : ℝ) = (n.factorial : ℝ) := by
    exact_mod_cast this
  linarith

/-- **Fixed `S`, `b`: the exponential moment of `Σ_j Y_j`.** -/
theorem fixed_mgf (S : Finset (Fin n)) (b : ℕ) (hb : b ≤ m) (hn : 0 < n)
    (lam t α β δ : ℝ) (ht : 0 ≤ t) (hδ : 0 < δ) (htα : t < α) (htβ : t < β)
    (hα : 1 - (S.card : ℝ) / n + (S.card : ℝ) / n * Real.exp α ≤
      Real.exp (α * ((S.card : ℝ) / n + lam)))
    (hβ : 1 - (1 - (S.card : ℝ) / n) + (1 - (S.card : ℝ) / n) * Real.exp β ≤
      Real.exp (β * ((1 - (S.card : ℝ) / n) + lam))) :
    ∑ σ : Scramble m n, Real.exp (t * ∑ j : Fin n, Round2.Ydual σ S j b lam) ≤
      ((Fintype.card (Scramble m n) : ℕ) : ℝ) * (Lb t α δ + Lb t β δ - 1) ^ n := by
  classical
  set s := S.card
  have hs : s ≤ n := by simpa [s] using Finset.card_le_univ S
  set p : ℝ := (s : ℝ) / n
  set Mc := Lb t α δ + Lb t β δ - 1
  set N : ℝ := ((Zs m b s n).card : ℝ)
  have hN0 : 0 < N := by
    rw [show N = ((n.choose s : ℕ) : ℝ) ^ m from card_Zs b s hs]
    apply pow_pos; exact_mod_cast Nat.choose_pos hs
  let φ : Fin n → (Fin m → Finset (Fin n)) → ℝ := fun j y =>
    Real.exp (t * max (Yplus p lam j b y) (Yminus p lam j b y))
  have hφ0 : ∀ j y, 0 ≤ φ j y := fun j y => (Real.exp_pos _).le
  have hφm : ∀ j, Monotone (φ j) := fun j y y' hy =>
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left
      (max_le_max (Yplus_mono p lam j b hy) (Yminus_mono p lam j b hy)) ht)
  have hφinter : ∀ j ζ, φ j (fun r => ζ r ∩ ({j} : Finset (Fin n))) =
      Real.exp (t * max (Yplus p lam j b ζ) (Yminus p lam j b ζ)) := fun j ζ => by
    simp only [φ, Yplus_inter, Yminus_inter]
  -- step 1: pushforward and flip
  have h1 : ∑ σ : Scramble m n, Real.exp (t * ∑ j : Fin n, Round2.Ydual σ S j b lam) =
      ((s.factorial * (n - s).factorial : ℕ) : ℝ) ^ m *
        ∑ ζ ∈ Zs m b s n, Real.exp (t * ∑ j : Fin n, Yω p lam (unflip b ζ) j b) := by
    simp_rw [Ydual_eq_Yω]
    rw [Push.sum_scramble_rowSets S (fun ω => Real.exp (t * ∑ j : Fin n, Yω p lam ω j b)),
      sum_unflip b s hs]
  -- step 2: pointwise by the product of column factors
  have h2 : ∀ ζ ∈ Zs m b s n, Real.exp (t * ∑ j : Fin n, Yω p lam (unflip b ζ) j b) ≤
      ∏ j : Fin n, φ j (fun r => ζ r ∩ ({j} : Finset (Fin n))) := by
    intro ζ _
    simp_rw [hφinter]
    rw [← Real.exp_sum]
    apply Real.exp_le_exp.2
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_left (Yω_le_max p lam j b hb ζ) ht
  -- step 3: negative association and the column bound
  have hNA := NegAssoc.neg_assoc_prod (Finset.univ : Finset (Fin n)) m (kflip m b s n)
    (fun j : Fin n => ({j} : Finset (Fin n))) φ hφ0 hφm Finset.univ
    (fun j _ => Finset.subset_univ _)
    (by
      intro x _ y _ hxy
      simp only [Function.onFun]
      exact Finset.disjoint_singleton.2 hxy)
  have hcol : ∀ j : Fin n, ∑ ζ ∈ Zs m b s n, φ j (fun r => ζ r ∩ ({j} : Finset (Fin n))) ≤ N * Mc := by
    intro j
    simp_rw [hφinter]
    exact column_mgf b s hb hs hn j lam t α β δ ht hδ htα htβ hα hβ
  have hprod : ∏ j : Fin n, ∑ ζ ∈ Zs m b s n, φ j (fun r => ζ r ∩ ({j} : Finset (Fin n))) ≤
      (N * Mc) ^ n := by
    calc ∏ j : Fin n, ∑ ζ ∈ Zs m b s n, φ j (fun r => ζ r ∩ ({j} : Finset (Fin n)))
        ≤ ∏ _j : Fin n, (N * Mc) :=
          Finset.prod_le_prod (fun j _ => Finset.sum_nonneg fun ζ _ => hφ0 j _) (fun j _ => hcol j)
      _ = (N * Mc) ^ n := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hsumprod : ∑ ζ ∈ Zs m b s n, ∏ j : Fin n, φ j (fun r => ζ r ∩ ({j} : Finset (Fin n))) ≤
      N * Mc ^ n := by
    have hNA' : N ^ n * ∑ ζ ∈ Zs m b s n, ∏ j : Fin n, φ j (fun r => ζ r ∩ ({j} : Finset (Fin n))) ≤
        N * (N * Mc) ^ n := by
      have := hNA
      simp only [Finset.card_univ, Fintype.card_fin] at this
      exact this.trans (mul_le_mul_of_nonneg_left hprod hN0.le)
    have hpos : 0 < N ^ n := pow_pos hN0 n
    rw [mul_pow, ← mul_assoc, show N * N ^ n = N ^ n * N by ring, mul_assoc] at hNA'
    exact le_of_mul_le_mul_left hNA' hpos
  calc ∑ σ : Scramble m n, Real.exp (t * ∑ j : Fin n, Round2.Ydual σ S j b lam)
      = ((s.factorial * (n - s).factorial : ℕ) : ℝ) ^ m *
          ∑ ζ ∈ Zs m b s n, Real.exp (t * ∑ j : Fin n, Yω p lam (unflip b ζ) j b) := h1
    _ ≤ ((s.factorial * (n - s).factorial : ℕ) : ℝ) ^ m *
          ∑ ζ ∈ Zs m b s n, ∏ j : Fin n, φ j (fun r => ζ r ∩ ({j} : Finset (Fin n))) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum h2) (by positivity)
    _ ≤ ((s.factorial * (n - s).factorial : ℕ) : ℝ) ^ m * (N * Mc ^ n) :=
        mul_le_mul_of_nonneg_left hsumprod (by positivity)
    _ = ((Fintype.card (Scramble m n) : ℕ) : ℝ) * Mc ^ n := by
        rw [card_scramble_eq s hs, show N = ((n.choose s : ℕ) : ℝ) ^ m from card_Zs b s hs]
        ring

/-- **Fixed `S`, `b`: failure count (Markov).** -/
theorem fixed_fail (S : Finset (Fin n)) (b : ℕ) (hb : b ≤ m) (hn : 0 < n)
    (lam t α β δ x : ℝ) (ht : 0 ≤ t) (hδ : 0 < δ) (htα : t < α) (htβ : t < β)
    (hα : 1 - (S.card : ℝ) / n + (S.card : ℝ) / n * Real.exp α ≤
      Real.exp (α * ((S.card : ℝ) / n + lam)))
    (hβ : 1 - (1 - (S.card : ℝ) / n) + (1 - (S.card : ℝ) / n) * Real.exp β ≤
      Real.exp (β * ((1 - (S.card : ℝ) / n) + lam))) :
    ((Finset.univ.filter fun σ : Scramble m n => x ≤ ∑ j : Fin n, Round2.Ydual σ S j b lam).card : ℝ) ≤
      Real.exp (-(t * x)) * ((Fintype.card (Scramble m n) : ℕ) : ℝ) *
        (Lb t α δ + Lb t β δ - 1) ^ n := by
  classical
  have hm := fixed_mgf S b hb hn lam t α β δ ht hδ htα htβ hα hβ
  set B := Finset.univ.filter fun σ : Scramble m n => x ≤ ∑ j : Fin n, Round2.Ydual σ S j b lam
  have hmark : Real.exp (t * x) * (B.card : ℝ) ≤
      ∑ σ : Scramble m n, Real.exp (t * ∑ j : Fin n, Round2.Ydual σ S j b lam) := by
    calc Real.exp (t * x) * (B.card : ℝ) = ∑ σ ∈ B, Real.exp (t * x) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ ∑ σ ∈ B, Real.exp (t * ∑ j : Fin n, Round2.Ydual σ S j b lam) :=
          Finset.sum_le_sum fun σ hσ => Real.exp_le_exp.2
            (mul_le_mul_of_nonneg_left (Finset.mem_filter.1 hσ).2 ht)
      _ ≤ ∑ σ : Scramble m n, Real.exp (t * ∑ j : Fin n, Round2.Ydual σ S j b lam) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun _ _ _ => (Real.exp_pos _).le)
  have hpos : 0 < Real.exp (t * x) := Real.exp_pos _
  have := hmark.trans hm
  rw [show Real.exp (-(t * x)) = (Real.exp (t * x))⁻¹ from Real.exp_neg _]
  rw [mul_assoc, ← div_eq_inv_mul, le_div_iff₀ hpos]
  linarith

end Round2Fixed
