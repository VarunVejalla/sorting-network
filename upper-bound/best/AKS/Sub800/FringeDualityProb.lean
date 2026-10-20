import AKS.Sub800.FringeDualityDet
import AKS.Sub800.FringeDualityTail
import AKS.Sub800.Round2Fixed

/-! # Fringe by double weak duality: the probability step for a fixed output set (UB-34)

For a fixed set `S` of output columns and a cost `φ ≥ 0` (linear for round 1, convex for round 2),
the walks `walkYφ σ (ind S) φ j` are, after pushing the uniform scramble forward to independent
uniform `|S|`-subsets per row (`Push.sum_scramble_rowSets`), the walk maxima `Yz φ ζ j` of the
subset model. They are monotone in the subsets and depend on column `j` only, so negative
association (`NegAssoc.neg_assoc_prod`) bounds the moment of their sum by the product of column
moments (`fixed_mgf_cost`); Markov gives the failure count (`fixed_fail_cost`). The column moment
comes from `card_Yz_gt_le_exp` and `sum_exp_le_layer`. -/

open Finset BigOperators Chvatal

namespace FringeDuality

variable {m n : ℕ}

theorem walkA_ind_eq (σ : Scramble m n) (S : Finset (Fin n)) (j : Fin n) (h : ℕ) :
    walkA σ (ind S) j h = (Nz (fun r => Push.rowSet (σ r) S) j h : ℝ) := by
  classical
  unfold walkA Nz ind
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one,
    Finset.filter_filter]
  congr 2
  ext r
  simp [Push.rowSet]

theorem walkYφ_ind_eq (σ : Scramble m n) (S : Finset (Fin n)) (φ : ℕ → ℝ) (j : Fin n) :
    walkYφ σ (ind S) φ j = Yz φ (fun r => Push.rowSet (σ r) S) j := by
  unfold walkYφ Yz
  simp_rw [walkA_ind_eq]

theorem Nz_mono_sets {ζ ζ' : Fin m → Finset (Fin n)} (hζ : ζ ≤ ζ') (j : Fin n) (h : ℕ) :
    Nz ζ j h ≤ Nz ζ' j h := by
  apply Finset.card_le_card
  intro r hr
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
  exact ⟨hr.1, hζ r hr.2⟩

theorem Yz_mono (D : ℕ → ℝ) (j : Fin n) : Monotone (fun ζ : Fin m → Finset (Fin n) => Yz D ζ j) := by
  intro ζ ζ' hζ
  unfold Yz
  apply Finset.sup'_le
  intro h hh
  refine le_trans ?_ (Finset.le_sup' (fun h => (Nz ζ' j h : ℝ) - D h) hh)
  have : (Nz ζ j h : ℝ) ≤ Nz ζ' j h := by exact_mod_cast Nz_mono_sets hζ j h
  linarith

theorem Nz_inter (ζ : Fin m → Finset (Fin n)) (j : Fin n) (h : ℕ) :
    Nz (fun r => ζ r ∩ ({j} : Finset (Fin n))) j h = Nz ζ j h := by
  unfold Nz
  congr 1
  ext r
  simp

theorem Yz_inter (D : ℕ → ℝ) (ζ : Fin m → Finset (Fin n)) (j : Fin n) :
    Yz D (fun r => ζ r ∩ ({j} : Finset (Fin n))) j = Yz D ζ j := by
  unfold Yz
  simp_rw [Nz_inter]

/-- **Fixed `S`: the moment of `Σ_j Y_j(1_S, φ)` from a column moment bound.** -/
theorem fixed_mgf_cost (S : Finset (Fin n)) (φ : ℕ → ℝ) (t Mc : ℝ) (ht : 0 ≤ t)
    (hcol0 : ∀ j : Fin n,
      ∑ ζ ∈ Fintype.piFinset (fun _ : Fin m => (Finset.univ : Finset (Fin n)).powersetCard S.card),
        Real.exp (t * Yz φ ζ j) ≤
      ((Fintype.piFinset (fun _ : Fin m => (Finset.univ : Finset (Fin n)).powersetCard S.card)).card : ℝ) *
        Mc) :
    ∑ σ : Scramble m n, Real.exp (t * ∑ j : Fin n, walkYφ σ (ind S) φ j) ≤
      ((Fintype.card (Scramble m n) : ℕ) : ℝ) * Mc ^ n := by
  classical
  set s := S.card
  have hs : s ≤ n := by simpa [s] using Finset.card_le_univ S
  set Z := Fintype.piFinset (fun _ : Fin m => (Finset.univ : Finset (Fin n)).powersetCard s)
  set N : ℝ := (Z.card : ℝ)
  have hZ : Z = Round2Col.Zs m 0 s n := by
    simp only [Z, Round2Col.Zs, Round2Col.kflip]
    congr 1
    funext r
    simp
  have hN0 : 0 < N := by
    rw [show N = ((n.choose s : ℕ) : ℝ) ^ m by
      simp only [N]; rw [hZ]; exact Round2Fixed.card_Zs 0 s hs]
    apply pow_pos; exact_mod_cast Nat.choose_pos hs
  let ψ : Fin n → (Fin m → Finset (Fin n)) → ℝ := fun j y => Real.exp (t * Yz φ y j)
  have hψ0 : ∀ j y, 0 ≤ ψ j y := fun j y => (Real.exp_pos _).le
  have hψm : ∀ j, Monotone (ψ j) := fun j y y' hy =>
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (Yz_mono φ j hy) ht)
  have hψinter : ∀ j ζ, ψ j (fun r => ζ r ∩ ({j} : Finset (Fin n))) = Real.exp (t * Yz φ ζ j) :=
    fun j ζ => by simp only [ψ, Yz_inter]
  -- step 1: pushforward
  have h1 : ∑ σ : Scramble m n, Real.exp (t * ∑ j : Fin n, walkYφ σ (ind S) φ j) =
      ((s.factorial * (n - s).factorial : ℕ) : ℝ) ^ m *
        ∑ ζ ∈ Z, Real.exp (t * ∑ j : Fin n, Yz φ ζ j) := by
    simp_rw [walkYφ_ind_eq]
    exact Push.sum_scramble_rowSets S (fun ω => Real.exp (t * ∑ j : Fin n, Yz φ ω j))
  -- step 2: the exponential of the sum is the product of column factors
  have h2 : ∀ ζ ∈ Z, Real.exp (t * ∑ j : Fin n, Yz φ ζ j) =
      ∏ j : Fin n, ψ j (fun r => ζ r ∩ ({j} : Finset (Fin n))) := by
    intro ζ _
    simp_rw [hψinter]
    rw [← Real.exp_sum, Finset.mul_sum]
  -- step 3: negative association
  have hNA := NegAssoc.neg_assoc_prod (Finset.univ : Finset (Fin n)) m (fun _ => s)
    (fun j : Fin n => ({j} : Finset (Fin n))) ψ hψ0 hψm Finset.univ
    (fun j _ => Finset.subset_univ _)
    (by
      intro x _ y _ hxy
      simp only [Function.onFun]
      exact Finset.disjoint_singleton.2 hxy)
  have hcol : ∀ j : Fin n, ∑ ζ ∈ Z, ψ j (fun r => ζ r ∩ ({j} : Finset (Fin n))) ≤ N * Mc := by
    intro j
    simp_rw [hψinter]
    exact hcol0 j
  have hprod : ∏ j : Fin n, ∑ ζ ∈ Z, ψ j (fun r => ζ r ∩ ({j} : Finset (Fin n))) ≤ (N * Mc) ^ n := by
    calc ∏ j : Fin n, ∑ ζ ∈ Z, ψ j (fun r => ζ r ∩ ({j} : Finset (Fin n)))
        ≤ ∏ _j : Fin n, (N * Mc) :=
          Finset.prod_le_prod (fun j _ => Finset.sum_nonneg fun ζ _ => hψ0 j _) (fun j _ => hcol j)
      _ = (N * Mc) ^ n := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hsumprod : ∑ ζ ∈ Z, ∏ j : Fin n, ψ j (fun r => ζ r ∩ ({j} : Finset (Fin n))) ≤ N * Mc ^ n := by
    have hNA' : N ^ n * ∑ ζ ∈ Z, ∏ j : Fin n, ψ j (fun r => ζ r ∩ ({j} : Finset (Fin n))) ≤
        N * (N * Mc) ^ n := by
      have := hNA
      simp only [Finset.card_univ, Fintype.card_fin] at this
      exact this.trans (mul_le_mul_of_nonneg_left hprod hN0.le)
    have hpos : 0 < N ^ n := pow_pos hN0 n
    rw [mul_pow, ← mul_assoc, show N * N ^ n = N ^ n * N by ring, mul_assoc] at hNA'
    exact le_of_mul_le_mul_left hNA' hpos
  calc ∑ σ : Scramble m n, Real.exp (t * ∑ j : Fin n, walkYφ σ (ind S) φ j)
      = ((s.factorial * (n - s).factorial : ℕ) : ℝ) ^ m *
          ∑ ζ ∈ Z, Real.exp (t * ∑ j : Fin n, Yz φ ζ j) := h1
    _ = ((s.factorial * (n - s).factorial : ℕ) : ℝ) ^ m *
          ∑ ζ ∈ Z, ∏ j : Fin n, ψ j (fun r => ζ r ∩ ({j} : Finset (Fin n))) := by
        rw [Finset.sum_congr rfl h2]
    _ ≤ ((s.factorial * (n - s).factorial : ℕ) : ℝ) ^ m * (N * Mc ^ n) :=
        mul_le_mul_of_nonneg_left hsumprod (by positivity)
    _ = ((Fintype.card (Scramble m n) : ℕ) : ℝ) * Mc ^ n := by
        rw [Round2Fixed.card_scramble_eq s hs, show N = ((n.choose s : ℕ) : ℝ) ^ m by
          simp only [N]; rw [hZ]; exact Round2Fixed.card_Zs 0 s hs]
        ring

/-- **Fixed `S`: failure count (Markov).** -/
theorem fixed_fail_cost (S : Finset (Fin n)) (φ : ℕ → ℝ) (t x K : ℝ) (ht : 0 ≤ t)
    (hm : ∑ σ : Scramble m n, Real.exp (t * ∑ j : Fin n, walkYφ σ (ind S) φ j) ≤ K) :
    ((Finset.univ.filter fun σ : Scramble m n => x ≤ ∑ j : Fin n, walkYφ σ (ind S) φ j).card : ℝ) ≤
      Real.exp (-(t * x)) * K := by
  classical
  set B := Finset.univ.filter fun σ : Scramble m n => x ≤ ∑ j : Fin n, walkYφ σ (ind S) φ j
  have hmark : Real.exp (t * x) * (B.card : ℝ) ≤
      ∑ σ : Scramble m n, Real.exp (t * ∑ j : Fin n, walkYφ σ (ind S) φ j) := by
    calc Real.exp (t * x) * (B.card : ℝ) = ∑ σ ∈ B, Real.exp (t * x) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ ∑ σ ∈ B, Real.exp (t * ∑ j : Fin n, walkYφ σ (ind S) φ j) :=
          Finset.sum_le_sum fun σ hσ => Real.exp_le_exp.2
            (mul_le_mul_of_nonneg_left (Finset.mem_filter.1 hσ).2 ht)
      _ ≤ ∑ σ : Scramble m n, Real.exp (t * ∑ j : Fin n, walkYφ σ (ind S) φ j) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun _ _ _ => (Real.exp_pos _).le)
  have hpos : 0 < Real.exp (t * x) := Real.exp_pos _
  have := hmark.trans hm
  rw [show Real.exp (-(t * x)) = (Real.exp (t * x))⁻¹ from Real.exp_neg _, ← div_eq_inv_mul,
    le_div_iff₀ hpos]
  linarith

/-- **Union over all output sets of one size.** If every `S` with `|S| = s` fails on at most `F`
scrambles, then at most `C(n, s) · F` scrambles fail for some such `S`. -/
theorem union_sets_le (s : ℕ) (P : Finset (Fin n) → Scramble m n → Prop)
    [∀ S σ, Decidable (P S σ)] (F : ℝ)
    (hF : ∀ S : Finset (Fin n), S.card = s →
      ((Finset.univ.filter fun σ : Scramble m n => P S σ).card : ℝ) ≤ F) :
    ((Finset.univ.filter fun σ : Scramble m n =>
        ∃ S ∈ (Finset.univ : Finset (Fin n)).powersetCard s, P S σ).card : ℝ) ≤
      (n.choose s : ℝ) * F := by
  classical
  have hsub : (Finset.univ.filter fun σ : Scramble m n =>
      ∃ S ∈ (Finset.univ : Finset (Fin n)).powersetCard s, P S σ) ⊆
      ((Finset.univ : Finset (Fin n)).powersetCard s).biUnion
        (fun S => Finset.univ.filter fun σ : Scramble m n => P S σ) := by
    intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    obtain ⟨S, hS, hP⟩ := hσ
    exact Finset.mem_biUnion.2 ⟨S, hS, by simpa using hP⟩
  calc ((Finset.univ.filter fun σ : Scramble m n =>
        ∃ S ∈ (Finset.univ : Finset (Fin n)).powersetCard s, P S σ).card : ℝ)
      ≤ ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard s,
          ((Finset.univ.filter fun σ : Scramble m n => P S σ).card : ℝ) := by
        exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    _ ≤ ∑ _S ∈ (Finset.univ : Finset (Fin n)).powersetCard s, F :=
        Finset.sum_le_sum fun S hS => hF S (Finset.mem_powersetCard.1 hS).2
    _ = (n.choose s : ℝ) * F := by
        rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]

end FringeDuality
