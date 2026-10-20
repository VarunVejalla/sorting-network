import AKS.Sub800.RowMgf
import AKS.Sub800.Round2Union
import Mathlib.Tactic

/-! # Fringe by double weak duality: level crossing (UB-34)

The sparse-regime tail of a walk maximum `Y = max_h (N(h) − D(h))`, with `N` a nondecreasing count
and `D` a nondecreasing drift, is controlled by the times at which the count first reaches each level:
if `Y > y`, then some level `k > y` is reached by height `T`, where `T` is any height beyond which
`D ≥ k − y`. `level_crossing` states this deterministically, so a union bound over `k` reduces the
tail to binomial tails `P(N(T_k) ≥ k)`. -/

namespace FringeDuality

/-- **Level crossing.** If `N` is monotone, `D` is monotone, and `N h − D h > y` for some `h ≤ H`,
then for `k = N h` we have `y < k` and, for every `T` with `D h < k − y → h ≤ T` (in particular for `T`
the last height with `D T < k − y`), `k ≤ N T`. -/
theorem level_crossing (N : ℕ → ℕ) (D : ℕ → ℝ) (hN : Monotone N) (hD0 : ∀ h, 0 ≤ D h) (y : ℝ)
    (h : ℕ) (hy : y < (N h : ℝ) - D h) (T : ℕ) (hT : ∀ h', D h' < (N h : ℝ) - y → h' ≤ T) :
    y < (N h : ℝ) ∧ N h ≤ N T := by
  have hD : D h < (N h : ℝ) - y := by linarith
  exact ⟨by linarith [hD0 h], hN (hT h hD)⟩

/-- The union form: `Y > y` implies that some level `k ∈ (y, K]` is reached by its deadline `T k`,
where the deadline satisfies `D h' < k − y → h' ≤ T k`. -/
theorem exists_level_of_gt (N : ℕ → ℕ) (D : ℕ → ℝ) (hN : Monotone N) (hD0 : ∀ h, 0 ≤ D h)
    (y : ℝ) (h : ℕ) (hy : y < (N h : ℝ) - D h) (T : ℕ → ℕ)
    (hT : ∀ (k : ℕ) (h' : ℕ), D h' < (k : ℝ) - y → h' ≤ T k) :
    ∃ k : ℕ, y < (k : ℝ) ∧ k ≤ N (T k) :=
  ⟨N h, level_crossing N D hN hD0 y h hy (T (N h)) (hT (N h))⟩

open Finset in
/-- **Chernoff for the hit count of one column.** Over independent rows, each a uniform `s`-subset
of the `n` output columns, the number `N` of rows in `R` whose subset contains the column `j`
satisfies `#{ζ : k ≤ N} ≤ e^{−θk} · Π_{r ∈ R} (1 − p + p e^θ) · C(n,s)^m`, `p = s/n`, `θ ≥ 0`. -/
theorem card_hits_ge_le {m n : ℕ} (hn : 0 < n) (s : ℕ) (j : Fin n) (R : Finset (Fin m)) (k : ℕ)
    (θ : ℝ) (hθ : 0 ≤ θ) :
    (((Fintype.piFinset fun _ : Fin m => (univ : Finset (Fin n)).powersetCard s).filter
        fun ζ => k ≤ (R.filter fun r => j ∈ ζ r).card).card : ℝ) ≤
      Real.exp (-(θ * k)) * (1 - (s : ℝ) / n + (s : ℝ) / n * Real.exp θ) ^ R.card *
        ((n.choose s : ℝ) ^ m) := by
  classical
  set Z := Fintype.piFinset fun _ : Fin m => (univ : Finset (Fin n)).powersetCard s
  set g : Fin m → Finset (Fin n) → ℝ := fun r T =>
    if r ∈ R then Real.exp (θ * (if j ∈ T then 1 else 0)) else 1
  -- indicator ≤ e^{θ(N − k)} = e^{−θk} Π_r g r (ζ r)
  have hpt : ∀ ζ ∈ Z, (if k ≤ (R.filter fun r => j ∈ ζ r).card then (1 : ℝ) else 0) ≤
      Real.exp (-(θ * k)) * ∏ r, g r (ζ r) := by
    intro ζ _
    have hprod : ∏ r, g r (ζ r) = Real.exp (θ * (R.filter fun r => j ∈ ζ r).card) := by
      have : ∏ r, g r (ζ r) = ∏ r, Real.exp (if r ∈ R ∧ j ∈ ζ r then θ else 0) := by
        refine Finset.prod_congr rfl fun r _ => ?_
        simp only [g]
        by_cases h1 : r ∈ R <;> by_cases h2 : j ∈ ζ r <;> simp [h1, h2]
      have hc : (univ.filter fun r => r ∈ R ∧ j ∈ ζ r) = R.filter fun r => j ∈ ζ r := by
        ext r; simp
      rw [this, ← Real.exp_sum, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
        nsmul_eq_mul, hc, mul_comm]
    rw [hprod, ← Real.exp_add]
    split_ifs with hk
    · apply Real.one_le_exp
      have : (k : ℝ) ≤ (R.filter fun r => j ∈ ζ r).card := by exact_mod_cast hk
      nlinarith
    · exact (Real.exp_pos _).le
  have hcard : ((Z.filter fun ζ => k ≤ (R.filter fun r => j ∈ ζ r).card).card : ℝ) =
      ∑ ζ ∈ Z, (if k ≤ (R.filter fun r => j ∈ ζ r).card then (1 : ℝ) else 0) := by
    rw [Finset.sum_boole]
  rw [hcard]
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [← Finset.mul_sum]
  -- factorise over rows
  have hfac : ∑ ζ ∈ Z, ∏ r, g r (ζ r) = ∏ r, ∑ T ∈ (univ : Finset (Fin n)).powersetCard s, g r T :=
    (Finset.prod_univ_sum (fun _ => (univ : Finset (Fin n)).powersetCard s) g).symm
  rw [hfac]
  have hrow : ∀ r, ∑ T ∈ (univ : Finset (Fin n)).powersetCard s, g r T =
      (n.choose s : ℝ) * (if r ∈ R then (1 - (s : ℝ) / n + (s : ℝ) / n * Real.exp θ) else 1) := by
    intro r
    by_cases hr : r ∈ R
    · have := RowMgf.sum_bit n s j hn (fun β => Real.exp (θ * (if β then 1 else 0)))
      simp only [g, hr, if_true]
      have e : ∀ T : Finset (Fin n), Real.exp (θ * (if j ∈ T then 1 else 0)) =
          Real.exp (θ * (if decide (j ∈ T) then 1 else 0)) := fun T => by
        by_cases h : j ∈ T <;> simp [h]
      simp_rw [e]
      rw [this]
      simp
    · simp only [g, hr, if_false, Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_powersetCard,
        Finset.card_univ, Fintype.card_fin]
  simp_rw [hrow]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]
  ring_nf
  exact le_refl _

section SubsetModel

variable {m n : ℕ}

open Finset

/-- Hits of column `j` in the bottom `h` rows of a row-subset family `ζ`. -/
def Nz (ζ : Fin m → Finset (Fin n)) (j : Fin n) (h : ℕ) : ℕ :=
  (univ.filter fun r : Fin m => m - h ≤ r.val ∧ j ∈ ζ r).card

theorem Nz_mono (ζ : Fin m → Finset (Fin n)) (j : Fin n) : Monotone (Nz ζ j) := by
  intro a b hab
  apply Finset.card_le_card
  intro r hr
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
  exact ⟨le_trans (Nat.sub_le_sub_left hab m) hr.1, hr.2⟩

/-- The walk maximum against a drift `D`: `max_{h ≤ m} (N(h) − D(h))`. -/
noncomputable def Yz (D : ℕ → ℝ) (ζ : Fin m → Finset (Fin n)) (j : Fin n) : ℝ :=
  (Finset.range (m + 1)).sup' ⟨0, by simp⟩ fun h => (Nz ζ j h : ℝ) - D h

/-- **Tail by level crossing** (subset model). If the deadlines `T k ≤ m` satisfy
`h ≤ m → D h < k − y → h ≤ T k`, then `#{ζ : y < Y} ≤ Σ_{k ≤ m, y < k} #{ζ : k ≤ N(T k)}`. -/
theorem card_Yz_gt_le (Z : Finset (Fin m → Finset (Fin n))) (D : ℕ → ℝ) (hD0 : ∀ h, 0 ≤ D h)
    (j : Fin n) (y : ℝ) (T : ℕ → ℕ)
    (hT : ∀ (k h : ℕ), h ≤ m → D h < (k : ℝ) - y → h ≤ T k) :
    ((Z.filter fun ζ => y < Yz D ζ j).card : ℝ) ≤
      ∑ k ∈ (Finset.range (m + 1)).filter (fun k : ℕ => y < (k : ℝ)),
        ((Z.filter fun ζ => k ≤ Nz ζ j (T k)).card : ℝ) := by
  classical
  have hsub : Z.filter (fun ζ => y < Yz D ζ j) ⊆
      ((Finset.range (m + 1)).filter (fun k : ℕ => y < (k : ℝ))).biUnion
        (fun k : ℕ => Z.filter fun ζ => k ≤ Nz ζ j (T k)) := by
    intro ζ hζ
    simp only [Finset.mem_filter] at hζ
    obtain ⟨hζZ, hy⟩ := hζ
    obtain ⟨h, hh, hval⟩ := Finset.exists_mem_eq_sup' (s := Finset.range (m + 1))
      ⟨0, Finset.mem_range.2 (Nat.succ_pos m)⟩ (fun h => (Nz ζ j h : ℝ) - D h)
    rw [Yz, hval] at hy
    have hhm : h ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hh)
    have hD : D h < (Nz ζ j h : ℝ) - y := by linarith
    have hk : y < (Nz ζ j h : ℝ) := by linarith [hD0 h]
    have hNm : Nz ζ j h ≤ m := by
      unfold Nz
      exact (Finset.card_filter_le _ _).trans (by simp)
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_range]
    exact ⟨Nz ζ j h, ⟨Nat.lt_succ_of_le hNm, hk⟩, hζZ, Nz_mono ζ j (hT _ h hhm hD)⟩
  calc ((Z.filter fun ζ => y < Yz D ζ j).card : ℝ)
      ≤ ((((Finset.range (m + 1)).filter (fun k : ℕ => y < (k : ℝ))).biUnion
          (fun k : ℕ => Z.filter fun ζ => k ≤ Nz ζ j (T k))).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ ∑ k ∈ (Finset.range (m + 1)).filter (fun k : ℕ => y < (k : ℝ)),
          ((Z.filter fun ζ => k ≤ Nz ζ j (T k)).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le

/-- Bottom `h` rows. -/
def bottomRows (m h : ℕ) : Finset (Fin m) := Finset.univ.filter fun r : Fin m => m - h ≤ r.val

theorem Nz_eq (ζ : Fin m → Finset (Fin n)) (j : Fin n) (h : ℕ) :
    Nz ζ j h = ((bottomRows m h).filter fun r => j ∈ ζ r).card := by
  unfold Nz bottomRows
  rw [Finset.filter_filter]

theorem card_bottomRows (h : ℕ) (hh : h ≤ m) : (bottomRows m h).card = h :=
  Round2Union.card_rows_top h hh

/-- **Explicit tail** (subset model, uniform `s`-subsets per row): Chernoff at every level. -/
theorem card_Yz_gt_le_exp (hn : 0 < n) (s : ℕ) (D : ℕ → ℝ) (hD0 : ∀ h, 0 ≤ D h) (j : Fin n)
    (y : ℝ) (T : ℕ → ℕ) (hTm : ∀ k, T k ≤ m)
    (hT : ∀ (k h : ℕ), h ≤ m → D h < (k : ℝ) - y → h ≤ T k) (θ : ℕ → ℝ) (hθ : ∀ k, 0 ≤ θ k) :
    (((Fintype.piFinset fun _ : Fin m => (Finset.univ : Finset (Fin n)).powersetCard s).filter
        fun ζ => y < Yz D ζ j).card : ℝ) ≤
      ∑ k ∈ (Finset.range (m + 1)).filter (fun k : ℕ => y < (k : ℝ)),
        Real.exp (-(θ k * k)) * (1 - (s : ℝ) / n + (s : ℝ) / n * Real.exp (θ k)) ^ T k *
          ((n.choose s : ℝ) ^ m) := by
  refine (card_Yz_gt_le _ D hD0 j y T hT).trans (Finset.sum_le_sum fun k _ => ?_)
  have h := card_hits_ge_le (m := m) hn s j (bottomRows m (T k)) k (θ k) (hθ k)
  rw [card_bottomRows (T k) (hTm k)] at h
  simpa only [Nz_eq] using h

/-- **Discrete layer cake.** For `0 ≤ Y ≤ y (N)` on a finite set, a nondecreasing grid `y 0 = 0`,
and `t ≥ 0`: `Σ e^{tY} ≤ |Z| + Σ_{i < N} (e^{t y(i+1)} − e^{t y(i)}) · #{Y > y i}`. -/
theorem sum_exp_le_layer {Ω : Type*} (Z : Finset Ω) (Y : Ω → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (y : ℕ → ℝ) (N : ℕ) (hy0 : y 0 = 0) (hymono : Monotone y) (hY0 : ∀ ω ∈ Z, 0 ≤ Y ω)
    (hYN : ∀ ω ∈ Z, Y ω ≤ y N) :
    ∑ ω ∈ Z, Real.exp (t * Y ω) ≤
      (Z.card : ℝ) + ∑ i ∈ Finset.range N,
        (Real.exp (t * y (i + 1)) - Real.exp (t * y i)) * ((Z.filter fun ω => y i < Y ω).card : ℝ) := by
  classical
  -- pointwise: e^{tY} ≤ 1 + Σ_{i<N} (e^{t y(i+1)} − e^{t y i}) [y i < Y]
  have hpt : ∀ ω ∈ Z, Real.exp (t * Y ω) ≤ 1 + ∑ i ∈ Finset.range N,
      (Real.exp (t * y (i + 1)) - Real.exp (t * y i)) * (if y i < Y ω then 1 else 0) := by
    intro ω hω
    -- telescoping up to the first grid point ≥ Y ω
    have key : ∀ M : ℕ, Y ω ≤ y M → Real.exp (t * Y ω) ≤ 1 + ∑ i ∈ Finset.range M,
        (Real.exp (t * y (i + 1)) - Real.exp (t * y i)) * (if y i < Y ω then 1 else 0) := by
      intro M
      induction M with
      | zero =>
        intro h
        rw [hy0] at h
        have : Y ω = 0 := le_antisymm h (hY0 ω hω)
        simp [this]
      | succ M ih =>
        intro h
        rw [Finset.sum_range_succ]
        by_cases hM : Y ω ≤ y M
        · have hinc : 0 ≤ (Real.exp (t * y (M + 1)) - Real.exp (t * y M)) *
              (if y M < Y ω then 1 else 0) := by
            apply mul_nonneg
            · have := hymono (Nat.le_succ M)
              have : t * y M ≤ t * y (M + 1) := mul_le_mul_of_nonneg_left this ht
              linarith [Real.exp_le_exp.2 this]
            · split_ifs <;> norm_num
          linarith [ih hM]
        · push_neg at hM
          rw [if_pos hM, mul_one]
          -- the sum up to M telescopes to e^{t y M} − 1 because every earlier grid point is < Y
          have htel : ∑ i ∈ Finset.range M, (Real.exp (t * y (i + 1)) - Real.exp (t * y i)) *
              (if y i < Y ω then 1 else 0) = Real.exp (t * y M) - Real.exp (t * y 0) := by
            rw [← Finset.sum_range_sub (fun i => Real.exp (t * y i))]
            refine Finset.sum_congr rfl fun i hi => ?_
            have : y i < Y ω := lt_of_le_of_lt (hymono (Finset.mem_range.1 hi).le) hM
            rw [if_pos this, mul_one]
          rw [htel, hy0, mul_zero, Real.exp_zero]
          have : t * Y ω ≤ t * y (M + 1) := mul_le_mul_of_nonneg_left h ht
          linarith [Real.exp_le_exp.2 this]
    exact key N (hYN ω hω)
  calc ∑ ω ∈ Z, Real.exp (t * Y ω)
      ≤ ∑ ω ∈ Z, (1 + ∑ i ∈ Finset.range N,
          (Real.exp (t * y (i + 1)) - Real.exp (t * y i)) * (if y i < Y ω then 1 else 0)) :=
        Finset.sum_le_sum hpt
    _ = (Z.card : ℝ) + ∑ i ∈ Finset.range N,
          (Real.exp (t * y (i + 1)) - Real.exp (t * y i)) * ((Z.filter fun ω => y i < Y ω).card : ℝ) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, Finset.sum_comm]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.mul_sum, Finset.sum_boole]

end SubsetModel

end FringeDuality
