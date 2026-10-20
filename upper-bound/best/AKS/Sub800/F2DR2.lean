import AKS.Sub800.F2DSR
import AKS.Chvatal.F2R2Fail

/-! # R2 failure bounds for `F2PD`: the exact per-`E` reduction

For a fixed rank `E`, the bad set `badE g Φ E κ B` (package, `F2R2Fail`) is bounded by
`Yν · Zν · #Scramble`, where `ν ≤ n` is any positive real and

* `Yν = ∑_{k ≤ κ} C(M,k) ν^k / k!` (the `y`-vector count with `C(n,k) ≤ n^k/k!`),
* `Zν = ∑_{s=1}^{n} (ν^s / s!) (e M s / (ν T_s))^{T_s}`, `T_s = Φ s + E`, `M = B - 1`.

Unlike the package's `badE_card_le`, the Chernoff base keeps `T_s` (no `R^{20 s}` loss), and the
dependence on `n` is removed by `n ≥ ν` (every `(k, s)` term has a negative power of `n`). -/

namespace Chvatal

open Finset

/-- One `(k, s)` term: `n ≥ ν` may be replaced by `ν`. -/
theorem term_le_nu (n k s M T : ℕ) (ν : ℝ) (hν : 0 < ν) (hνn : ν ≤ n) (hT : k + s ≤ T)
    (x : ℝ) (hx : 0 ≤ x) :
    (n.choose k : ℝ) * ((n.choose s : ℝ) * (x / n) ^ T) ≤
      (ν ^ k / k.factorial) * ((ν ^ s / s.factorial) * (x / ν) ^ T) := by
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le hν hνn
  have h1 : (n.choose k : ℝ) ≤ (n : ℝ) ^ k / k.factorial := Nat.choose_le_pow_div k n
  have h2 : (n.choose s : ℝ) ≤ (n : ℝ) ^ s / s.factorial := Nat.choose_le_pow_div s n
  have hk : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hs : (0 : ℝ) < s.factorial := by exact_mod_cast Nat.factorial_pos s
  have key : (n : ℝ) ^ k * ((n : ℝ) ^ s * (x / n) ^ T) ≤ ν ^ k * (ν ^ s * (x / ν) ^ T) := by
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hT
    have e1 : ∀ y : ℝ, 0 < y → y ^ k * (y ^ s * (x / y) ^ (k + s + r)) = x ^ (k + s) * (x / y) ^ r :=
      fun y hy => by
        rw [div_pow, div_pow]
        field_simp
        ring
    rw [e1 _ hn0, e1 _ hν]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_left hx hν hνn) _
  calc (n.choose k : ℝ) * ((n.choose s : ℝ) * (x / n) ^ T)
      ≤ ((n : ℝ) ^ k / k.factorial) * (((n : ℝ) ^ s / s.factorial) * (x / n) ^ T) := by
        gcongr
    _ = ((n : ℝ) ^ k * ((n : ℝ) ^ s * (x / n) ^ T)) / (k.factorial * s.factorial) := by
        field_simp
    _ ≤ (ν ^ k * (ν ^ s * (x / ν) ^ T)) / (k.factorial * s.factorial) := by
        gcongr
    _ = _ := by field_simp

/-- `Yν`. -/
noncomputable def Ynu (κ M : ℕ) (ν : ℝ) : ℝ :=
  ∑ k ∈ range (κ + 1), (M.choose k : ℝ) * (ν ^ k / k.factorial)

/-- `Zν` (terms `s = 1, …, n`). -/
noncomputable def Znu (n Φ E M : ℕ) (ν : ℝ) : ℝ :=
  ∑ s ∈ Icc 1 n, (ν ^ s / s.factorial) *
    (Real.exp 1 * M * s / (ν * ((Φ * s + E : ℕ) : ℝ))) ^ (Φ * s + E)

set_option maxHeartbeats 1000000 in
/-- **Exact per-`E` reduction.** -/
theorem badE_card_le_nu {m n : ℕ} (hn : 0 < n) (g Φ E κ B : ℕ) (ν : ℝ) (hν : 0 < ν)
    (hνn : ν ≤ n) (hΦ : 1 ≤ Φ) (hκE : κ ≤ E) (hB : 2 ≤ B)
    (hR : Real.exp 1 * ((B - 1 : ℕ) : ℝ) ≤ ν * Φ) :
    ((badE (m := m) (n := n) g Φ E κ B).card : ℝ) ≤
      Ynu κ (B - 1) ν * Znu n Φ E (B - 1) ν * Fintype.card (Scramble m n) := by
  classical
  set M := B - 1 with hMdef
  have hM1 : 1 ≤ M := by omega
  have htot : (0 : ℝ) < Fintype.card (Scramble m n) := by exact_mod_cast Fintype.card_pos
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM1
  let Cs : Finset (MonotoneColumnSums m n) := Finset.univ.filter fun c =>
    (Finset.univ.filter fun col => g < (c col).val).card ≤ κ ∧ ∑ col, ((c col).val - g) < B
  let Y : Finset (Fin n → ℕ) := Cs.image (topOf g)
  have hYsub : Y ⊆ ycap n κ M := by
    intro t ht
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp ht
    have hc' := (Finset.mem_filter.mp hc).2
    refine mem_ycap.mpr ⟨by rw [suppC_topOf]; exact hc'.1, ?_⟩
    have : ∑ i, topOf g c i = ∑ col, ((c col).val - g) := rfl
    omega
  let rep : (Fin n → ℕ) → MonotoneColumnSums m n := fun t =>
    if h : ∃ c ∈ Cs, topOf g c = t then Classical.choose h else fun _ => 0
  have hrep : ∀ t ∈ Y, rep t ∈ Cs ∧ topOf g (rep t) = t := fun t ht => by
    have hex : ∃ c ∈ Cs, topOf g c = t := by
      obtain ⟨c, hc, h⟩ := Finset.mem_image.mp ht
      exact ⟨c, hc, h⟩
    simp only [rep, dif_pos hex]
    exact Classical.choose_spec hex
  let U : (Fin n → ℕ) → ℕ → Finset (Scramble m n) := fun t s =>
    tailBadSet (rep t) (topRows m g) s ((Φ * s + E : ℕ) : ℝ)
  have hsub : badE (m := m) (n := n) g Φ E κ B ⊆
      Y.biUnion fun t => (Finset.Icc 1 n).biUnion (U t) := by
    intro σ hσ
    simp only [badE, Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    obtain ⟨c, hc1, hc2, S, hne, hge⟩ := hσ
    have hcCs : c ∈ Cs := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc1, hc2⟩
    have hY : topOf g c ∈ Y := Finset.mem_image.mpr ⟨c, hcCs, rfl⟩
    obtain ⟨-, hrt⟩ := hrep _ hY
    have hones : onesInRows (rep (topOf g c)) σ (topRows m g) S =
        onesInRows c σ (topRows m g) S :=
      onesInRows_topRows_depends_only_on_top _ _
        (fun col => by simpa [topOf] using (congrFun hrt col)) σ S
    refine Finset.mem_biUnion.mpr ⟨topOf g c, hY, Finset.mem_biUnion.mpr ⟨S.card, ?_, ?_⟩⟩
    · rw [Finset.mem_Icc]
      exact ⟨hne.card_pos, by simpa using Finset.card_le_univ S⟩
    · simp only [U, tailBadSet, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨S, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, rfl⟩, ?_⟩
      rw [hones]
      exact_mod_cast hge
  -- per-(t, s) Chernoff bound, base `e M s / (n T_s)`
  set x : ℕ → ℝ := fun s => Real.exp 1 * M * s / ((Φ * s + E : ℕ) : ℝ) with hxdef
  have hUb : ∀ t ∈ Y, ∀ s ∈ Finset.Icc 1 n, ((U t s).card : ℝ) ≤
      ((n.choose s : ℝ) * (x s / n) ^ (Φ * s + E)) * Fintype.card (Scramble m n) := by
    intro t ht s hs
    obtain ⟨hcs, -⟩ := hrep t ht
    have hc' := (Finset.mem_filter.mp hcs).2
    have hs1 := (Finset.mem_Icc.mp hs).1
    have hs0 : (0 : ℝ) < s := by exact_mod_cast hs1
    have hcB : (∑ r ∈ topRows m g, ((monotoneRowOnes (rep t) r).card : ℝ)) ≤ M := by
      have h1 := top_ones_le g (rep t)
      have h2 : ∑ r ∈ topRows m g, (monotoneRowOnes (rep t) r).card ≤ M := by omega
      exact_mod_cast h2
    have hTpos : (0 : ℝ) < ((Φ * s + E : ℕ) : ℝ) := by
      have : 0 < Φ * s + E := by have := Nat.mul_pos (by omega : 0 < Φ) hs1; omega
      exact_mod_cast this
    have hT : (M : ℝ) * s / n ≤ ((Φ * s + E : ℕ) : ℝ) := by
      rw [div_le_iff₀ hn0]
      have hMn : (M : ℝ) ≤ n * Φ := by
        have h1 : Real.exp 1 * M ≤ n * Φ :=
          hR.trans (mul_le_mul_of_nonneg_right hνn (Nat.cast_nonneg _))
        nlinarith [Real.add_one_le_exp (1 : ℝ)]
      push_cast
      have hE : (0 : ℝ) ≤ E := Nat.cast_nonneg _
      nlinarith [mul_le_mul_of_nonneg_right hMn hs0.le, mul_nonneg hE hn0.le]
    have key := tail_union_top_gen hn (rep t) g s (M : ℝ) _ hMr hs1 hcB hT
    rw [div_le_iff₀ htot, Real.rpow_natCast] at key
    have e : Real.exp 1 * (M : ℝ) * s / (n * ((Φ * s + E : ℕ) : ℝ)) = x s / n := by
      simp only [hxdef]; field_simp
    rw [e] at key
    exact key
  have h2 : ((badE (m := m) (n := n) g Φ E κ B).card : ℝ) ≤
      ∑ t ∈ Y, ∑ s ∈ Finset.Icc 1 n, ((U t s).card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans
      ((Finset.card_biUnion_le).trans (Finset.sum_le_sum fun t _ => Finset.card_biUnion_le))
  have hxnn : ∀ s, 0 ≤ x s := fun s => by simp only [hxdef]; positivity
  set W : ℝ := ∑ s ∈ Finset.Icc 1 n, (n.choose s : ℝ) * (x s / n) ^ (Φ * s + E) with hW
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun s _ => by have := hxnn s; positivity
  have hstep : ((badE (m := m) (n := n) g Φ E κ B).card : ℝ) ≤
      ((ycap n κ M).card : ℝ) * W * Fintype.card (Scramble m n) := by
    calc _ ≤ ∑ t ∈ Y, W * Fintype.card (Scramble m n) := by
          refine h2.trans (Finset.sum_le_sum fun t ht => ?_)
          calc ∑ s ∈ Finset.Icc 1 n, ((U t s).card : ℝ)
              ≤ ∑ s ∈ Finset.Icc 1 n, ((n.choose s : ℝ) * (x s / n) ^ (Φ * s + E)) *
                  Fintype.card (Scramble m n) := Finset.sum_le_sum (hUb t ht)
            _ = W * Fintype.card (Scramble m n) := by rw [hW, Finset.sum_mul]
      _ = (Y.card : ℝ) * (W * Fintype.card (Scramble m n)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((ycap n κ M).card : ℝ) * (W * Fintype.card (Scramble m n)) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_card hYsub) (by positivity)
      _ = _ := by ring
  -- the y count and the n → ν substitution
  have hyc : ((ycap n κ M).card : ℝ) ≤ ∑ k ∈ range (κ + 1), (n.choose k : ℝ) * (M.choose k : ℝ) := by
    have := ycap_card_le n κ M
    unfold ycapW at this
    exact_mod_cast this
  have hprod : (∑ k ∈ range (κ + 1), (n.choose k : ℝ) * (M.choose k : ℝ)) * W ≤
      Ynu κ M ν * Znu n Φ E M ν := by
    rw [hW, Ynu, Znu, Finset.sum_mul_sum, Finset.sum_mul_sum]
    refine Finset.sum_le_sum fun k hk => Finset.sum_le_sum fun s hs => ?_
    have hk' : k ≤ κ := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hs1 := (Finset.mem_Icc.mp hs).1
    have hT : k + s ≤ Φ * s + E := by nlinarith
    have h := term_le_nu n k s M (Φ * s + E) ν hν hνn hT (x s) (hxnn s)
    have e : x s / ν = Real.exp 1 * M * s / (ν * ((Φ * s + E : ℕ) : ℝ)) := by
      simp only [hxdef]; field_simp
    rw [e] at h
    have hMk : (0 : ℝ) ≤ M.choose k := Nat.cast_nonneg _
    calc (n.choose k : ℝ) * (M.choose k : ℝ) * ((n.choose s : ℝ) * (x s / n) ^ (Φ * s + E))
        = (M.choose k : ℝ) * ((n.choose k : ℝ) * ((n.choose s : ℝ) * (x s / n) ^ (Φ * s + E))) := by
          ring
      _ ≤ (M.choose k : ℝ) * ((ν ^ k / k.factorial) * ((ν ^ s / s.factorial) *
            (Real.exp 1 * M * s / (ν * ((Φ * s + E : ℕ) : ℝ))) ^ (Φ * s + E))) :=
          mul_le_mul_of_nonneg_left h hMk
      _ = _ := by ring
  calc _ ≤ ((ycap n κ M).card : ℝ) * W * Fintype.card (Scramble m n) := hstep
    _ ≤ (∑ k ∈ range (κ + 1), (n.choose k : ℝ) * (M.choose k : ℝ)) * W *
          Fintype.card (Scramble m n) := by gcongr
    _ ≤ _ := mul_le_mul_of_nonneg_right hprod htot.le

end Chvatal
