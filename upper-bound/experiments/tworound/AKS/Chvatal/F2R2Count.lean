module

public import AKS.Chvatal.Lemma62TopsCount
public import AKS.Chvatal.Lemma62Ratio
public import Mathlib.Data.Nat.Choose.Vandermonde

/-! # Counting vectors of bounded support and mass (`F2ROUND.md` §3, "Y count")

`ycap n κ M` is the set of `y : Fin n → ℕ` with at most `κ` nonzero entries and total at most `M`.
`ycap_card_le : |ycap n κ M| ≤ Σ_{k ≤ κ} C(n,k) C(M,k)` (induction on `n`, as `tops_card_le`),
and for `2κ ≤ n`, `2κ ≤ M`, `1 ≤ κ` this is at most `(κ+1) (e² n M / κ²)^κ`. -/

@[expose] public section

namespace Chvatal

open Finset

/-- Number of nonzero entries. -/
def suppC {n : ℕ} (y : Fin n → ℕ) : ℕ := ∑ i, if y i = 0 then 0 else 1

/-- Vectors with at most `κ` nonzero entries and total at most `M`. -/
def ycap (n κ M : ℕ) : Finset (Fin n → ℕ) :=
  (Fintype.piFinset fun _ => Finset.range (M + 1)).filter fun y => suppC y ≤ κ ∧ ∑ i, y i ≤ M

theorem mem_ycap {n κ M : ℕ} {y : Fin n → ℕ} : y ∈ ycap n κ M ↔ suppC y ≤ κ ∧ ∑ i, y i ≤ M := by
  simp only [ycap, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
  refine ⟨fun h => h.2, fun hs => ⟨fun c => ?_, hs⟩⟩
  have := Finset.single_le_sum (f := y) (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
  omega

/-- Closed-form bound. -/
def ycapW (n κ M : ℕ) : ℕ := ∑ k ∈ Finset.range (κ + 1), Nat.choose n k * Nat.choose M k

theorem ycapW_zero (κ M : ℕ) : 1 ≤ ycapW 0 κ M := by
  unfold ycapW
  rw [Finset.sum_range_succ' _ κ]
  simp

theorem ycapW_succ (n K M : ℕ) :
    ycapW (n + 1) (K + 1) M = ycapW n (K + 1) M +
      ∑ k ∈ Finset.range (K + 1), Nat.choose n k * Nat.choose M (k + 1) := by
  unfold ycapW
  rw [Finset.sum_range_succ' _ (K + 1), Finset.sum_range_succ' (fun k => Nat.choose n k * Nat.choose M k) (K + 1)]
  simp_rw [Nat.choose_succ_succ', add_mul]
  rw [Finset.sum_add_distrib]
  simp
  ring

theorem sum_Icc_choose_zero (K M : ℕ) (k : ℕ) :
    ∑ a ∈ Finset.Icc 1 M, Nat.choose (M - a) k ≤ Nat.choose M (k + 1) := by
  have := sum_Icc_choose_le 0 k M
  simpa using this

/-- Tail/head decomposition of the support count and the total. -/
theorem suppC_cons {n : ℕ} (a : ℕ) (t : Fin n → ℕ) :
    suppC (consN a t) = (if a = 0 then 0 else 1) + suppC t := by
  unfold suppC
  rw [Fin.sum_univ_succ]
  simp [consN]

theorem sum_cons {n : ℕ} (a : ℕ) (t : Fin n → ℕ) : ∑ i, (consN a t) i = a + ∑ i, t i := by
  rw [Fin.sum_univ_succ]
  simp [consN]

theorem ycap_card_le (n : ℕ) : ∀ κ M, (ycap n κ M).card ≤ ycapW n κ M := by
  induction n with
  | zero =>
    intro κ M
    exact (Finset.card_le_one_of_subsingleton _).trans (ycapW_zero κ M)
  | succ n ih =>
    intro κ M
    have hdec : ∀ y : Fin (n + 1) → ℕ, y = consN (y 0) (fun i : Fin n => y i.succ) := by
      intro y
      funext c
      refine Fin.cases ?_ (fun i => ?_) c <;> simp [consN]
    cases κ with
    | zero =>
      have hsub : ycap (n + 1) 0 M ⊆ (ycap n 0 M).image (consN 0) := by
        intro y hy
        rw [mem_ycap] at hy
        have h := hdec y
        rw [h, suppC_cons, sum_cons] at hy
        have h0 : y 0 = 0 := by
          by_contra hne
          simp [hne] at hy
        refine Finset.mem_image.mpr ⟨fun i => y i.succ, mem_ycap.mpr ⟨by
          rw [h0] at hy; simpa using hy.1, by rw [h0] at hy; simpa using hy.2⟩, ?_⟩
        have h2 := hdec y; rw [h0] at h2; exact h2.symm
      refine (Finset.card_le_card hsub).trans (Finset.card_image_le.trans ((ih 0 M).trans ?_))
      unfold ycapW
      simp
    | succ K =>
      have hsub : ycap (n + 1) (K + 1) M ⊆
          (ycap n (K + 1) M).image (consN 0) ∪
          (Finset.Icc 1 M).biUnion fun a => (ycap n K (M - a)).image (consN a) := by
        intro y hy
        rw [mem_ycap] at hy
        have h := hdec y
        rw [h, suppC_cons, sum_cons] at hy
        rw [Finset.mem_union]
        by_cases h0 : y 0 = 0
        · left
          refine Finset.mem_image.mpr ⟨fun i => y i.succ, mem_ycap.mpr ⟨by
            rw [h0] at hy; simpa using hy.1, by rw [h0] at hy; simpa using hy.2⟩, ?_⟩
          have h2 := hdec y; rw [h0] at h2; exact h2.symm
        · right
          refine Finset.mem_biUnion.mpr ⟨y 0, Finset.mem_Icc.mpr ⟨by omega, by omega⟩,
            Finset.mem_image.mpr ⟨fun i => y i.succ, mem_ycap.mpr ⟨by
              simp only [h0, if_false] at hy; omega, by omega⟩, ?_⟩⟩
          exact (hdec y).symm
      calc (ycap (n + 1) (K + 1) M).card
          ≤ (ycap n (K + 1) M).card +
            ∑ a ∈ Finset.Icc 1 M, ((ycap n K (M - a)).image (consN a)).card :=
            (Finset.card_le_card hsub).trans <| (Finset.card_union_le _ _).trans <| by
              gcongr
              · exact Finset.card_image_le
              · exact Finset.card_biUnion_le
        _ ≤ ycapW n (K + 1) M + ∑ a ∈ Finset.Icc 1 M, ycapW n K (M - a) := by
            gcongr with a ha
            · exact ih _ _
            · exact Finset.card_image_le.trans (ih _ _)
        _ ≤ _ := by
            rw [ycapW_succ]
            gcongr
            calc ∑ a ∈ Finset.Icc 1 M, ycapW n K (M - a)
                = ∑ k ∈ Finset.range (K + 1), Nat.choose n k *
                    ∑ a ∈ Finset.Icc 1 M, Nat.choose (M - a) k := by
                  unfold ycapW
                  rw [Finset.sum_comm]
                  simp_rw [Finset.mul_sum]
              _ ≤ _ := Finset.sum_le_sum fun k _ => Nat.mul_le_mul_left _ (sum_Icc_choose_zero K M k)

/-- `C(N,k) ≤ C(N,κ)` for `k ≤ κ`, `2 κ ≤ N`. -/
theorem choose_mono_of_le {N k κ : ℕ} (hk : k ≤ κ) (hκ : 2 * κ ≤ N) :
    Nat.choose N k ≤ Nat.choose N κ := by
  induction κ, hk using Nat.le_induction with
  | base => exact le_rfl
  | succ κ hk ih =>
    exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))

theorem ycapW_le (n κ M : ℕ) (hn : 2 * κ ≤ n) (hM : 2 * κ ≤ M) :
    ycapW n κ M ≤ (κ + 1) * (Nat.choose n κ * Nat.choose M κ) := by
  unfold ycapW
  calc ∑ k ∈ Finset.range (κ + 1), Nat.choose n k * Nat.choose M k
      ≤ ∑ k ∈ Finset.range (κ + 1), Nat.choose n κ * Nat.choose M κ := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hk' : k ≤ κ := by simpa [Nat.lt_succ_iff] using hk
        exact Nat.mul_le_mul (choose_mono_of_le hk' hn) (choose_mono_of_le hk' hM)
    _ = _ := by simp

/-- The real-valued bound `(κ+1) (e² n B / κ²)^κ` for any `B ≥ M`. -/
theorem ycap_card_le_real (n κ M B : ℕ) (hκ : 1 ≤ κ) (hn : 2 * κ ≤ n) (hM : 2 * κ ≤ M)
    (hMB : M ≤ B) :
    ((ycap n κ M).card : ℝ) ≤
      ((κ : ℝ) + 1) * (Real.exp 1 ^ 2 * n * B / (κ : ℝ) ^ 2) ^ κ := by
  have h1 : (ycap n κ M).card ≤ (κ + 1) * (Nat.choose n κ * Nat.choose M κ) :=
    (ycap_card_le n κ M).trans (ycapW_le n κ M hn hM)
  have h2 : ((ycap n κ M).card : ℝ) ≤ ((κ : ℝ) + 1) * ((Nat.choose n κ : ℝ) * Nat.choose M κ) := by
    exact_mod_cast h1
  exact h2.trans (mul_le_mul_of_nonneg_left (choose_mul_choose_le_of_le n hMB hκ) (by positivity))

theorem topClosed_zero (n M : ℕ) : topClosed 0 n M = Nat.choose (M + n) n := by
  have h := Nat.add_choose_eq M n n
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  unfold topClosed
  rw [h]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := by simpa [Nat.lt_succ_iff] using hk
  simp only [Nat.zero_mul, Nat.sub_zero]
  rw [Nat.choose_symm hk', mul_comm]

/-- Support-free count: at most `C(M + n, n)` vectors of total at most `M`. -/
theorem ycap_card_le_choose (n κ M : ℕ) : (ycap n κ M).card ≤ Nat.choose (M + n) n := by
  have hsub : ycap n κ M ⊆ tops 0 n M := by
    intro y hy
    exact Finset.mem_image.mpr ⟨y, mem_sset.mpr (mem_ycap.mp hy).2, by funext c; simp⟩
  exact (Finset.card_le_card hsub).trans ((tops_card_le 0 n M).trans (le_of_eq (topClosed_zero n M)))

end Chvatal
