module

public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Tactic.Linarith

/-! # Chvátal Lemma 6.2 (ii): counting distinct tops

The top (matrix without its bottom `h = f/2` rows) of a monotone matrix with column sums `s` is
`s - h`.  `tops h n j` is the set of tops of all `s` with `Σ s ≤ j`; we prove
`(tops h n j).card ≤ Σ_{k ≤ n} C(n,k) · C(j - h·k, k)` by induction on the number of columns:
column `0` has top `0` (remaining columns, same budget) or top `a - h ≥ 1` (budget `j - a`),
and a hockey-stick estimate closes the recursion. -/

@[expose] public section

namespace Chvatal

open Finset

/-- Column-sum vectors with total at most `j`. -/
def sset (n j : ℕ) : Finset (Fin n → ℕ) :=
  (Fintype.piFinset fun _ => Finset.range (j + 1)).filter fun s => ∑ c, s c ≤ j

/-- Tops (column sums with the bottom `h` rows removed) of vectors with total at most `j`. -/
def tops (h n j : ℕ) : Finset (Fin n → ℕ) :=
  (sset n j).image fun s c => s c - h

/-- Prepend a column value (non-dependent `Fin.cons`). -/
def consN {n : ℕ} (a : ℕ) (t : Fin n → ℕ) : Fin (n + 1) → ℕ := Fin.cons a t

theorem mem_sset {n j : ℕ} {s : Fin n → ℕ} : s ∈ sset n j ↔ ∑ c, s c ≤ j := by
  simp only [sset, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
  refine ⟨fun h => h.2, fun hs => ⟨fun c => ?_, hs⟩⟩
  have := Finset.single_le_sum (f := s) (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
  omega

/-- Closed-form bound of claim (ii). -/
def topClosed (h n j : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), Nat.choose n k * Nat.choose (j - h * k) k

/-- Hockey stick with a shifted argument. -/
theorem sum_range_choose_shift_le (h k : ℕ) :
    ∀ M, ∑ m ∈ Finset.range M, Nat.choose (m - h * k) k ≤ Nat.choose (M - h * k) (k + 1) := by
  intro M
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ]
    by_cases hM : h * k ≤ M
    · rw [show M + 1 - h * k = (M - h * k) + 1 by omega, Nat.choose_succ_succ']
      omega
    · have hk : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hM)
      have h0 : M - h * k = 0 := by omega
      rw [h0, Nat.choose_zero_succ] at ih
      rw [h0, Nat.choose_eq_zero_of_lt hk]
      omega

theorem sum_Icc_choose_le (h k j : ℕ) :
    ∑ a ∈ Finset.Icc (h + 1) j, Nat.choose (j - a - h * k) k ≤
      Nat.choose (j - h * (k + 1)) (k + 1) := by
  have : ∑ a ∈ Finset.Icc (h + 1) j, Nat.choose (j - a - h * k) k =
      ∑ m ∈ Finset.range (j - h), Nat.choose (m - h * k) k := by
    refine Finset.sum_nbij' (fun a => j - a) (fun m => j - m) ?_ ?_ ?_ ?_ (fun _ _ => rfl) <;>
      intro x hx <;> simp only [Finset.mem_Icc, Finset.mem_range] at hx ⊢ <;> omega
  rw [this]
  refine (sum_range_choose_shift_le h k (j - h)).trans ?_
  rw [show j - h - h * k = j - h * (k + 1) by rw [Nat.mul_add, Nat.mul_one]; omega]

theorem topClosed_succ (h n j : ℕ) :
    topClosed h (n + 1) j = topClosed h n j +
      ∑ k ∈ Finset.range (n + 1), Nat.choose n k * Nat.choose (j - h * (k + 1)) (k + 1) := by
  have A : ∑ k ∈ Finset.range (n + 1), Nat.choose n (k + 1) * Nat.choose (j - h * (k + 1)) (k + 1)
      = ∑ k ∈ Finset.range n, Nat.choose n (k + 1) * Nat.choose (j - h * (k + 1)) (k + 1) := by
    rw [Finset.sum_range_succ]; simp [Nat.choose_succ_self]
  have B : topClosed h n j =
      ∑ k ∈ Finset.range n, Nat.choose n (k + 1) * Nat.choose (j - h * (k + 1)) (k + 1) + 1 := by
    unfold topClosed
    rw [Finset.sum_range_succ' _ n]; simp
  unfold topClosed
  rw [Finset.sum_range_succ' _ (n + 1)]
  simp_rw [Nat.choose_succ_succ', add_mul]
  rw [Finset.sum_add_distrib, A]
  unfold topClosed at B
  rw [B]
  simp
  ring

/-- **Claim (ii)** (Chvátal Lemma 6.2): the number of distinct tops of monotone matrices
    with at most `j` ones is at most `Σ_k C(n,k) · C(j - h·k, k)`. -/
theorem tops_card_le (h n : ℕ) : ∀ j, (tops h n j).card ≤ topClosed h n j := by
  induction n with
  | zero => intro j; simpa [topClosed] using Finset.card_le_one_of_subsingleton _
  | succ n ih =>
    intro j
    have hsub : tops h (n + 1) j ⊆
        (tops h n j).image (consN 0) ∪
        (Finset.Icc (h + 1) j).biUnion fun a => (tops h n (j - a)).image (consN (a - h)) := by
      intro t ht
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
      rw [mem_sset, Fin.sum_univ_succ] at hs
      have key : ∀ b, ∑ c : Fin n, s c.succ ≤ b →
          (fun c : Fin n => s c.succ - h) ∈ tops h n b := fun b hb =>
        Finset.mem_image.mpr ⟨_, mem_sset.mpr hb, rfl⟩
      have hcons : (fun c => s c - h) = consN (s 0 - h) (fun c : Fin n => s c.succ - h) := by
        funext c
        refine Fin.cases ?_ (fun i => ?_) c <;> simp [consN]
      rw [Finset.mem_union]
      by_cases ha : s 0 ≤ h
      · exact Or.inl (Finset.mem_image.mpr ⟨_, key j (by omega), by
          rw [hcons, Nat.sub_eq_zero_of_le ha]⟩)
      · exact Or.inr (Finset.mem_biUnion.mpr ⟨s 0, Finset.mem_Icc.mpr ⟨by omega, by omega⟩,
          Finset.mem_image.mpr ⟨_, key _ (by omega), hcons.symm⟩⟩)
    calc (tops h (n + 1) j).card
        ≤ (tops h n j).card +
          ∑ a ∈ Finset.Icc (h + 1) j, ((tops h n (j - a)).image (consN (a - h))).card :=
          (Finset.card_le_card hsub).trans <| (Finset.card_union_le _ _).trans <| by
            gcongr
            · exact Finset.card_image_le
            · exact Finset.card_biUnion_le
      _ ≤ topClosed h n j + ∑ a ∈ Finset.Icc (h + 1) j, topClosed h n (j - a) := by
          gcongr with a ha
          · exact ih j
          · exact Finset.card_image_le.trans (ih (j - a))
      _ ≤ _ := by
          rw [topClosed_succ]
          gcongr
          calc ∑ a ∈ Finset.Icc (h + 1) j, topClosed h n (j - a)
              = ∑ k ∈ Finset.range (n + 1), Nat.choose n k *
                  ∑ a ∈ Finset.Icc (h + 1) j, Nat.choose (j - a - h * k) k := by
                unfold topClosed
                rw [Finset.sum_comm]
                simp_rw [Finset.mul_sum]
            _ ≤ _ := Finset.sum_le_sum fun k _ => Nat.mul_le_mul_left _ (sum_Icc_choose_le h k j)

end Chvatal
